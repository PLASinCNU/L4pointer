#include "util.h"
#include <llvm/Analysis/ConstantFolding.h>
#include <map>
#include <set>
static std::map<std::string, int> MallocFuncs = {
    {"malloc", 0},
    {"valloc", 0},
    {"_Znwj", 0}, /* new(unsigned int) */
    {"_ZnwjRKSt9nothrow_t", 0},
    {"_Znwm", 0}, /* new(unsigned long) */
    {"_ZnwmRKSt9nothrow_t", 0},
    {"_Znaj", 0}, /* new[](unsigned int) */
    {"_ZnajRKSt9nothrow_t", 0},
    {"_Znam", 0}, /* new[](unsigned long) */
    {"_ZnamRKSt9nothrow_t", 0},

    /* C++ exception support */
    /* XXX do we want to include this? we don't propagate this later. */
    /* XXX this buffer extends below the returned pointer. */
    {"__cxa_allocate_exception", 0},
};

static std::map<std::string, int> MallocWrappers = {
    /* custom pool allocators
     * This does not include direct malloc() wrappers such as xmalloc, only
     * functions that allocate a large memory pool once and then perform small
     * allocations in that pool. */
    {"ggc_alloc", 0},        // gcc
    {"alloc_anon", 1},       // gcc
    {"ngx_alloc", 0},        // nginx
    {"ngx_palloc", 1},       // nginx
    {"ngx_palloc_small", 1}, // nginx ngx_palloc inline
    {"ngx_palloc_large", 1}, // nginx ngx_palloc inline
};

static std::set<std::string> CallocFuncs = {
    "calloc",
};

static std::set<std::string> CallocWrappers = {};

static std::set<std::string> ReallocFuncs = {
    "realloc",
    "reallocf",
};

static std::set<std::string> ReallocWrappers = {};

static std::set<std::string> FreeFuncs = {
    "free",
};

static std::set<std::string> FreeWrappers = {};

static inline bool isInList(std::map<std::string, int> Map, Function *F) {
  return Map.find(F->getName().str()) != Map.end();
}

static inline bool isInList(std::set<std::string> sset, Function *F) {
  return sset.count(F->getName().str()) > 0;
}

bool isMalloc(Function *F) { return isInList(MallocFuncs, F); }

bool isCalloc(Function *F) { return isInList(CallocFuncs, F); }

bool isRealloc(Function *F) { return isInList(ReallocFuncs, F); }

bool isFree(Function *F) { return isInList(FreeFuncs, F); }

bool isMallocWrapper(Function *F) { return isInList(MallocWrappers, F); }

bool isCallocWrapper(Function *F) { return isInList(CallocWrappers, F); }

bool isReallocWrapper(Function *F) { return isInList(ReallocWrappers, F); }

bool isFreeWrapper(Function *F) { return isInList(FreeWrappers, F); }

bool isAllocationFunc(Function *F) {
  return isMalloc(F) || isCalloc(F) || isRealloc(F) || isMallocWrapper(F) ||
         isCallocWrapper(F) || isReallocWrapper(F);
}

bool isAllocation(Instruction *I) {
  if (!I)
    return false;
  if (isa<AllocaInst>(I))
    return false;

  if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
    llvm::CallSite CS(I);
    if (isHeapAllocation(CS)) {
      return true;
    }
  }

  return false;
}

bool isHeapAlloc(Instruction& I){
  if(isa<CallInst>(I) || isa<InvokeInst>(I)){
    llvm::CallSite cs(&I);
    return isHeapAllocation(cs);
  }
  return false;
}

bool isStackValue(Instruction* I){
  if(isa<AllocaInst>(I)){
    AllocaInst* alloca = dyn_cast<AllocaInst>(I);
    Type* allocType = alloca->getAllocatedType();
    errs() << "Instruction : ";
    I->print(errs()); 

    errs() << "   Alloc Type: ";
    allocType->print(errs());
    errs() <<"\n";
    if(allocType->isPointerTy()) {
      errs() << "It's Pointer. \n";
      return false;
    }
    else return true;
  }
  return false;
}

bool isHeapAllocation(CallSite &CS) {
  Function *F = CS.getCalledFunction();
  if (!F || !F->hasName() || F->isIntrinsic())
    return false;

  if (isMalloc(F)) {
  } else if (isCalloc(F)) {
  } else if (isRealloc(F)) {
  } else if (isMallocWrapper(F)) {
  } else if (isCallocWrapper(F)) {
  } else if (isReallocWrapper(F)) {
  } else {
    return false;
  }
  return true;
}
static inline bool scanList(std::set<std::string> list, Function *F) {
  return list.count(F->getName().str()) > 0;
}

unsigned long long 
getAddressSpaceMask(bool overflowbit) {
  unsigned long long Mask = 0xFFFFFFFFFFFF;
  if (overflowbit) {
    Mask |= (1ULL << 63);
    Mask |= (1ULL << 55);
  }
  return Mask;
}

Instruction *getInsertPointAfter(Instruction *I) {
  if (InvokeInst *Invoke = dyn_cast<InvokeInst>(I)) {
    BasicBlock *Dst = Invoke->getNormalDest();
    BasicBlock *NewBlock = BasicBlock::Create(
        I->getContext(), "invoke_insert_point", Dst->getParent(), Dst);
    BranchInst *Br = BranchInst::Create(Dst, NewBlock);
    Invoke->setNormalDest(NewBlock);

    /* Patch references in PN nodes in original successor */
    BasicBlock::iterator It(Dst->begin());
    while (PHINode *PN = dyn_cast<PHINode>(It)) {
      int i;
      while ((i = PN->getBasicBlockIndex(Invoke->getParent())) >= 0)
        PN->setIncomingBlock(i, NewBlock);
      It++;
    }

    return Br;
  }

  if (isa<PHINode>(I))
    return &*I->getParent()->getFirstInsertionPt();

  assert(!isa<TerminatorInst>(I));
  return &*std::next(BasicBlock::iterator(I));
}

Value *instrumentWithByteSize(IRBuilder<> &B, Instruction *I,
                              const DataLayout &DL, AllocationType CallType) {
  int SizeArg = getSizeArg(I);
  switch (CallType) {
  case Malloc:
  case Realloc: {
    CallSite CS(I);
    return CS.getArgOperand(SizeArg);
  }
  case Calloc: {
    CallSite CS(I);
    Value *NumElements = CS.getArgOperand(0);
    Value *ElementSize = CS.getArgOperand(1);
    return B.CreateMul(NumElements, ElementSize);
  }
  case Alloca: {
    AllocaInst *AI = cast<AllocaInst>(I);
    Value *Size = B.getInt64(DL.getTypeAllocSize(AI->getAllocatedType()));

    if (AI->isArrayAllocation())
      Size = B.CreateMul(Size, AI->getArraySize());

    return Size;
  }
  }
  return nullptr; /* never reached */
}

Value *instrumentWithByteSize(IRBuilder<> &B, Instruction *I,
                              const DataLayout &DL) {
  AllocationType CallType = getCallType(I);
  int SizeArg = getSizeArg(I);
  
  switch (CallType) {
  case Malloc:
  case Realloc: {
    CallSite CS(I);
    return CS.getArgOperand(SizeArg);
  }
  case Calloc: {
    CallSite CS(I);
    Value *NumElements = CS.getArgOperand(0);
    Value *ElementSize = CS.getArgOperand(1);
    return B.CreateMul(NumElements, ElementSize);
  }
  case Alloca: {
    AllocaInst *AI = cast<AllocaInst>(I);
    Value *Size = B.getInt64(DL.getTypeAllocSize(AI->getAllocatedType()));

    if (AI->isArrayAllocation())
      Size = B.CreateMul(Size, AI->getArraySize());

    return Size;
  }
  case AllocaNone: return nullptr;
  default: return nullptr;
  }
  return nullptr; /* never reached */
}

const SCEV* getSizeSCEV(Instruction *I, ScalarEvolution &SE) {
  AllocationType CallType = getCallType(I);
  if (CallType == AllocationType::AllocaNone)
    return nullptr;

  int SizeArg = getSizeArg(I);


  switch (CallType) {
  case Malloc:
  case Realloc:{
    if(SizeArg == -1) {
    errs() << "error, size is -1\n";
    return nullptr;
  }
    CallSite CS = CallSite(I);
    Value* tempV = CS.getArgOperand(SizeArg);
    return SE.getSCEV(tempV);
  }
  case Calloc: {
    CallSite CS(I);
    Value *NumElements = CS.getArgOperand(0);
    Value *ElementSize = CS.getArgOperand(1);
    return SE.getMulExpr(SE.getSCEV(NumElements), SE.getSCEV(ElementSize),
                         SCEV::FlagNUW);
  }
  case Alloca: {
    AllocaInst *AI = cast<AllocaInst>(I);
    IntegerType *i64Ty = Type::getInt64Ty(AI->getContext());
    const SCEV *Size = SE.getSizeOfExpr(i64Ty, AI->getAllocatedType());

    if (AI->isArrayAllocation())
      Size = SE.getMulExpr(Size, SE.getSCEV(AI->getArraySize()), SCEV::FlagNUW);

    return Size;
  }
  }
  return nullptr;
}

AllocationType getCallType(Instruction *I) {

  // if return None, the error occurs.
  AllocationType CallType;

  if (isa<AllocaInst>(I)) 
      CallType = AllocationType::Alloca;
     
  if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
    llvm::CallSite CS(I);
    Function *F = CS.getCalledFunction();

    if (!F || !F->hasName() || F->isIntrinsic())
      return AllocationType::AllocaNone;

    // XXX removed the ParentFunc check here in favor of source patches, still
    // need a source patch for ngx_set_environment
    if (isMalloc(F)) {
      CallType = AllocationType::Malloc;
    } else if (isCalloc(F)) {
      CallType = AllocationType::Calloc;
    } else if (isRealloc(F)) {
      CallType = AllocationType::Realloc;
    } else if (isMallocWrapper(F)) {
      CallType = AllocationType::Malloc;
    } else if (isCallocWrapper(F)) {
      CallType = AllocationType::Calloc;
    } else if (isReallocWrapper(F)) {
      CallType = AllocationType::Realloc;
    } else {
      return AllocationType::AllocaNone;
    }
  }
  return CallType;
}

int getSizeArg(Instruction *I) {
  if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
    llvm::CallSite CS(I);
    Function *F = CS.getCalledFunction();
    return getSizeArg(F);
  }
  return -1;
}

int getSizeArg(Function *F) {
  const std::string &name = F->getName().str();
  
  auto it = MallocFuncs.find(name);
  if (it != MallocFuncs.end())
    return it->second;

  it = MallocWrappers.find(name);
  if (it != MallocWrappers.end())
    return it->second;
  return -1;
}

const SCEV *getGlobalSizeSCEV(GlobalVariable *GV, ScalarEvolution &SE) {
  return SE.getSizeOfExpr(Type::getInt64Ty(GV->getContext()),
                          GV->getType()->getPointerElementType());
}


static void collectPHIOriginsRecursive(PHINode *PN,
                                       std::vector<Value *> &Origins,
                                       std::set<Value *> &Visited) {
  for (unsigned I = 0, E = PN->getNumIncomingValues(); I < E; ++I) {
    Value *V = PN->getIncomingValue(I);

    if (Visited.count(V) != 0)
      continue;
    Visited.insert(V);

    ifcast(PHINode, IPN, V) collectPHIOriginsRecursive(IPN, Origins, Visited);
    else Origins.push_back(V);
  }
}

void collectPHIOrigins(PHINode *PN, std::vector<Value *> &Origins) {
  std::set<Value *> Visited = {PN};
  collectPHIOriginsRecursive(PN, Origins, Visited);
}


Value* createTag(IRBuilder<>& irb, Value* size, std::string prefix){
  Value* tagVal;
  Value* UnderOffset = irb.CreateShl(size, 56, prefix+".under");
  Value* OverOffset = irb.CreateShl(size, 48, prefix+".over");
  tagVal = irb.CreateOr(UnderOffset, OverOffset, prefix + ".tag");
  valuePrint(size, "size");
  Value* sizeAnd = irb.CreateAnd(size, 0x0000ffffffffffff, "size");
  valuePrint(sizeAnd, "sizeAnd");
  Value* resultOffset = irb.CreateOr(tagVal, sizeAnd, prefix+".offset");

  errs() <<"tagVal: ";
  tagVal->print(errs());
  errs() <<"\n";
  return resultOffset;
}

Value* createOverMask(IRBuilder<>& irb, Value* size){
  ConstantInt* one = ConstantInt::get(Type::getInt64Ty(irb.getContext()), (1ULL << 7)-1);
  Value* maskNoShift = irb.CreateSub(one, size, "sub");
  ConstantInt* clearOver = ConstantInt::get(Type::getInt64Ty(irb.getContext()), 0x00FF);
  Value* temp = irb.CreateAnd(maskNoShift, clearOver);
  Value* maskShift = irb.CreateShl(temp, 48, "over.shift");
  return maskShift;
}

Value* getClearTagPointer(IRBuilder<>& irb, Value* MAllocP){
  unsigned long long clearAddress = (1ULL<<48)-1;
  clearAddress = (0x8080ULL << 48) | clearAddress;
  ConstantInt* clearBit = ConstantInt::get(Type::getInt64Ty(irb.getContext()), clearAddress);
  Value* IntPointer = irb.CreatePtrToInt(MAllocP, irb.getInt64Ty(), MAllocP->getName()+".to.int");
  Value* ClearInt = irb.CreateAnd(IntPointer, clearBit, ".and");
  Value* ClearPointer = irb.CreateIntToPtr(ClearInt, MAllocP->getType(), MAllocP->getName()+".clear");
  return ClearPointer;
}

void valuePrint(Value* value, std::string prefix){
  if(!value) return;
  errs() <<prefix<<": ";
  value->print(errs());
  errs() <<"\n";
}

void typePrint(Type* type, std::string prefix){
  if(!type) return;
  errs() <<prefix<<": ";
  type->print(errs());
  errs() <<"\n";
}