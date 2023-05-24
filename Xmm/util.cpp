#include "util.h"

#include <llvm/Analysis/ConstantFolding.h>
#include <llvm/IR/InstIterator.h>

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

static std::set<std::string> ExternStruct = {"struct._IO_FILE",
                                             "struct._IO_marker",
                                             "union.pthread_mutex_t",
                                             "struct.__pthread_mutex_s",
                                             "struct.__pthread_internal_list",
                                             "union.pthread_cond_t",
                                             "struct.__pthread_cond_s",
                                             "union.anon",
                                             "union.pthread_mutexattr_t",
                                             "struct.anon",
                                             "thread_args",
                                             "struct.stat",
                                             "struct.stats_t"};

bool isExternalStruct(std::string name) { return ExternStruct.count(name) > 0; }
bool isUsedFunctionPointer(Function *F)
{
  for (Value *val : F->users())
  {
    if (CallInst *CI = dyn_cast<CallInst>(val))
    {
      if (CI->getCalledFunction() == F)
        continue;
      else // Operand 의 인자로 쓰였다는 뜻, 함수포인터로 인자가 넘어간 경우
        return true;
    }
    else
      return true;
  }
  return false;
}

bool isArgsFunction(Function* F){
  if(F->getName()=="dealwithargs"){
    return true;
  }
  if(F->getName() == "main"){
    return true;
  }
  return false;
}

bool isUserAllocation(Function *F)
{
  if (F->getName() == "localmalloc")
  {
    return true;
  }

  if (F->getName() == "default_bzalloc"){
    return true;
  }
  return false;
}
bool isStringFunction(Function* F){
  
  for(Instruction & I : instructions(*F)){
    if(ReturnInst* RI = dyn_cast<ReturnInst>(&I)){
      Value* val = RI->getReturnValue();
      if(val){
        if(Constant* cons = dyn_cast<Constant>(val)){
          if(cons->isNullValue()) return false;
          if(cons->getType()->isIntegerTy()) return false;
          if(cons->getType()->isPointerTy()) return true;
        }
        
      }
      else return false;
    }
  }
  return false;
}

bool isAllUseSelf(Function *F)
{
  if (F->doesNotRecurse())
    return false;

  for (Value *v : F->users())
  {
    if (CallInst *CI = dyn_cast<CallInst>(v))
    {
      Function *parent = CI->getParent()->getParent();
      if (parent != F)
        return false;
    }
  }
  return true;
}

void deleteFunction(Function *F)
{
  // errs() << F->getName() << "\n";

  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E;)
  {
    inst_iterator vI = I;
    I++;

    vI->replaceAllUsesWith(UndefValue::get(vI->getType()));
    vI->eraseFromParent();
  }
  for (Value *use : F->users())
  {
    if (ConstantExpr *cExpr = dyn_cast<ConstantExpr>(use))
    {
      cExpr->replaceAllUsesWith(UndefValue::get(cExpr->getType()));
      cExpr->destroyConstant();
    }
  }
}
void traceUses(Function *F)
{
  errs() << "Function User : " << F->getName() << "\n";
  for (Value *v : F->users())
  {
    valuePrint(v, "User: ");
    if (Instruction *I = dyn_cast<Instruction>(v))
    {
      errs() << "User's parent : " << I->getParent()->getParent()->getName()
             << "\n";
    }
  }
}
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

static inline bool isInList(std::map<std::string, int> Map, Function *F)
{
  return Map.find(F->getName().str()) != Map.end();
}

static inline bool isInList(std::set<std::string> sset, Function *F)
{
  return sset.count(F->getName().str()) > 0;
}
bool isPassFunction(Function* F){
  if(F->getName() =="King") return true;
  if(F->getName() =="Queen") return true;
  if(F->getName() =="Rook") return true;
  if(F->getName() =="Bishop") return true;
  if(F->getName() =="Knight") return true;
  if(F->getName() =="Pawn") return true;
  if(F->getName() == "ErrorIt") return true;
  return false;
}

bool isMalloc(Function *F) { return isInList(MallocFuncs, F); }

bool isCalloc(Function *F) { return isInList(CallocFuncs, F); }

bool isRealloc(Function *F) { return isInList(ReallocFuncs, F); }

bool isFree(Function *F) { return isInList(FreeFuncs, F); }

bool isMallocWrapper(Function *F) { return isInList(MallocWrappers, F); }

bool isCallocWrapper(Function *F) { return isInList(CallocWrappers, F); }

bool isReallocWrapper(Function *F) { return isInList(ReallocWrappers, F); }

bool isFreeWrapper(Function *F) { return isInList(FreeWrappers, F); }

bool isAllocationFunc(Function *F)
{
  return isMalloc(F) || isCalloc(F) || isRealloc(F) || isMallocWrapper(F) ||
         isCallocWrapper(F) || isReallocWrapper(F);
}

bool isAllocation(Instruction *I)
{
  if (!I)
    return false;
  if (isa<AllocaInst>(I))
    return false;

  if (isa<CallInst>(I) || isa<InvokeInst>(I))
  {

    CallInst *CS= dyn_cast<CallInst>(I);
    if (isHeapAllocation(*CS))
    {
      return true;
    }
  }

  return false;
}

bool isHeapAlloc(Instruction &I)
{
  if (isa<CallInst>(I) || isa<InvokeInst>(I))
  {
    
    CallInst *cs= dyn_cast<CallInst>(&I);
    return isHeapAllocation(*cs);
  }
  return false;
}

bool isStackValue(Instruction *I)
{
  if (isa<AllocaInst>(I))
  {
    AllocaInst *alloca = dyn_cast<AllocaInst>(I);
    Type *allocType = alloca->getAllocatedType();

    if (allocType->isPointerTy())
    {
      return false;
    }
    else
      return true;
  }
  return false;
}

bool isHeapAllocation(CallInst &CS)
{
  Function *F = CS.getCalledFunction();
  if (!F || !F->hasName() || F->isIntrinsic())
    return false;

  if (isMalloc(F))
  {
  }
  else if (isCalloc(F))
  {
  }
  else if (isRealloc(F))
  {
  }
  else if (isMallocWrapper(F))
  {
  }
  else if (isCallocWrapper(F))
  {
  }
  else if (isReallocWrapper(F))
  {
  }
  else
  {
    return false;
  }
  return true;
}
static inline bool scanList(std::set<std::string> list, Function *F)
{
  return list.count(F->getName().str()) > 0;
}

unsigned long long getAddressSpaceMask(bool overflowbit)
{
  unsigned long long Mask = 0xFFFFFFFFFFFF;
  if (overflowbit)
  {
    Mask |= (1ULL << 63);
    Mask |= (1ULL << 55);
  }
  return Mask;
}

Instruction *getInsertPointBefore(Instruction *I)
{
  if (BasicBlock::iterator(I) == I->getParent()->begin())
    return nullptr;
  return &*std::prev(BasicBlock::iterator(I));
}
Instruction *getInsertPointAfter(Instruction *I)
{
  if (InvokeInst *Invoke = dyn_cast<InvokeInst>(I))
  {
    BasicBlock *Dst = Invoke->getNormalDest();
    BasicBlock *NewBlock = BasicBlock::Create(
        I->getContext(), "invoke_insert_point", Dst->getParent(), Dst);
    BranchInst *Br = BranchInst::Create(Dst, NewBlock);
    Invoke->setNormalDest(NewBlock);

    /* Patch references in PN nodes in original successor */
    BasicBlock::iterator It(Dst->begin());
    while (PHINode *PN = dyn_cast<PHINode>(It))
    {
      int i;
      while ((i = PN->getBasicBlockIndex(Invoke->getParent())) >= 0)
        PN->setIncomingBlock(i, NewBlock);
      It++;
    }

    return Br;
  }

  if (isa<PHINode>(I))
    return &*I->getParent()->getFirstInsertionPt();

  return &*std::next(BasicBlock::iterator(I));
}

Value *instrumentWithByteSize(IRBuilder<> &B, Instruction *I,
                              const DataLayout &DL, AllocationType CallType)
{
  int SizeArg = getSizeArg(I);
  switch (CallType)
  {
  case Malloc:
  case Realloc:
  {
    CallInst *CS= dyn_cast<CallInst>(I);
    return CS->getArgOperand(SizeArg);
  }
  case Calloc:
  {
    CallInst *CS= dyn_cast<CallInst>(I);
    Value *NumElements = CS->getArgOperand(0);
    Value *ElementSize = CS->getArgOperand(1);
    return B.CreateMul(NumElements, ElementSize);
  }
  case Alloca:
  {
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
                              const DataLayout &DL)
{
  AllocationType CallType = getCallType(I);
  int SizeArg = getSizeArg(I);

  switch (CallType)
  {
  case Malloc:
  case Realloc:
  {
CallInst *CS= dyn_cast<CallInst>(I);
    return CS->getArgOperand(SizeArg);
  }
  case Calloc:
  {
    CallInst *CS= dyn_cast<CallInst>(I);
    Value *NumElements = CS->getArgOperand(0);
    Value *ElementSize = CS->getArgOperand(1);
    return B.CreateMul(NumElements, ElementSize);
  }
  case Alloca:
  {
    AllocaInst *AI = cast<AllocaInst>(I);
    Value *Size = B.getInt64(DL.getTypeAllocSize(AI->getAllocatedType()));

    if (AI->isArrayAllocation())
      Size = B.CreateMul(Size, AI->getArraySize());

    return Size;
  }
  case AllocaNone:
    return nullptr;
  default:
    return nullptr;
  }
  return nullptr; /* never reached */
}

const SCEV *getSizeSCEV(Instruction *I, ScalarEvolution &SE)
{
  AllocationType CallType = getCallType(I);
  if (CallType == AllocationType::AllocaNone)
    return nullptr;

  int SizeArg = getSizeArg(I);

  switch (CallType)
  {
  case Malloc:
  case Realloc:
  {
    if (SizeArg == -1)
    {
      errs() << "error, size is -1\n";
      return nullptr;
    }
    CallInst *CS= dyn_cast<CallInst>(I);
    Value *tempV = CS->getArgOperand(SizeArg);
    return SE.getSCEV(tempV);
  }
  case Calloc:
  {
    CallInst *CS= dyn_cast<CallInst>(I);
    Value *NumElements = CS->getArgOperand(0);
    Value *ElementSize = CS->getArgOperand(1);
    return SE.getMulExpr(SE.getSCEV(NumElements), SE.getSCEV(ElementSize),
                         SCEV::FlagNUW);
  }
  case Alloca:
  {
    AllocaInst *AI = cast<AllocaInst>(I);
    IntegerType *i64Ty = Type::getInt64Ty(AI->getContext());
    const SCEV *Size = SE.getSizeOfExpr(i64Ty, AI->getAllocatedType());

    if (AI->isArrayAllocation())
      Size =
          SE.getMulExpr(Size, SE.getSCEV(AI->getArraySize()), SCEV::FlagNUW);

    return Size;
  }
  }
  return nullptr;
}

AllocationType getCallType(Instruction *I)
{
  // if return None, the error occurs.
  AllocationType CallType;

  if (isa<AllocaInst>(I))
    CallType = AllocationType::Alloca;

  if (isa<CallInst>(I) || isa<InvokeInst>(I))
  {
    CallInst *CS= dyn_cast<CallInst>(I);
    Function *F = CS->getCalledFunction();

    if (!F || !F->hasName() || F->isIntrinsic())
      return AllocationType::AllocaNone;

    // XXX removed the ParentFunc check here in favor of source patches, still
    // need a source patch for ngx_set_environment
    if (isMalloc(F))
    {
      CallType = AllocationType::Malloc;
    }
    else if (isCalloc(F))
    {
      CallType = AllocationType::Calloc;
    }
    else if (isRealloc(F))
    {
      CallType = AllocationType::Realloc;
    }
    else if (isMallocWrapper(F))
    {
      CallType = AllocationType::Malloc;
    }
    else if (isCallocWrapper(F))
    {
      CallType = AllocationType::Calloc;
    }
    else if (isReallocWrapper(F))
    {
      CallType = AllocationType::Realloc;
    }
    else
    {
      return AllocationType::AllocaNone;
    }
  }
  return CallType;
}

int getSizeArg(Instruction *I)
{
  if (isa<CallInst>(I) || isa<InvokeInst>(I))
  {
    CallInst *CS= dyn_cast<CallInst>(I);
    Function *F = CS->getCalledFunction();
    return getSizeArg(F);
  }
  return -1;
}

int getSizeArg(Function *F)
{
  const std::string &name = F->getName().str();

  auto it = MallocFuncs.find(name);
  if (it != MallocFuncs.end())
    return it->second;

  it = MallocWrappers.find(name);
  if (it != MallocWrappers.end())
    return it->second;
  return -1;
}

const SCEV *getGlobalSizeSCEV(GlobalVariable *GV, ScalarEvolution &SE)
{
  return SE.getSizeOfExpr(Type::getInt64Ty(GV->getContext()),
                          GV->getType()->getPointerElementType());
}

bool isMalloc(Instruction *I)
{
  if (!isAllocation(I))
    return false;
  if (CallInst *CI = dyn_cast<CallInst>(I))
  {
    Function *func = CI->getCalledFunction();
    if (func->getName() == "malloc")
      return true;
  }
  return false;
}

bool isRealloc(Instruction *I)
{
  if (!isAllocation(I))
    return false;
  if (CallInst *CI = dyn_cast<CallInst>(I))
  {
    Function *func = CI->getCalledFunction();
    if (func->getName() == "realloc")
      return true;
  }
  return false;
}

static void collectPHIOriginsRecursive(PHINode *PN,
                                       std::vector<Value *> &Origins,
                                       std::set<Value *> &Visited)
{
  for (unsigned I = 0, E = PN->getNumIncomingValues(); I < E; ++I)
  {
    Value *V = PN->getIncomingValue(I);

    if (Visited.count(V) != 0)
      continue;
    Visited.insert(V);

    ifcast(PHINode, IPN, V) collectPHIOriginsRecursive(IPN, Origins, Visited);
    else Origins.push_back(V);
  }
}

void collectPHIOrigins(PHINode *PN, std::vector<Value *> &Origins)
{
  std::set<Value *> Visited = {PN};
  collectPHIOriginsRecursive(PN, Origins, Visited);
}

Value *createMask(IRBuilder<> &irb, Value *size, LLVMContext &ctx)
{
  // 초기화 전용
  // 이거 고쳐야됨
  //
  // 이거 반대로 하고 있음
  // 반대로 하는거만 고치면됨
  // 그리고 생각해보니 처음에 초기화할 때는
  // underflow를 보기위한 태그는 0으로 놔도 됨
  Value *op = size;
  ConstantInt *one = ConstantInt::get(Type::getInt64Ty(ctx), (1ULL << 31));
  if (size->getType()->getIntegerBitWidth() != 64)
  {
    op = irb.CreateZExt(size, Type::getInt64Ty(ctx));
  }
  valuePrint(op, "op");
  Value *maskNoShift = irb.CreateSub(one, op, "sub");
  // valuePrint(maskNoShift, "mask");
  return maskNoShift;
}
Constant *createConstantMask(Value *size, LLVMContext &ctx)
{
  Constant *consSize = dyn_cast<Constant>(size);
  ConstantInt *one = ConstantInt::get(Type::getInt64Ty(ctx), (1ULL << 31));
  Constant *maskNoShift = ConstantExpr::getSub(one, consSize, "sub");
  return maskNoShift;
}

Value *getClearTagPointer(IRBuilder<> &irb, Value *MAllocP,
                          std::string prefix)
{
  std::string Prefix = std::string(MAllocP->getName()) + "." + prefix;
  unsigned long long clearAddress = (1ULL << 48) - 1;
  clearAddress = (0x8080ULL << 48) | clearAddress;
  ConstantInt *clearBit =
      ConstantInt::get(Type::getInt64Ty(irb.getContext()), clearAddress);
  Value *IntPointer =
      irb.CreatePtrToInt(MAllocP, irb.getInt64Ty(), Prefix + ".to.int");
  Value *ClearInt = irb.CreateAnd(IntPointer, clearBit, Prefix + ".and");
  Value *ClearPointer =
      irb.CreateIntToPtr(ClearInt, MAllocP->getType(), Prefix + ".clear");
  return ClearPointer;
}

void valuePrint(Value *value, std::string prefix)
{
  if (!value)
    return;
  errs() << prefix << ": ";
  value->print(errs());
  errs() << "\n";
}

void instPrint(Instruction *inst, std::string prefix)
{
  if (!inst)
    return;
  errs() << prefix << ": ";
  inst->print(errs());
  errs() << "\n";
}
bool isFunctionPtrTy(Type *type)
{
  if (type->isPointerTy())
  {
    PointerType *ptrTy = dyn_cast<PointerType>(type);
    return ptrTy->getPointerElementType()->isFunctionTy();
  }
  return false;
}

bool isFunctionPtrPtrTy(Type *type)
{
  if (type->isPointerTy())
  {
    PointerType *ptrTy = dyn_cast<PointerType>(type);
    if (ptrTy->getPointerElementType()->isPointerTy())
    {
      PointerType *ptrPtrTy =
          dyn_cast<PointerType>(ptrTy->getPointerElementType());
      return ptrPtrTy->getPointerElementType()->isFunctionTy();
    }
  }
  return false;
}
void typePrint(Type *type, std::string prefix)
{
  assert(type);
  if (StructType *st = dyn_cast<StructType>(type))
  {
    errs() << prefix << ": ";
    st->print(errs());
    errs() << "\n";
  }
  else if (PointerType *pt = dyn_cast<PointerType>(type))
  {
    errs() << prefix << ": *";
    pt->getPointerElementType()->print(errs());
    errs() << "\n";
  }
  else
  {
    errs() << prefix << ": ";
    type->print(errs());
    errs() << "\n";
  }
}

void deleteFunctionInst(Function &F)
{
  // F.print(errs());
  for (Instruction &I : instructions(F))
  {
    // I.dropAllReferences();
    if (Value *v = dyn_cast<Value>(&I))
    {
      for (Value *use : v->users())
      {
        valuePrint(use, "use");
      }
      v->dropDroppableUses();
    }
    I.dropAllReferences();
    I.dropDroppableUses();
  }
  for (Instruction &I : instructions(F))
  {
    instPrint(&I, "I");
    I.eraseFromParent();
  }
}
bool isI128TypeEqual(Type *type)
{
  typePrint(type, "Type: ");
  if (type->isIntegerTy())
  {
    if (type->getIntegerBitWidth() == 128)
      return true;
  }
  return false;
}