#include <llvm/ADT/TinyPtrVector.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ScalarEvolutionExpander.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/NoFolder.h>
#include <llvm/Transforms/Utils/Local.h>
#include <llvm/Transforms/Utils/LoopUtils.h>
#include <llvm/Analysis/DependenceAnalysis.h>
#include <llvm/IR/LLVMContext.h>
#include <initializer_list>

#include "AddressSpace.h"
#include "MPAvailable.h"
#include "util.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/ADT/Statistic.h"
#define DEBUG_TYPE "EPSILON"

using namespace llvm;

char MPAvailable::ID = 0;

#if (!LLVM_ENABLE_STATS)

#undef STATISTIC
#define CUSTOM_STATISTICS 1
#define STATISTIC(X,Y) \
unsigned long X;\
const char* X##_desc = Y;

#define STATISTICS_DUMP(X) \
    errs()<<"    "<<X<<" : "<<X##_desc<<"\n";

#endif

STATISTIC(NEpsilon,   "Number of Epsilon");


// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerSkeletonPass(const PassManagerBuilder &,
                                 legacy::PassManagerBase &PM) {
  PM.add(new DominatorTreeWrapperPass());
  PM.add(new LoopInfoWrapperPass());
  PM.add(new ScalarEvolutionWrapperPass());
  PM.add(new DependenceAnalysisWrapperPass());
  PM.add(new MPAvailable());
}
static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_EnabledOnOptLevel0,
                   registerSkeletonPass);

 

void MPAvailable::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<ScalarEvolutionWrapperPass>();
  AU.addRequired<DependenceAnalysisWrapperPass>();
  // AU.addRequired<DominanceFrontier>();
  // AU.addRequired<SymbolicRangeAnalysis>();
  // AU.addRequired<>();
  AU.setPreservesAll();
}

void MPAvailable::createXmmStructTy(Module &M){
  //std::list<Type> xmm_elements = {Type::getInt64Ty(M.getContext()), Type::getInt64Ty(M.getContext())};
  ArrayRef<Type*> xmm_element_types( {Type::getInt64Ty(M.getContext()), Type::getInt64Ty(M.getContext())});
  static LLVMContext TheContext;

  XMM_POINTER = StructType::create(TheContext, xmm_element_types, "XMM_WRAP_POINTER");
  XMM_POINTER->print(errs());
}

void MPAvailable::replaceAllocaXMMP(Function& F){
  for(Instruction& I : instructions(F)){
    switch(I.getOpcode()){
      case Instruction::Alloca:
        AllocaInst* ai = dyn_cast<AllocaInst>(&I);
        ai->getType()->print(errs());
        errs()<<ai->getType()->getContainedType(0)->isPointerTy()<<"\n";
        if(ai->getType()->isPointerTy()&&ai->getType()->getContainedType(0)->isPointerTy()){
          IRBuilder<> irb(getInsertPointAfter(&I));
          AllocaInst* xmm_ai = irb.CreateAlloca(XMM_POINTER, nullptr, dyn_cast<Value>(ai)->getName()+"_XMM");
          ptrToXMM[ai] = xmm_ai;
          xmmToType[ai] = ai->getType();

          instPrint(ai, "ai");
          instPrint(xmm_ai, "xmm_ai");
          //replaceAllUsesWith는 타입이 같아야만 이루어짐 
          
          replaceAll(ai, xmm_ai);
          ai->eraseFromParent();
          //여기서 바로 지우지 말고 모든 인스트럭션이 교체된 후에 지울것, 왜냐하면 포인터가 어떤 타입의 포인터인지 알기 위해서임
          //기존의 AI는 allocMPointer에서 삭제됨
        }
      break;
    }
  }
}

bool MPAvailable::runOnModule(Module &M) {
  DL = &M.getDataLayout();
  errs() <<"Run on XMM Module\n";
  DenseMap<Value *, const SCEV *> PointerBounds;

  createXmmStructTy(M);
  for (auto &F : M) {
    
    if (!F.hasName()) {
      errs() << "F has no name \n";
      continue;
    }
    if (!(&F))
      continue;
    if (F.isDeclaration())
      continue;
    DT = &getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
    LI = &getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
    SE = &getAnalysis<ScalarEvolutionWrapperPass>(F).getSE();
    replaceAllocaXMMP(F);
    allocOnFunction(F);
  }
  propagateGEP(M);

  eraseRemoveInstruction();
  STATISTICS_DUMP(NEpsilon);
  return false;
}


static void setSafeName(Value *V) {
  // Void values can not have a name
  if (V->getType()->isVoidTy())
    return;

  // Don't corrupt externally visable symbols
  GlobalValue *GV = dyn_cast<GlobalValue>(V);
  if (GV && GV->isDeclarationForLinker())
    return;

  // Don't name values that are not globals or instructions
  if (!GV && !isa<Instruction>(V))
    return;

  // Add name to anonymous instructions
  if (!V->hasName()) {
    V->setName("safe.anon");
    return;
  }

  // Don't corrupt llvm.* names
  if (V->getName().startswith("llvm."))
    return;

  // Don't rename twice
  if (V->getName().startswith("safe."))
    return;

  // Default: prefix name with "safe."
  V->setName(Twine("safe.") + V->getName());
}


bool MPAvailable::libCallReturnsSameObjectPointer(CallSite &CS, Value *Param) {
  Function *F = CS.getCalledFunction();
  assert(F);
  assert(F->isDeclaration());

  int Arg;
  switch (getLibPtrType(F, &Arg)) {
  case LibPtr::Strtok:
  case LibPtr::CopyFromArg:
  case LibPtr::PtrDiff:
    return CS.getArgOperand(Arg) == Param;
  default:
    return false;
  }

  return false;
}

bool MPAvailable::isNotDereferencedInLastLoopIteration(GetElementPtrInst *GEP,
                                                       InductionDescriptor &D) {
  // If the pointer is a GEP in a loop ...
  const SCEV *SC = SE->getSCEV(GEP);
  ifncast(const SCEVAddRecExpr, AR, SC) return false;

  const Loop *L = AR->getLoop();

  // ... and all users are loads/stores within the loop ...
  SmallVector<Instruction *, 4> Derefs;
  for (User *U : GEP->users()) {
    if (LoadInst *LI = dyn_cast<LoadInst>(U)) {
      Derefs.push_back(LI);
    } else if (StoreInst *SI = dyn_cast<StoreInst>(U)) {
      if (SI->getValueOperand() == GEP)
        return false;
      Derefs.push_back(LI);
    } else {
      return false;
    }
  }

  // ... and it is based on the loop induction variable ...
  if (GEP->getNumOperands() != 2)
    return false;

  ifncast(PHINode, PN, GEP->getOperand(1)) return false;

  assert(AR->getLoop()->getLoopPreheader());
  if (!InductionDescriptor::isInductionPHI(PN, L, SE, D))
    return false;

  // ... which determines the exit condition of the loop ...
  BranchInst *Br;
  Value *ComparedExitValue = getComparedLoopExitValue(L, PN, Br);
  if (!ComparedExitValue)
    return false;

  const SCEV *ExitExpr = SE->getSCEVAtScope(AR, L->getParentLoop());
  assert(SE->hasOperand(ExitExpr, SE->getSCEV(ComparedExitValue)));

  // ... and the branch dominates all loads/stores ...
  for (Instruction *Deref : Derefs) {
    if (!DT->dominates(Br, Deref)) {
      return false;
    }
  }

  // ... then the pointer is never dereferenced in the last iteration
  return true;
}

Value *MPAvailable::getComparedLoopExitValue(const Loop *L, Value *V,
                                             BranchInst *&Br) {
  if (!L->hasDedicatedExits())
    return nullptr;

  Br = dyn_cast<BranchInst>(L->getHeader()->getTerminator());

  if (!Br || Br->isUnconditional())
    return nullptr;

  ifncast(ICmpInst, Cmp, Br->getCondition()) return nullptr;

  if (Cmp->getPredicate() != ICmpInst::ICMP_EQ)
    return nullptr;

  if (L->contains(Br->getSuccessor(0)) || !L->contains(Br->getSuccessor(1)))
    return nullptr;

  if (Cmp->getOperand(0) == V)
    return Cmp->getOperand(1);
  else if (Cmp->getOperand(1) == V)
    return Cmp->getOperand(0);

  return nullptr;
}

const SCEV *MPAvailable::getSizeOfSCEV(Type *Ty) {
  return SE->getSizeOfExpr(Type::getInt64Ty(Ty->getContext()), Ty);
}

const SCEV *MPAvailable::addSCEVs(const SCEV *LHS, const SCEV *RHS) {
  if (!LHS) {
    assert(RHS);
    return RHS;
  }
  if (!RHS) {
    assert(LHS);
    return LHS;
  }
  return SE->getAddExpr(LHS, RHS);
}

const SCEV *MPAvailable::getPointerCastOrArithOffset(Instruction *UI,
                                                     Value *I) {
  switch (UI->getOpcode()) {
  case Instruction::BitCast:
  case Instruction::PtrToInt:
  case Instruction::IntToPtr:
    return SE->getZero(Type::getInt64Ty(UI->getContext()));
  case Instruction::GetElementPtr:
    return getGEPOffsetSCEV(cast<GetElementPtrInst>(UI));
  case Instruction::Add:
    return SE->getSCEV(otherOperand(UI, I));
  case Instruction::Sub:
    if (UI->getOperand(0) == I)
      return SE->getNegativeSCEV(SE->getSCEV(UI->getOperand(1)));
    break;
  default:
    break;
  }
  return nullptr;
}

const SCEV *MPAvailable::getGEPOffsetSCEV(GetElementPtrInst *GEP, bool NoWrap) {
  Value *Base = GEP->getPointerOperand();
  const SCEV *Offset = SE->getMinusSCEV(SE->getSCEV(GEP), SE->getSCEV(Base));
  if (NoWrap) {
    Offset = addNoWrapFlags(Offset);
    SE->forgetValue(GEP);
  }
  return Offset;
}

const SCEV *MPAvailable::addNoWrapFlags(const SCEV *V) {
  // TODO: if we don't need this, remove it

  // FIXME: this appears to make stuff persistent even if you call
  // forgetValue (?)
  SmallVector<const SCEV *, 3> Ops;

  ifcast(const SCEVNAryExpr, NAry, V) {
    for (const SCEV *Op : NAry->operands())
      Ops.push_back(addNoWrapFlags(Op));
  }
  else ifcast(const SCEVCastExpr, Cast, V) {
    Ops.push_back(addNoWrapFlags(Cast->getOperand()));
  }
  else ifcast(const SCEVUDivExpr, UDiv, V) {
    Ops.push_back(addNoWrapFlags(UDiv->getLHS()));
    Ops.push_back(addNoWrapFlags(UDiv->getRHS()));
  }

  // SCEV::NoWrapFlags Flags = ScalarEvolution::setFlags(SCEV::FlagNUW,
  // SCEV::FlagNSW);
  SCEV::NoWrapFlags Flags = SCEV::FlagNSW;

  switch (static_cast<SCEVTypes>(V->getSCEVType())) {
  case scAddExpr:
    return SE->getAddExpr(Ops, Flags);
  case scMulExpr:
    return SE->getMulExpr(Ops, Flags);
  case scUDivExpr:
    return SE->getUDivExpr(Ops[0], Ops[1]);
  case scAddRecExpr:
    return SE->getAddRecExpr(Ops, cast<SCEVAddRecExpr>(V)->getLoop(), Flags);
  case scSignExtend:
    return SE->getSignExtendExpr(Ops[0], V->getType());
  case scZeroExtend:
    return SE->getZeroExtendExpr(Ops[0], V->getType());
  case scTruncate:
    return SE->getTruncateExpr(Ops[0], V->getType());
  case scConstant:
  case scUnknown:
  case scSMaxExpr:
  case scUMaxExpr:
  case scCouldNotCompute:
    return V;
  }

  llvm_unreachable("broken out of covered switch");
}


void MPAvailable::allocation(Module &M) {
  for (Function &F : M) {
    allocOnFunction(F);
  }
}

void MPAvailable::propagateGEP(Module &M) {
  for (Function &F : M) {
    if (F.isDeclaration())
      continue;
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E;) {
      inst_iterator vI = I;
      I++;
      
      switch (vI->getOpcode()) {
      case Instruction::Store: {
        StoreInst *si = dyn_cast<StoreInst>(&*vI);
        handleStore(si);
        break;
      }
      case Instruction::GetElementPtr:{
        GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(&*vI);
        handleGEP(gep);
        break;
      }

      case Instruction::Load:
      {

        LoadInst *li = dyn_cast<LoadInst>(&*vI);
        handleLoad(li);
        break;
      }
      }
    }
  }
}

void MPAvailable::allocOnFunction(Function &F) {
  //SRA = &getAnalysis<SymbolicRangeAnalysis>(F);
  //ScalarEvolution *SE = &getAnalysis<ScalarEvolutionWrapperPass>(F).getSE();
  for (Instruction &I : instructions(F)) {
    if (isAllocation(&I))
      allocEpsilon(I, SE);

    if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
      Function *F = CallSite(&I).getCalledFunction();
      if (F && F->isDeclaration())
        continue;
    }
  }
}

void MPAvailable::allocEpsilon(Instruction& I, ScalarEvolution *SE){
  if(isa<BitCastInst>(I.getNextNode())){
    IRBuilder<> irb(getInsertPointAfter(I.getNextNode()));
    allocMPointer(I, SE, irb);
  } else{
    IRBuilder<> irb(getInsertPointAfter(&I));
    allocMPointer(I, SE, irb);
  }
}

void MPAvailable::allocMPointer(Instruction &I, ScalarEvolution *SE, IRBuilder<>& irb) {
  // base 태그 생성 테스트 끝
  // errs() << I << "\n";
  Value *ptr = dyn_cast<Value>(&I); // maskMallocWrapper(irb, I);

  if (isStackValue(&I))
    return;

  Value *Size = instrumentWithByteSize(irb, &I, *DL);
  
  Value* newSize;

  Value* allocaVar;
  BitCastInst* bci = nullptr;
  Instruction* origStore;
  if(bci = dyn_cast<BitCastInst>( I.getNextNode())){
    allocaVar = bci->getNextNode()->getOperand(1);
    origStore = bci->getNextNode();
  } else{
    allocaVar = I.getNextNode()->getOperand(1);
    origStore = I.getNextNode();
  }
  //일단 태그 만들기
  instPrint(&I, "allocMP");
  instPrint(origStore, "orig");
  valuePrint(allocaVar, "allocVar");
  ArrayRef<Value*> maskGEP = {ConstantInt::get(IntegerType::get(I.getContext(), 64), 0), ConstantInt::get(IntegerType::get(I.getContext(), 64), 0)};
  ArrayRef<Value*> maskAddr = {ConstantInt::get(IntegerType::get(I.getContext(), 64), 0), ConstantInt::get(IntegerType::get(I.getContext(), 64), 1)};
  Value* mask = irb.CreateGEP(allocaVar, maskGEP, ".MASK");
  Value* address = irb.CreateGEP(allocaVar, maskAddr, ".PTR");
  Value *OvSz = createMask(irb, newSize);
  Value *PtrInt = irb.CreatePtrToInt(ptr, irb.getInt64Ty());

  irb.CreateStore(OvSz, mask);
  irb.CreateStore(address, PtrInt);

  origStore->eraseFromParent();
  if(bci) bci->eraseFromParent();

  for(auto it : ptrToXMM){
    AllocaInst* orig = it.first;
    AllocaInst* replace = it.second;
    orig->replaceAllUsesWith(replace);
    orig->eraseFromParent();
  }
}


Constant *MPAvailable::getNullPtr(PointerType *Ty) {
  IntegerType *IntTy = IntegerType::get(Ty->getContext(), 64);
  ConstantInt *IntVal = ConstantInt::get(IntTy, BOUND_MASK_HIGH);
  return ConstantExpr::getIntToPtr(IntVal, Ty);
}


void MPAvailable::handleGEP(GetElementPtrInst *gep) {
  //GEP에서 add, sub가 이루어져야됨
  //먼저 포인터 만들고
  //그 다음 offset, 
  //만약 xmm_offset이 마이너스면 subtraction으로 만들것
  //xmm레지스터의 sub 돌아가는 원리를 모르니까 

  //기존코드: STORE나 LOAD가 이루어질때 GEP를 거치기 때문에 STORE, LOAD가 이루어질때 GEP를 바꿧으나
  //STORE, LOAD와 상관없이 바꾸는 새 코드로 만들기
  //AllocaInst->Load->GEP 
  //기존의 LOAD가 Xmm AllocaInst로 바뀌어있음
  //LOAD 인스트럭션의 operand 확인 
  //오퍼랜드의 타입이 xmm alloca 면 여기서 핸들링 
  //아니라면 
  //에러처리 그리고 출력할 것 그런 케이스 확인하기 위해서
  IRBuilder<> irb(getInsertPointAfter(gep));


  Value* xmm_pointer;
  Value* xmm_offset;  
  GetElementPtrInst *PreemptedGep = nullptr;

  if (!gep)
    return;


  if(gep->getOperand(0)->getType() != XMM_POINTER) return ;
  if (gep->getPointerOperand()->getType()->getContainedType(0) != XMM_POINTER) return ;
  //XMM 포인터는 기존의 포인터 변수 대신에 내가 만든 구조체로 할당되기 때문에 
  //gep 이전의 load도 다시 해야 됨
  //

  bool isPositive = hasNegativeOffset(gep);
  
  Value *base = gep->getPointerOperand()->stripPointerCasts(); // base는 load 인스트럭션
  LoadInst* origLoad = dyn_cast<LoadInst>(base);
  Value *origPtr = origLoad->getOperand(0);
  AllocaInst* origAlloca = dyn_cast<AllocaInst>(origPtr);
  AllocaInst* xmmAlloca = ptrToXMM[origAlloca];
  Value* xmmPtr = dyn_cast<Value> (xmmAlloca);
  Value* xmmBase = irb.CreateLoad(xmmPtr, base->getName() + ".xmm");

  willBeRemoveSet.insert(origLoad);
  
  Value *tag;
  uint64_t constOffset;

  if (!gep)
    return;
  if (gep->getType()->isVectorTy())
    return;
  std::vector<User *> Users(gep->user_begin(), gep->user_end());

  Value *Diff;
  Value *addOffset;
  ConstantInt *ConstOffset = nullptr;
  APInt ConstOffsetVal(64, 0);
  IntegerType *PtrIntTy = getPtrIntTy(gep->getContext());
  std::string Prefix = std::string(base->getName()) + "." + ".array.";

  Value *PtrInt = irb.CreateBitCast(base, Type::getIntNTy(gep->getContext(), 128));
      //cast<Instruction>(irb.CreatePtrToInt(ptrToXMM[base], PtrIntTy, Prefix + "int"));

  if (gep->accumulateConstantOffset(*DL, ConstOffsetVal))
    ConstOffset = irb.getInt(ConstOffsetVal);

  //const 일경우 -1. 양수, 2. 음수
  //const 아닐 경우 - 1. 양수, 음수
  
  //속도를 위해선 메모리 load나 레지스터 거쳐가는 것을 최대한 줄일것
  if (ConstOffset&&isPositive) {
    //const 이면서 양수일 때,
    Diff = ConstOffset;
    constOffset = ConstOffset->getSExtValue();
    Constant* constIndex = ConstantInt::get(IntegerType::get(gep->getContext(),128), constOffset);
    tag = createXmmTag(irb, constIndex);
    addOffset = irb.CreateAnd(tag, Diff);
  } else if(isPositive){
    //const 아니고 양수일 때,
    Diff = EmitGEPOffset(&irb, *DL, PreemptedGep);
    tag = createXmmTag(irb, Diff);
    addOffset = irb.CreateAnd(tag, Diff);
  } else if(ConstOffset){
    //const 인데, 음수임
    constOffset = -(ConstOffset->getSExtValue());
    Constant* constValue = ConstantInt::get(IntegerType::get(gep->getContext(), 64), constOffset);
    tag = createXmmTag(irb, constValue);
    Value* tempAddOffset = irb.CreateAnd(tag, constOffset);
    addOffset = tempAddOffset;
  } else{
    Diff = EmitGEPOffset(&irb, *DL, PreemptedGep);
    Value* neg = irb.CreateNeg(Diff);
    tag = createXmmTag(irb, neg);
    Value* tempAddOffset = irb.CreateAnd(tag, Diff);
    addOffset = tempAddOffset;
  }
  
  //tag를 만들고 나서 보수하는거니까 tag하고 나서 확인하고 해도 되지
  Value *PtrAdd;

  if(isPositive) PtrAdd = irb.CreateAdd(PtrInt, addOffset, Prefix+".added");
  else PtrAdd = irb.CreateSub(PtrInt, addOffset, Prefix+".sub");
  Value* result = irb.CreateBitCast(PtrAdd, XMM_POINTER);
  
  gep->replaceAllUsesWith(result);
  gep->eraseFromParent();
}

bool MPAvailable::hasNegativeOffset(GetElementPtrInst *gep) {
  APInt ConstOffset(64, 0);
  if (gep->accumulateConstantOffset(*DL, ConstOffset))
    return ConstOffset.isNegative();

  // For synamid offsets, look for the pattern "gep %base, (sub 0, %idx)"
  // XXX this is best-effort and may not catch all cases
  for (int i = 1, l = gep->getNumOperands(); i < l; i++) {
    Value *Index = gep->getOperand(i);

    Instruction *I = dyn_cast<Instruction>(Index);
    if (I == nullptr)
      continue;
    if (I->getOpcode() != Instruction::Sub)
      continue;

    ConstantInt *PossibleZero = dyn_cast<ConstantInt>(I->getOperand(0));
    if (PossibleZero == nullptr)
      continue;
    if (PossibleZero->getSExtValue() == 0)
      return true;
  }

  return false;
}

void MPAvailable::handleStore(StoreInst *si) {
  // GEP->STORE
  // LOAD->STORE
  // TYPE 검사
  Value* addr = si->getOperand(1);

  IRBuilder<> irb(getInsertPointAfter(si));
  if (addr->getType() == XMM_POINTER)
  {
    Value *clearTagPointer = clearTag(addr, irb, addr->getName());
    Value *replaceInst = irb.CreateLoad(clearTagPointer, si->getName() + "clear.bit");
    si->replaceAllUsesWith(replaceInst);
    si->eraseFromParent();
  }
  return;
}

void MPAvailable::handleLoad(LoadInst *li) {
  //오퍼랜드가 GEP인지 아니면 AllocaInst 인지 확인해야함 
  //GEP->LOAD
  //AllocaInst->LOAD
  //LOAD->LOAD
  Value* liOp = li->getPointerOperand();
  if(dyn_cast<AllocaInst>(liOp)){
    return ;
  }
  else if (liOp->getType() == XMM_POINTER)
  {
    //태그 클리어 및 로드하는 인스트럭션으로 바꿔주기
    //타입 확인도 할것
    IRBuilder<> irb(getInsertPointAfter(li));
    Value *clearTagPointer = clearTag(liOp, irb, liOp->getName());
    Value *replaceInst = irb.CreateLoad(clearTagPointer, liOp->getName() + "clear.bit");
    li->replaceAllUsesWith(replaceInst);
    li->eraseFromParent();
  }
}

bool MPAvailable::isInnerTagPossible(Value *size) {
  if (ConstantInt *intSize = dyn_cast<ConstantInt>(size)) {
    int realSize = intSize->getSExtValue();
    if (realSize <= 128)
      return true;
    else
      return false;
  } else {
    //SRA->
    const SCEV *sc = SE->getSCEV(size);
    if(sc->isAllOnesValue()){
      ConstantRange cr = SE->getUnsignedRange(sc);
      if(cr.isEmptySet()) return false;
      APInt ai = cr.getUnsignedMax();
      int64_t intSize = ai.getSExtValue();
      if(intSize > 128) return false;//if(>128) return false;
      else return true;
    } else return false;
  }
  return false;
}

void MPAvailable::sizeToIndex(Value* size, Type* type, IRBuilder<>& irb, std::string prefix){
  //Size is INPUT of MALLOC. 
  //size = sizeof(type)*index;
  if(ConstantInt* intSize = dyn_cast<ConstantInt>(size)){
    int realSize = intSize->getSExtValue();
    type->getPointerAddressSpace();
  }
}

void MPAvailable::initFunction(Module &M) {
  Type *PtrIntTy = getPtrIntTy(M.getContext());
  AddWithOverflowFunc =
      Intrinsic::getDeclaration(&M, Intrinsic::uadd_with_overflow, PtrIntTy);
}

void MPAvailable::eraseRemoveInstruction() {
  for(Instruction* inst: willBeRemoveSet) inst->eraseFromParent();
}

Value* MPAvailable::clearTag(Value* xmmPtr, IRBuilder<>& irb, std::string prefix){
  // xmmPtr 은 XMMP 구조체 
  // 먼저, tag 갖고 오기 tag 가공해야됨 그 이유는 상위 17bit으로 몰아주기 위해서 
  // 그 다음 메모리 주소 bitcast 하기
  // and 연산해서 바꿔주기 
  Value* xmmTag = irb.CreateInBoundsGEP(XMM_POINTER, xmmPtr, ConstantInt::get(Type::getInt8Ty(irb.getContext()), 0), prefix + ".tag");
  Value* xmmOffset = irb.CreateInBoundsGEP(XMM_POINTER, xmmPtr, ConstantInt::get(Type::getInt8Ty(irb.getContext()), 1), prefix + ".offset");

  Value* xmmTagAnd = irb.CreateAnd(xmmTag, 0x8000000080000000, prefix + ".tag.and"); //여기서 이미 태그를 제외한 메타데이터 클리어가 됨
  Value* xmmTagOverShl = irb.CreateShl(xmmTagAnd, 31, prefix + ".tag.over.shl");
  Value* xmmTagAssemble = irb.CreateOr(xmmTagAnd, xmmTagOverShl, prefix + "tag.assemble");
  Value* xmmTagResult = irb.CreateAnd(xmmTagAssemble, 0xC000000000000000, prefix + ".result");
  
  Value* clearPointer = irb.CreateOr(xmmTagResult, xmmOffset, prefix + ".clear");
  Value* result = irb.CreateBitCast(clearPointer, xmmToType[dyn_cast<AllocaInst>(xmmPtr)], prefix + ".unwrap");

  return result;
}

void MPAvailable::replaceAll(Value* orig, Value* replacer){
  for( User* use : orig->users()){
    if(Instruction* inst = dyn_cast<Instruction>(use)){
      instPrint(inst, "replace");
      switch (inst->getOpcode()){
        case Instruction::Load:{
          inst->setOperand(0, replacer);
          break;
        }
        case Instruction::Store:{
          inst->setOperand(1, replacer);
          break;
        }
      }
    }
  }
}

void MPAvailable::transFormation(Function* F){

}
static RegisterPass<MPAvailable> MPAVAILABLE("mpav", "MPAvailable");