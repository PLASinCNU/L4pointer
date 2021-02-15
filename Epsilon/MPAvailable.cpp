#include <llvm/ADT/TinyPtrVector.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ScalarEvolutionExpander.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/NoFolder.h>
#include <llvm/Transforms/Utils/Local.h>
#include <llvm/Transforms/Utils/LoopUtils.h>
#include <llvm/Analysis/DependenceAnalysis.h>

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

using namespace llvm;

char MPAvailable::ID = 0;

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerSkeletonPass(const PassManagerBuilder &,
                                 legacy::PassManagerBase &PM) {
  PM.add(new MPAvailable());
}
static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
                   registerSkeletonPass);



void MPAvailable::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<ScalarEvolutionWrapperPass>();
  AU.addRequired<DependenceAnalysisWrapperPass>();
  // AU.addRequired<DominanceFrontier>();
  //AU.addRequired<SymbolicRangeAnalysis>();
  //AU.addRequired<>();
  AU.setPreservesAll();
}

bool MPAvailable::runOnModule(Module &M) {
  DL = &M.getDataLayout();

  DenseMap<Value *, const SCEV *> PointerBounds;

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
    allocOnFunction(F);
  }
  propagateGEP(M);
  return false;
}

void MPAvailable::propagateAllocationBounds(
    Function &F, DenseMap<Value *, const SCEV *> &PointerBounds) {
  SmallVector<std::pair<Instruction *, const SCEV *>, 16> Worklist;

  // TODO: propagate argument type bounds (?)

  for (Instruction &I : instructions(F)) {
    if (isAllocation(&I)) {
      Worklist.push_back(std::make_pair(&I, getSizeSCEV(&I, *SE)));
    } else if (I.getNumOperands() > 0) {
      ifncast(GlobalVariable, GV, I.getOperand(0)) continue;

      const SCEV *Size = getGlobalSizeSCEV(GV, *SE);

      switch (I.getOpcode()) {
      case Instruction::BitCast:
      case Instruction::PtrToInt:
      case Instruction::IntToPtr:
        Worklist.push_back(std::make_pair(&I, Size));
        break;
      case Instruction::GetElementPtr:
        Worklist.push_back(std::make_pair(
            &I, SE->getMinusSCEV(
                    Size, getGEPOffsetSCEV(cast<GetElementPtrInst>(&I)))));
        break;
      case Instruction::Call:
      case Instruction::Invoke:
        // TODO: use libptrret info
        break;
      default:
        break;
      }
    }
  }

  while (!Worklist.empty()) {
    const auto &P = Worklist.pop_back_val();
    Instruction *I = P.first;
    const SCEV *Dist = P.second;

    assert(PointerBounds.count(I) == 0);
    PointerBounds[I] = Dist;

    for (User *U : I->users()) {
      Instruction *UI = cast<Instruction>(U);
      const SCEV *UDist = nullptr;

      switch (UI->getOpcode()) {
      case Instruction::Call:
      case Instruction::Invoke:
        // TODO: use libptrret info
        break;
      case Instruction::ICmp:
      case Instruction::Load:
      case Instruction::Store:
      case Instruction::Ret:
        // Ignored
        break;
      default:
        if (const SCEV *Offset = getPointerCastOrArithOffset(UI, I)) {
          UDist = Offset->isZero() ? Dist : SE->getMinusSCEV(Dist, Offset);
          break;
        }
        break;
      }

      if (UDist)
        Worklist.push_back(std::make_pair(UI, UDist));
    }
  }
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
    EPTagAnalysis epAn = EPTagAnalysis(&F, AllocMpUses, NonAllocMp);
    epAn.runOnFunction();
    if (F.isDeclaration())
      continue;
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E;) {
      inst_iterator vI = I;
      I++;
      
      switch (vI->getOpcode()) {
      case Instruction::Store: {
        if (epAn.checkMP(dyn_cast<Instruction>(&*vI)))
        {
          StoreInst *si = dyn_cast<StoreInst>(&*vI);
          handleStore(si);
        }
        break;
      }
      case Instruction::Load: {
        if (epAn.checkMP(dyn_cast<Instruction>(&*vI)))
        {
          LoadInst *li = dyn_cast<LoadInst>(&*vI);
          handleLoad(li);
        }
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
      allocMPointer(I, SE);

    if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
      Function *F = CallSite(&I).getCalledFunction();
      if (F && F->isDeclaration())
        continue;
    }
  }
}

void MPAvailable::allocMPointer(Instruction &I, ScalarEvolution *SE) {
  // base 태그 생성 테스트 끝
  // errs() << I << "\n";
  IRBuilder<> irb(getInsertPointAfter(&I));
  Value *ptr = dyn_cast<Value>(&I); // maskMallocWrapper(irb, I);

  if (isStackValue(&I))
    return;

  Value *Size = instrumentWithByteSize(irb, &I, *DL);
  if(!isInnerTagPossible(Size)) {
    NonAllocMp.insert(&I);
    return ;
  }else AllocMpUses.insert(&I);

  Value *OvSz = createOverMask(irb, Size);

  Value *PtrInt = irb.CreatePtrToInt(ptr, irb.getInt64Ty());
  Value *Tagged = irb.CreateOr(PtrInt, OvSz);
  Value *NewPtr = irb.CreateIntToPtr(Tagged, ptr->getType(),
                                     Twine(ptr->getName()) + ".tagged");
  TagPtrOrigin.insert(NewPtr);
  AllocMpUses.insert(dyn_cast<Instruction>(NewPtr));
  if (ptr->user_empty())
    return;
  std::vector<User *> Users(ptr->user_begin(), ptr->user_end());
  for (User *U : Users) {
    Instruction *comesAfter = dyn_cast<Instruction>(U);
    Instruction *comesBefore = dyn_cast<Instruction>(NewPtr);
    if (comesBefore->comesBefore(
            comesAfter)) { // Order < other->Order comesBefore < comesAfter
      U->replaceUsesOfWith(
          ptr,
          NewPtr); // 이부분이 old 포인터가 반드시 쓰여야 되는 지점것까지 교체함
      errs()<< " User: ";
      U->print(errs());
      errs() <<"\n";
      for(User *UU: U->users()){
        errs() << " UUser: ";
        UU->print(errs());
        errs() << "\n";
      }
      AllocMpUses.insert(comesAfter);
    }
  }
}

Value *MPAvailable::maskMallocWrapper(IRBuilder<> &B, Instruction &I) {
  Value *ptr = dyn_cast<Value>(&I);

  if (!isHeapAlloc(I))
    return ptr;
  std::vector<User *> Users(ptr->user_begin(), ptr->user_end());

  std::string Prefix = ptr->hasName() ? ptr->getName().str() + "." : "";

  Value *PtrInt = B.CreatePtrToInt(ptr, Type::getInt64Ty(ptr->getContext()),
                                   Prefix + "int");
  Value *Masked = B.CreateAnd(PtrInt, getAddressSpaceMask(), Prefix + "mask");
  Value *NewPtr =
      B.CreateIntToPtr(Masked, ptr->getType(), Prefix + "unwrapped");

  for (User *U : Users)
    U->replaceUsesOfWith(ptr, NewPtr);

  return NewPtr;
}

Constant *MPAvailable::getNullPtr(PointerType *Ty) {
  IntegerType *IntTy = IntegerType::get(Ty->getContext(), 64);
  ConstantInt *IntVal = ConstantInt::get(IntTy, BOUND_MASK_HIGH);
  return ConstantExpr::getIntToPtr(IntVal, Ty);
}


void MPAvailable::handleGEP(GetElementPtrInst *gep, IRBuilder<> &irb,
                            std::string prefix) {
  GetElementPtrInst *PreemptedGep = nullptr;

  if (!gep)
    return;

  Value *base = gep->getPointerOperand()->stripPointerCasts();
  valuePrint(base, "base");
  if (!gep)
    return;
  if (gep->getType()->isVectorTy())
    return;
  std::vector<User *> Users(gep->user_begin(), gep->user_end());

  Value *Diff;
  ConstantInt *ConstOffset = nullptr;
  APInt ConstOffsetVal(64, 0);
  IntegerType *PtrIntTy = getPtrIntTy(gep->getContext());
  std::string Prefix = std::string(base->getName()) + "." + prefix + ".array.";

  Instruction *PtrInt =
      cast<Instruction>(irb.CreatePtrToInt(base, PtrIntTy, Prefix + "int"));

  if (gep->accumulateConstantOffset(*DL, ConstOffsetVal))
    ConstOffset = irb.getInt(ConstOffsetVal);

  //결국 이 PreemptedOffset의 용도는 필요없기 때문에 그에 맞게 바꿔줘야됨
  //삭제함
  if (ConstOffset) {
    Diff = ConstOffset;
  } else {
    Diff = EmitGEPOffset(&irb, *DL, PreemptedGep);
  }

  errs() << "Diff: ";
  Diff->print(errs());
  errs() << "\n";

  Value *Shifted = createTag(irb, Diff);

  Value *AddOffset = Shifted;
  Value *PtrAdd;

  PtrAdd = irb.CreateAdd(PtrInt, AddOffset, Prefix + "added");
  //이부분이 offset 만들고 조정함
  if (hasNegativeOffset(gep)) {
    // diff negation 한 다음에, 이걸로 shift하고, 그다음에 이걸 보수한다
    Value *neg = irb.CreateNeg(Diff);
    valuePrint(neg, "neg");
    Shifted = createTag(irb, neg);
    AddOffset = irb.CreateNeg(Shifted);
    // Value *Zero = ConstantInt::get(PtrIntTy, 0);
    // Value *Mask = ConstantInt::get(PtrIntTy, getAddressSpaceMask());
    // Value *OrigPtrInt =
    //     irb.CreatePtrToInt(gep->getOperand(0), PtrIntTy, Prefix +
    //     "origptrint");
    // Value *HasMeta = irb.CreateICmpUGT(OrigPtrInt, Mask, Prefix + "hasmeta");
    // // 값비교  UGT : unsigned greater than > AddOffset =
    // irb.CreateSelect(HasMeta, Shifted, Zero, Prefix + "offset");  //분기없이
    // HasMeta 값에 Shifted인지 Zero인지 선택 메타데이터값을 갖고 있으면 Shifted
    // 아니면 zero를 채워넣음
    PtrAdd = irb.CreateAdd(PtrInt, AddOffset, Prefix + "sub");
  } else {
    PtrAdd = irb.CreateAdd(PtrInt, AddOffset, Prefix + "added");
  }
  Value *NewPtr = irb.CreateIntToPtr(PtrAdd, gep->getType(), Prefix + "newptr");

  gep->replaceAllUsesWith(
      NewPtr); // 왜 지워지는지 암, 그 이유는 gep를 통해 NewPtr이 만들어지는데
               // gep가 사라지기 때문, 그래서 gep대신에 원래의 포인터로 NewPtr을
               // 만들어야됨
  // gep->removeFromParent();
  gep->eraseFromParent();
  // for (User *U : Users)
  //   U->replaceUsesOfWith(gep, NewPtr);
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
  // GEP 없이 LOAD -> STORE 하는 패턴이 있음, 그 경우에 대한 대처가 필요함
  valuePrint(si, "si: ");
  Value *newPtr;
  Value *clearTagPointer;
  Value *replaceInst;

  GetElementPtrInst *gep;
  gep = dyn_cast<GetElementPtrInst>(si->getPointerOperand());
  if (!gep) {
    gep = dyn_cast<GetElementPtrInst>(si->getValueOperand());
  }

  if (!gep) {
    // LOAD -> STORE without GEP, this is the case, only clear.
    if (isa<AllocaInst>(si->getPointerOperand()))
      return;
    IRBuilder<> irb(getInsertPointAfter(si));
    newPtr = si->getPointerOperand();
    typePrint(si->getOperand(1)->getType(), "ptr_ type");
    clearTagPointer = getClearTagPointer(irb, newPtr, "store");
    replaceInst = irb.CreateStore(si->getValueOperand(), clearTagPointer);
    si->replaceAllUsesWith(replaceInst);
    si->eraseFromParent(); // For use this statement for debug, annotate this.
                           // Don't remove it!
    return;
  }

  IRBuilder<> irb(getInsertPointAfter(gep));

  handleGEP(gep, irb, "store");

  if (!dyn_cast<AllocaInst>(si->getOperand(1))) {
    // allocainst인 경우 포인터를 저장하기 위한 변수이므로 태그 클리어 과정이
    // 필요없음
    newPtr = si->getPointerOperand();
    typePrint(si->getOperand(1)->getType(), "ptr_ type");
    clearTagPointer = getClearTagPointer(irb, newPtr, "store");
    replaceInst = irb.CreateStore(si->getValueOperand(), clearTagPointer);
    si->replaceAllUsesWith(replaceInst);
    si->eraseFromParent(); // For use this statement for debug, annotate this.
                           // Don't remove it!
  }
}

void MPAvailable::handleLoad(LoadInst *li) {
  // LOAD->LOAD하는 패턴도 있음
  GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(li->getPointerOperand());
  Value *newPtr;
  Value *clearTagPointer;
  Value *replaceInst;
  if (!gep) {
    //변수로 부터 load한거면 클리어할 필요 없음
    //변수가 아니다? 그럼 무조건 클리어
    if (isa<AllocaInst>(li->getPointerOperand()))
      return;
    IRBuilder<> irb(getInsertPointAfter(li));
    newPtr = li->getPointerOperand();
    clearTagPointer = getClearTagPointer(irb, newPtr, "load");
    replaceInst = irb.CreateLoad(clearTagPointer, "clear.bit");
    li->replaceAllUsesWith(replaceInst);
    li->eraseFromParent();
    return;
  }

  IRBuilder<> irb(getInsertPointAfter(gep));
  handleGEP(gep, irb, "load");

  newPtr = li->getPointerOperand();
  clearTagPointer = getClearTagPointer(irb, newPtr, "load");
  replaceInst = irb.CreateLoad(clearTagPointer, "clear.bit");
  li->replaceAllUsesWith(replaceInst);
  li->eraseFromParent(); // For use this statement for debug, annotate this.
                         // Don't remove it!
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

void MPAvailable::EPTagAnalysis::init(){
  errs() <<" Init\n";
  for(Instruction&I: instructions(F)){
    I.print(errs());
    if(AllocEPSet.find((&I)) != AllocEPSet.end()){
      TagSet[&I].insert(EP);
      errs() <<" : EP";
    }
    else if (NonAllocEPSet.find(&I) != NonAllocEPSet.end())
    {
      TagSet[&I].insert(NONEP);
      errs() <<" : NONEP";
    }
    errs() <<"\n";
  }
}

void MPAvailable::EPTagAnalysis::runOnFunction(){
  bool isChanged = true;
  int loopCount = 0;
  while (isChanged)
  {
    printState();
    DenseMap<Instruction *, std::set<EPTag>> oldState = TagSet;
    for (Instruction &I : instructions(F))
    {
      switch (I.getOpcode())
      {
      case Instruction::Store:
      {
        StoreInst* si = dyn_cast<StoreInst>(&I);
        Value *src = si->getOperand(0);
        Value *dst = si->getOperand(1);
        setUnion(src, dst, isChanged);
        break;
      }
      case Instruction::Load:
      case Instruction::GetElementPtr:
      {
        Value *dst = dyn_cast<Value>(&I);
        Value *src = I.getOperand(0);
        setUnion(src, dst, isChanged);
        break;
      }
      default:
        break;
      }
    }
    //비교루틴 만들기 before == now 비교 
    if(isEqual(oldState, TagSet)) break;
  }
}
void MPAvailable::EPTagAnalysis::setUnion(Value* src, Value* dst, bool& isChanged){
  std::set<EPTag> result = std::set<EPTag>();
  
  std::set<EPTag>& op0_ = TagSet[dyn_cast<Instruction>(src)];
  std::set<EPTag>& op1_ = TagSet[dyn_cast<Instruction>(dst)];

  std::set_union(op0_.begin(), op0_.end(), op1_.begin(), op1_.end(), std::inserter(result, result.begin()));
  TagSet[dyn_cast<Instruction>(dst)] = result;
}

bool MPAvailable::EPTagAnalysis::checkMP(Instruction* I){
  std::set<EPTag>& ITagSet = TagSet[I];
  instPrint(I, "checkMP");
  errs() <<"check!!";
  for(const auto it : TagSet[I]){
    errs() << it << " ";
  }
  errs() << "\n";
  if(ITagSet.find(NONEP) == ITagSet.end()&&ITagSet.find(EP) !=ITagSet.end()) { errs() <<"true\n"; return true;}
  if(ITagSet.find(EP) == ITagSet.end()) {errs() <<"false\n"; return false;}
  return false;
}

void MPAvailable::initFunction(Module &M) {
  Type *PtrIntTy = getPtrIntTy(M.getContext());
  AddWithOverflowFunc =
      Intrinsic::getDeclaration(&M, Intrinsic::uadd_with_overflow, PtrIntTy);
}

bool MPAvailable::EPTagAnalysis::isEqual(DenseMap<Instruction *, std::set<EPTag>>& oldState, DenseMap<Instruction *, std::set<EPTag>>& newState){
  if(oldState.size() != newState.size()) return false;
  for( DenseMap<Instruction *, std::set<EPTag>>::iterator oldit = oldState.begin(); oldit != oldState.end();oldit++){
    if(newState.find(oldit->first) == newState.end()) return false;
    DenseMap<Instruction *, std::set<EPTag>>::iterator newit = newState.find_as(oldit->first);
    if(newit->second != oldit->second) return false;
  }
  return true;
}

void MPAvailable::EPTagAnalysis::printState(){
  errs() << "Print State\n";
  for(Instruction& I: instructions(F)){
    Instruction* inst = &I;
    inst->print(errs());
    errs() << ":: ";
    for(const auto iter : TagSet[inst]){
      errs() << iter <<" ";
    }
    errs() <<"\n";
  }
}
static RegisterPass<MPAvailable> MPAVAILABLE("mpav", "MPAvailable");