#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ScalarEvolutionExpander.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Transforms/Utils/LoopUtils.h>
#include <llvm/ADT/TinyPtrVector.h>
#include <llvm/IR/NoFolder.h>
#include <llvm/IR/Dominators.h>
#include <llvm/Transforms/Utils/Local.h>

#include <initializer_list>

#include "AddressSpace.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "MPAvailable.h"
#include "util.h"
#include "llvm/IR/InstIterator.h"


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

void MPAvailable::findSafeAllocations(Function& F){
  
  for (Instruction &I: instructions(F)){
    if(!isAllocation(&I)) continue;
    setTag(&I);
  }
}

void MPAvailable::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.setPreservesAll();
}

bool MPAvailable::runOnModule(Module &M) {
  DL = &M.getDataLayout();

  DenseMap<Value *, const SCEV *> PointerBounds;
  
  for (auto &F : M) {
    if(!F.hasName()){
      errs() <<"F has no name \n";
      continue;
    }

    if(!(&F)) continue;
    if(F.isDeclaration()) continue;
    DT = &getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
    LI = &getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
    SE = &getAnalysis<ScalarEvolutionWrapperPass>(F).getSE();

    // TODO: find trivially safe pointers in function arguments
    // TODO: use getDereferenceableBytes

    // Find safe GEP instructions

    PointerBounds.clear();

    // find safe GEPs
    propagateAllocationBounds(F, PointerBounds);
    findSafeGEPs(F, PointerBounds);

    // Find safe stack/heap allocations to avoid tagging
    findSafeAllocations(F);

    // Preempt bound checks by setting the metadata offset of a GEP to the
    // highest offset of the base pointer in the same basic block

    //preemptBoundChecks(F);

    
   
  
  }
  // Find safe global allocations to avoid tagging

  //findSafeGlobals(M);

  // Propagate safe status from allocations/geps to loads/stores and libcalls
  // to avoid masking
  propagateSafeTags();
  errs() << "Finished running safe analysis\n";

  // allocation pointer
  allocation(M);
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

void MPAvailable::setTag(Value *Allocation){
  SafeAllocations.insert(Allocation);
  setSafeName(Allocation);
}



bool MPAvailable::isNotDereferencedBeyonedNBytes(Value* Ptr, const SCEV *DistanceToEndOfObject){
  SmallVector<const SCEV*, 8> DerefBytes;
  if (!findAllDereferencedBytes(Ptr, DerefBytes))
    return false;

  for (const SCEV *NBytes : DerefBytes) {
    if (!compareSCEVs(ICmpInst::ICMP_SGE, DistanceToEndOfObject, NBytes))
      return false;
  }
  return true;
}

bool MPAvailable::needsTag(Value *Allocation) {
  //If Allocation is not key in SafeAllocations
  return !SafeAllocations.count(Allocation);
}

bool MPAvailable::needsMask(Instruction *I, Value *Operand) {
    return !SafeMaskSites.count(std::make_pair(I, Operand));
}

bool MPAvailable::needsPropagation(GetElementPtrInst *GEP) {
    return !SafeGEPs.count(GEP);
}

void MPAvailable::propagateSafeTags() {
  SmallVector<std::pair<Instruction *, Value *>, 32> Worklist;

  // Only propagate from safe allocations, we cannot propagate from safe GEPs
  // that can not be traced back to a safe allocation, since those pointers
  // may have metadata
  for (Value *Alloc : SafeAllocations) {
    for (User *U : Alloc->users()) {
      Instruction *UI = dyn_cast<Instruction>(U);
      if(UI == nullptr) continue;

      // No propagation should have happened yet
      assert(hasTag(UI));

      Worklist.push_back(std::make_pair(UI, Alloc));
    }
  }
  DenseSet<std::pair<Instruction *, Value *>> VisitedPHINodes;

  while (!Worklist.empty()) {
    const auto &it = Worklist.pop_back_val();
    Instruction *UI = it.first;
    Value *Ptr = it.second;

    // Depending on the type of user, tag it as safe and/or stop
    // propagation
    switch (UI->getOpcode()) {
    case Instruction::Load:
    case Instruction::Store: {
      // Prevent load/store masking
      setMaskSite(UI, Ptr);
      continue;
    }
    case Instruction::GetElementPtr:
      /* fall through */
    case Instruction::BitCast:
    case Instruction::IntToPtr:
    case Instruction::PtrToInt:
      // Propagate the information that this pointer does not have
      // metadata, this will be used when propagating from safe GEPs
      setTag(UI);
      break;
    case Instruction::Call:
    case Instruction::Invoke: {
      // Prevent libcall argument masking
      if (needsMask(UI, Ptr)) {
        setMaskSite(UI, Ptr);
      }

      // Avoid copying the tag to the return value
      CallSite CS(UI);
      Function *F = CS.getCalledFunction();
      if (F && F->isDeclaration() && libCallReturnsSameObjectPointer(CS, Ptr)) {
        setTag(UI);
        // Continue propagation
        break;
      }

      // Stop propagation
      continue;
    }
    case Instruction::PHI: {
      // Check if all incoming values are safe
      bool allSafe = true;
      PHINode *PN = cast<PHINode>(UI);
      for (Use &U : PN->operands()) {
        if (hasTag(PN->getIncomingValueForBlock(PN->getIncomingBlock(U)))) {
          allSafe = false;
          break;
        }
      }
      if (!allSafe) {
        VisitedPHINodes.insert(it);
        continue;
      }

      setTag(UI);
      break;
    }
    default:
      // TODO: add/sub
      continue;
    }

    // Recurse to users
    for (User *UU : UI->users()) {
      auto P = std::make_pair(cast<Instruction>(UU), UI);
      if (hasTag(UU) && !VisitedPHINodes.count(P))
        Worklist.push_back(P);
    }
  }
}

void MPAvailable::setMaskSite(Instruction* I, Value *Operand){
  SafeMaskSites.insert(std::make_pair(I, Operand));
  setSafeName(Operand);
}

bool MPAvailable::compareSCEVs(ICmpInst::Predicate Pred, const SCEV *LHS, const SCEV *RHS) {
  // DEBUG_LINE(" compare:    " << cmpstr(Pred, LHS, RHS));
  SE->SimplifyICmpOperands(Pred, LHS, RHS);
  // DEBUG_LINE(" simplified: " << cmpstr(Pred, LHS, RHS));
  bool Result = SE->isKnownPredicate(Pred, LHS, RHS);
  // DEBUG_LINE("     result: " << Result);
  return Result;
}

bool MPAvailable::compareSCEVs(ICmpInst::Predicate Pred, Value *LHS, Value *RHS) {
  return compareSCEVs(Pred, SE->getSCEV(LHS), SE->getSCEV(RHS));
}

void MPAvailable::findSafeGEPs(
    Function &F, DenseMap<Value *, const SCEV *> &PointerBounds) {
  for (Instruction &I : instructions(F)) {
    GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(&I); //Ignore this error, no error occurs at compile
    // GetElementPtrInst* GEP = GEP;
    if (GEP == nullptr)
      continue;

    // See if the distance to the end of the object was propagated by
    // propagateAllocationBounds.
    auto it = PointerBounds.find(GEP);
    if (it == PointerBounds.end())
      continue;
    const SCEV *Distance = it->second;

    // Some GEPs in loops use the induction variable, causing SCEV analysis
    // to think that the maximum value of the pointer is the value *after*
    // the loop, which is usually a pointer to the end of the object (which
    // is OOB). We detect the pattern where the induction variable is
    // compared to a loop exit value before ever being dereferenced, and
    // ignore the last iteration in the distance calculation.
    //   TODO: it may be better to use evaluateAtIteration icw
    //   getBackedgeTakenCount instead of the phi step stuff (
    InductionDescriptor D;
    if (isNotDereferencedInLastLoopIteration(GEP, D)) {
      if (D.getConsecutiveDirection() == 1) {
        // i += step
        const SCEV *Step = SE->getConstant(D.getConstIntStepValue());
        Distance = SE->getAddExpr(Distance, Step);
      } else if (D.getConsecutiveDirection() == -1) {
        // i -= step
        // XXX: not sure what to do here, check the first iteration only?
      }
    }

    // For a GEP in an incrementing for-loop, we only need to check the
    // value after (or in, see above) the last iteration. Note that an
    // incrementing loop implies a decrementing distance, hence the
    // isKnownNegative check.
    // Similarly, we only look at the first iteration for decrementing
    // loops

    if (const SCEVAddRecExpr *AR = dyn_cast<const SCEVAddRecExpr>(Distance)) {
      if (SE->isKnownNegative(AR->getStepRecurrence(*SE))) {
        Distance = SE->getSCEVAtScope(AR, AR->getLoop()->getParentLoop());
      } else if (SE->isKnownPositive(AR->getStepRecurrence(*SE))) {
        // TODO: get value at first iteration
      }
    }

    // We need to statically prove that the distance is larger than the
    // maximum dereferenced number of bytes from this pointer. So, we
    // traverse the uses until we find dereferences (load/store/memset/etc)
    // and accumulate the dereferenced byte ranges for static bounds
    // checks by SCEV.
    if (!isNotDereferencedBeyonedNBytes(GEP, Distance))
      continue;
    setNoPropagation(GEP);
  }
}


void MPAvailable::setNoPropagation(GetElementPtrInst *GEP)
{
  SafeGEPs.insert(GEP);
  setSafeName(GEP);
}

bool MPAvailable::libCallReturnsSameObjectPointer(CallSite & CS, Value * Param) {
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
    if(LoadInst* LI = dyn_cast<LoadInst>(U)) { Derefs.push_back(LI); }
    else if(StoreInst* SI = dyn_cast<StoreInst>(U))
    {
      if (SI->getValueOperand() == GEP)
        return false;
      Derefs.push_back(LI);
    }
    else {
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

Value* MPAvailable::getComparedLoopExitValue(const Loop *L, Value *V,
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

bool MPAvailable::findAllDereferencedBytes(
    Value *Ptr, SmallVectorImpl<const SCEV *> &DerefBytes) {
  struct Entry {
    Value *I;
    Instruction *UI;
    const SCEV *Offset;
  };

  SmallVector<struct Entry, 8> Worklist;
  SmallPtrSet<PHINode *, 4> VisitedPHINodes;

  for (User *U : Ptr->users()) {
    ifcast(Instruction, UI, U) Worklist.push_back({Ptr, UI, nullptr});
  }

  while (!Worklist.empty()) {
    const struct Entry &E = Worklist.pop_back_val();
    const SCEV *UOffset = E.Offset;

    switch (E.UI->getOpcode()) {
    case Instruction::Load:
      // Add the number of bytes loaded, do not look at users
      DerefBytes.push_back(addSCEVs(E.Offset, getSizeOfSCEV(E.UI->getType())));
      continue;
    case Instruction::Store:
      // Give up tracking if the pointer value is stored in memory
      if (E.UI->getOperand(0) == E.I)
        return false;
      // Add the number of bytes stored
      DerefBytes.push_back(
          addSCEVs(E.Offset, getSizeOfSCEV(E.UI->getOperand(0)->getType())));
      continue;
    case Instruction::PHI:
      // Avoid recursing cyclic phi references
      if (VisitedPHINodes.count(cast<PHINode>(E.UI)))
        continue;
      VisitedPHINodes.insert(cast<PHINode>(E.UI));
      break;
    case Instruction::Call:
    case Instruction::Invoke:
      // TODO: support safe calls that do not dereference memory (use
      // targetlibinfo maybe?)
      return false;

      // TODO: MemIntrinsic

    case Instruction::GetElementPtr:
      // Break  on safe GEPs since they are already proven to only
      // dereference inbounds (fallthrough to the check otherwise)
      if (!needsPropagation(cast<GetElementPtrInst>(E.UI)))
        continue;
      /* fall through */
    default:
      if (const SCEV *PtrOffset = getPointerCastOrArithOffset(E.UI, E.I)) {
        if (PtrOffset->isZero()) {
          // Follow pointer casts
        } else {
          UOffset = addSCEVs(UOffset, PtrOffset);
        }
        break;
      }

      return false;
    }

    for (User *U : E.UI->users())
      Worklist.push_back({E.UI, cast<Instruction>(U), UOffset});
  }

  return true;
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

const SCEV *MPAvailable::getPointerCastOrArithOffset(Instruction *UI, Value *I) {
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
    SmallVector<const SCEV*, 3> Ops;

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

    //SCEV::NoWrapFlags Flags = ScalarEvolution::setFlags(SCEV::FlagNUW, SCEV::FlagNSW);
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



GetElementPtrInst * MPAvailable::getPreemptedOffset(GetElementPtrInst *GEP) {
  return PreemptedArithOffsets.lookup(GEP);
}

void MPAvailable::preemptBoundChecks(Function &F) {
    DenseMap<Value*, SmallVector<GetElementPtrInst*, 4>> BaseGEPs;
    SmallVector<SmallVector<GetElementPtrInst*, 4>, 4> Groups;

    //DEBUG_LINE("hi, preempt " << F.getName());

    for (BasicBlock &BB : F) {
        // TODO: also consider bitcasts, insert zero-geps in that case

        // We are looking for GEPs that are only used once by a load/store, in
        // the other in which they are dereferenced (so that we know which one
        // to move the check to when merging). Note that the GEPs need not
        // even be in the same basic block, we use dominator information later
        // on to move instructions necessary for offset calculation to the
        // first dereferemced GEP.
        BaseGEPs.clear();
        for (Instruction &I : BB) {
            GetElementPtrInst *GEP;
            ifcast(LoadInst, LI, &I)
                GEP = dyn_cast<GetElementPtrInst>(LI->getPointerOperand());
            else ifcast(StoreInst, SI, &I)
                GEP = dyn_cast<GetElementPtrInst>(SI->getPointerOperand());
            else
                continue;


            //GEP가 null 이거나, Use가 1개가 아니라면
            if (!GEP || GEP->getNumUses() != 1)
                continue;
            //GEP가 null 아니고, Use가 1개 일때만 ...
            // Skip already safe GEPs
            if (!needsPropagation(GEP))
                continue;

            Value *Base = GEP->getPointerOperand()->stripPointerCasts();
            BaseGEPs.FindAndConstruct(Base).second.push_back(GEP);
        }

        // For each base pointer, divide the GEPs into groups that can be
        // compared to each other
        for (auto it : BaseGEPs) {
            //Value *Base = it.first;
            SmallVectorImpl<GetElementPtrInst*> &GEPs = it.second;
            Groups.clear();

            //DEBUG_LINE("base: " << *it.first);

            // Append a GEP to the first group that has a member that has a
            // comparable SCEV
            for (GetElementPtrInst *GEP : GEPs) {
                //DEBUG_LINE(" gep:" << *GEP);
                //DEBUG_LINE(" scev: " << *SE->getSCEV(GEP));
                bool Found = false;

                unsigned i = 0;
                //why compare?
                for (SmallVectorImpl<GetElementPtrInst*> &Group : Groups) {
                    //DEBUG_LINE(" group " << i);
                    for (GetElementPtrInst *Other : Group) {
                        //DEBUG_LINE(" other scev: " << *SE->getSCEV(Other));
                        // It does not matter how the SCEVs compare, as long as
                        // they are comparable, so that we can find the maximum
                        // later
                        // FIXME: maybe we should just compare to the first
                        // element

                        // The earlier GEP should not be used in the offset
                        // calculation, not should its loaded value, since then
                        // the offset calculation can not be moved up.

                        // E.g.:
                        //   %other = gep %base, ...
                        //   %otheri = bitcast %other to i64
                        //   %off = sub %otheri, %base
                        //   %gep = gep %base, %off, ...
                        if (instUsesInst(GEP, Other))
                            continue;

                        // E.g.:
                        //   %other = gep %base, ...
                        //   %off = load %other
                        //   %gep = gep %base, %off, ...
                        ifcast(LoadInst, LI, getSingleUser<Instruction>(Other)) {
                            if (instUsesInst(GEP, LI))
                                continue;
                        }

                        // The instructions must be part of the same inner loop
                        // as well
                        BasicBlock *GEPB = GEP->getParent(), *OtherB = Other->getParent();
                        if (GEPB != OtherB && LI->getLoopFor(GEPB) != LI->getLoopFor(OtherB))
                            continue;

                        if (compareGEPs(ICmpInst::ICMP_SLE, GEP, Other) ||
                            compareGEPs(ICmpInst::ICMP_SGT, GEP, Other)) {
                            Group.push_back(GEP);
                            //DEBUG_LINE(" found");
                            Found = true;
                            // TODO: assert that rest of the group is also comparable?
                            break;
                        }
                    }
                    if (Found)
                        break;
                    i++;
                }

                // Create a new group if no existing group was comparable
                if (!Found) {
                    Groups.emplace_back(std::initializer_list<GetElementPtrInst*>{GEP});
                    //DEBUG_LINE(" new group");
                }
            }

            // At this point, all groups with > 1 members can be merged into
            // the first dereferenced (which is the first element of the group,
            // by order of processing)
            for (SmallVectorImpl<GetElementPtrInst*> &Group : Groups) {
                if (Group.size() < 2)
                    continue;

                // Find the GEP with the maximum offset
                GetElementPtrInst *CheckGEP = Group[0];
                GetElementPtrInst *MaxGEP = CheckGEP;

                for (auto I = std::next(Group.begin()), E = Group.end(); I != E; ++I) {
                    GetElementPtrInst *GEP = *I;
                    if (compareGEPs(ICmpInst::ICMP_SGT, GEP, MaxGEP))
                        MaxGEP = GEP;
                }

                // Inform deltatagsprop pass to copy the offset of the maximum
                // GEP to the first dereferenced GEP
                if (MaxGEP != CheckGEP) {
                    setPreemptedOffset(CheckGEP, MaxGEP);
                }

                // Tag all the other GEPs in the group as safe to avoid
                // instrumentation
                for (auto I = std::next(Group.begin()), E = Group.end(); I != E; ++I) {
                    GetElementPtrInst *GEP = *I;
                    setNoPropagation(GEP);
                    // TODO: also remove mask from load/store
                }
            }
        }
    }
}

bool MPAvailable::compareGEPs(ICmpInst::Predicate Pred, GetElementPtrInst *LHS,
                              GetElementPtrInst *RHS) {
  Value *BaseL = LHS->getPointerOperand()->stripPointerCasts();
  Value *BaseR = RHS->getPointerOperand()->stripPointerCasts();
  assert(BaseL == BaseR);

  const SCEV *OffsetL = getGEPOffsetSCEV(LHS);
  const SCEV *OffsetR = getGEPOffsetSCEV(RHS);

  eliminateCommonOperandsForComparison(OffsetL, OffsetR);

  return compareSCEVs(Pred, OffsetL, OffsetR);
}

bool MPAvailable::eliminateCommonOperandsForComparison(const SCEV *&A,
                                                      const SCEV *&B) {
  if (A->getSCEVType() != B->getSCEVType())
    return false;

  SCEVTypes Ty = static_cast<SCEVTypes>(A->getSCEVType());

  if (Ty == scAddExpr || Ty == scMulExpr) {
    const SCEVNAryExpr *AN = cast<SCEVNAryExpr>(A);
    const SCEVNAryExpr *BN = cast<SCEVNAryExpr>(B);

    // Only handle binary operators (sufficient for GEPs)
    if (AN->getNumOperands() != 2 || BN->getNumOperands() != 2)
      return false;

    if (AN->getOperand(0) == BN->getOperand(0)) {
      A = AN->getOperand(1);
      B = BN->getOperand(1);
    } else if (AN->getOperand(1) == BN->getOperand(1)) {
      A = AN->getOperand(0);
      B = BN->getOperand(0);
    } else if (AN->getOperand(0) == BN->getOperand(1)) {
      A = AN->getOperand(1);
      B = BN->getOperand(0);
    } else if (AN->getOperand(1) == BN->getOperand(0)) {
      A = AN->getOperand(0);
      B = BN->getOperand(1);
    } else {
      return false;
    }

    eliminateCommonOperandsForComparison(A, B);
    return true;
  } else if (Ty == scAddRecExpr) {
    const SCEVAddRecExpr *AAR = cast<SCEVAddRecExpr>(A);
    const SCEVAddRecExpr *BAR = cast<SCEVAddRecExpr>(B);

    // Only handle the form A*X+b (again targeting GEPs)
    if (!AAR->isAffine() || !BAR->isAffine())
      return false;

    // FIXME: how do we handle loops?
    // if (AAR->getStart() == BAR->getStart()) {
    //    A = SE->getAddRecExpr();
    //}
  } else
    ifcast(const SCEVCastExpr, AC, A) {
      const SCEVCastExpr *BC = cast<SCEVCastExpr>(B);

      if (AC->getType() != BC->getType())
        return false;

      const SCEV *OpA = AC->getOperand(), *OpB = BC->getOperand();
      if (!eliminateCommonOperandsForComparison(OpA, OpB))
        return false;

      switch (Ty) {
      case scSignExtend:
        A = SE->getSignExtendExpr(OpA, AC->getType());
        B = SE->getSignExtendExpr(OpB, BC->getType());
        break;
      case scZeroExtend:
        A = SE->getZeroExtendExpr(OpA, AC->getType());
        B = SE->getZeroExtendExpr(OpB, BC->getType());
        break;
      case scTruncate:
        A = SE->getTruncateExpr(OpA, AC->getType());
        B = SE->getTruncateExpr(OpB, BC->getType());
        break;
      default:
        break;
      }
    }

  return false;
}

void MPAvailable::setPreemptedOffset(GetElementPtrInst *CheckGEP,
        GetElementPtrInst *OffsetGEP) {
    assert(getPreemptedOffset(CheckGEP) == nullptr);
    PreemptedArithOffsets[CheckGEP] = OffsetGEP;

    if (CheckGEP->hasName() && OffsetGEP->hasName())
        CheckGEP->setName(CheckGEP->getName() + Twine(".offsetof.") + OffsetGEP->getName());
    else if (OffsetGEP->hasName())
        CheckGEP->setName(Twine("anon.offsetof.") + OffsetGEP->getName());
    else if (CheckGEP->hasName())
        CheckGEP->setName(CheckGEP->getName() + Twine(".offsetof.anon"));
    else
        CheckGEP->setName("anon.offsetof.anon");
}

void MPAvailable::allocation(Module& M){
  for(Function &F: M){
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
        valuePrint(si, "si:");
        handleStore(si);
        break;
      }
      case Instruction::Load: {
        LoadInst *li = dyn_cast<LoadInst>(&*vI);
        handleLoad(li);
        break;
      }
      }
    }
  }
}

void MPAvailable::allocOnFunction(Function& F){
  for(Instruction &I: instructions(F)){
    if(isAllocation(&I)) allocMPointer(I);
    
    if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
      Function *F = CallSite(&I).getCalledFunction();
      if (F && F->isDeclaration())
        continue;
    }

    // for (Use &U : I.operands()) {
    //   if(U.)
    //   if(!U.get()) continue;
    //   if (ConstantPointerNull *NullPtr = dyn_cast<ConstantPointerNull>(U.get())) {
    //     U.set(getNullPtr(NullPtr->getType()));
    //   }
    // }
  }
}

void MPAvailable::allocMPointer(Instruction& I){
  //base 태그 생성 테스트 끝
  //errs() << I << "\n";
  IRBuilder<> irb(getInsertPointAfter(&I));
  Value* ptr = dyn_cast<Value>(&I);//maskMallocWrapper(irb, I);

  if(isStackValue(&I)) return;

  Value *Size = instrumentWithByteSize(irb, &I, *DL);
  IntegerType *SizeTy = cast<IntegerType>(Size->getType());


  Value *OvSz = createOverMask(irb, Size);
  
  //Value *UnSz = irb.CreateShl(Size, 48);
  
  //Value *SizeMask = irb.CreateOr(OvSz, UnSz, "size.mask"); //여기를 고쳐야함
  
  //Value *SizeMask = createTag(irb, Size, "");
  //Value *SizeMask = irb.CreateShl(IsnvSz, BOUND_SHIFT);

  Value *PtrInt = irb.CreatePtrToInt(ptr, irb.getInt64Ty());
  Value *Tagged = irb.CreateOr(PtrInt, OvSz);
  Value *NewPtr = irb.CreateIntToPtr(Tagged, ptr->getType(),
                                   Twine(ptr->getName()) + ".tagged");
  TagPtrOrigin.insert(NewPtr);

  if(ptr->user_empty()) return;
  std::vector<User*> Users(ptr->user_begin(), ptr->user_end());
  for (User *U : Users){
    Instruction* comesAfter = dyn_cast<Instruction>(U);
    Instruction* comesBefore = dyn_cast<Instruction>(NewPtr);
    if(comesBefore->comesBefore(comesAfter)){ //Order < other->Order comesBefore < comesAfter
      U->replaceUsesOfWith(ptr, NewPtr); // 이부분이 old 포인터가 반드시 쓰여야 되는 지점것까지 교체함
      AllocMpUses.insert(comesAfter);
    }
  }
}

Value* MPAvailable::maskMallocWrapper(IRBuilder<>& B, Instruction& I){
  Value* ptr = dyn_cast<Value>(&I);
  
  if(!isHeapAlloc(I)) return ptr;
  std::vector<User*> Users(ptr->user_begin(), ptr->user_end());

  std::string Prefix = ptr->hasName() ? ptr->getName().str() + "." : "";

  Value *PtrInt =
      B.CreatePtrToInt(ptr, Type::getInt64Ty(ptr->getContext()), Prefix + "int");
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

void MPAvailable::memAccess(Instruction& I){

}

void MPAvailable::propagateTagMem(Function& F){
  for(Instruction& I: instructions(F)){
    Value* v = dyn_cast<Value>(&I);
    std::vector<User*> Users(v->user_begin(), v->user_end());

    if(TagPtrOrigin.count(v)){
      for(User *u: Users){ 
        Instruction* useInst = dyn_cast<Instruction>(u);
        handleUse(*useInst);
      }
    }

  }
}
void MPAvailable::handleUse(Instruction &I) {
  switch (I.getOpcode()) {
  case Instruction::Store:
  case Instruction::Load: {
    unwrapTag(I);
    break;
  }
  case Instruction::Sub:
  case Instruction::Add:
    break;
  }
}

void MPAvailable::unwrapTag(Instruction& I){
  IRBuilder<> irb(getInsertPointAfter(&I));
  Value* ptr = dyn_cast<Value>(&I);
  Value* PtrInt = irb.CreatePtrToInt(ptr, irb.getInt64Ty());
  Value* TagCleaner = irb.CreateAnd(PtrInt, TAG_CLEAN_BIT);
  Value* NewPtr = irb.CreateIntToPtr(TagCleaner, ptr->getType()); 
}

void MPAvailable::handleGEP(GetElementPtrInst* gep, IRBuilder<>& irb, std::string prefix){
  GetElementPtrInst *PreemptedGep = nullptr;

  if (!gep)
    return;
 
  Value* base = gep->getPointerOperand()->stripPointerCasts();
  valuePrint(base, "base");
  if (!gep) return;
  if (gep->getType()->isVectorTy()) return ;
  std::vector<User *> Users(gep->user_begin(), gep->user_end());
  
  Value *Diff;
  ConstantInt *ConstOffset = nullptr;
  APInt ConstOffsetVal(64, 0);
  IntegerType *PtrIntTy = getPtrIntTy(gep->getContext());
  std::string Prefix = std::string(base->getName())+"."+prefix+".array.";

  Instruction *PtrInt =
      cast<Instruction>(irb.CreatePtrToInt(base, PtrIntTy, Prefix + "int"));

  if (gep->accumulateConstantOffset(*DL, ConstOffsetVal))
    ConstOffset = irb.getInt(ConstOffsetVal);

  //결국 이 PreemptedOffset의 용도는 필요없기 때문에 그에 맞게 바꿔줘야됨
  //삭제함
  if(ConstOffset){
    Diff = ConstOffset;
  }
  else{
    Diff = EmitGEPOffset(&irb, *DL, PreemptedGep);
  }
  //DIFF가 더해진 오프셋
  //create tag 
  //tag 만드는 함수로 대체 예정
  // Value *UnderOffset = irb.CreateShl(Diff, 56, Prefix+"UnderOffset");
  // Value *OverOffset = irb.CreateShl(Diff, 48, Prefix+"OverOffset");
  // Value *Shifted = irb.CreateAnd(UnderOffset, OverOffset, Prefix + "shifted");

  errs()<< "Diff: ";
  Diff->print(errs());
  errs()<<"\n";


  Value* Shifted = createTag(irb, Diff);

  Value *AddOffset = Shifted;
  Value *PtrAdd;
  Constant *ZeroPtr = irb.getIntN(64, 0);

  PtrAdd = irb.CreateAdd(PtrInt, AddOffset, Prefix + "added");
  //이부분이 offset 만들고 조정함
  if(hasNegativeOffset(gep)){
    //diff negation 한 다음에, 이걸로 shift하고, 그다음에 이걸 보수한다
    Value* neg = irb.CreateNeg(Diff);
    valuePrint(neg, "neg");
    Shifted = createTag(irb, neg);
    AddOffset = irb.CreateNeg(Shifted);
    // Value *Zero = ConstantInt::get(PtrIntTy, 0);
    // Value *Mask = ConstantInt::get(PtrIntTy, getAddressSpaceMask());
    // Value *OrigPtrInt =
    //     irb.CreatePtrToInt(gep->getOperand(0), PtrIntTy, Prefix + "origptrint");
    // Value *HasMeta = irb.CreateICmpUGT(OrigPtrInt, Mask, Prefix + "hasmeta"); // 값비교  UGT : unsigned greater than >
    // AddOffset = irb.CreateSelect(HasMeta, Shifted, Zero, Prefix + "offset");  //분기없이 HasMeta 값에 Shifted인지 Zero인지 선택 메타데이터값을 갖고 있으면 Shifted 아니면 zero를 채워넣음
    PtrAdd = irb.CreateAdd(PtrInt, AddOffset, Prefix + "sub");
  } else {
    PtrAdd = irb.CreateAdd(PtrInt, AddOffset, Prefix + "added");
  }
  Value *NewPtr = irb.CreateIntToPtr(PtrAdd, gep->getType(), Prefix + "newptr");

  
  gep->replaceAllUsesWith(NewPtr); // 왜 지워지는지 암, 그 이유는 gep를 통해 NewPtr이 만들어지는데 gep가 사라지기 때문, 그래서 gep대신에 원래의 포인터로 NewPtr을 만들어야됨
  //gep->removeFromParent();
  gep->eraseFromParent();
  // for (User *U : Users)
  //   U->replaceUsesOfWith(gep, NewPtr);
}

bool MPAvailable::hasNegativeOffset(GetElementPtrInst* gep){
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

void MPAvailable::handleStore(StoreInst* si){
  //GEP 없이 LOAD -> STORE 하는 패턴이 있음, 그 경우에 대한 대처가 필요함
  valuePrint(si, "si: ");
  Value *newPtr;
  Value *clearTagPointer;
  Value *replaceInst;

  GetElementPtrInst* gep;
  gep = dyn_cast<GetElementPtrInst>(si->getPointerOperand());
  if(!gep){
    gep = dyn_cast<GetElementPtrInst>(si->getValueOperand());
  }

  if (!gep) {
    //LOAD -> STORE without GEP, this is the case, only clear.
    IRBuilder<> irb(getInsertPointAfter(si));
    newPtr = si->getPointerOperand();
    typePrint(si->getOperand(1)->getType(), "ptr_ type");
    clearTagPointer = getClearTagPointer(irb, newPtr);
    replaceInst = irb.CreateStore(si->getValueOperand(), clearTagPointer);
    si->replaceAllUsesWith(replaceInst);
    si->eraseFromParent(); // For use this statement for debug, annotate this.
                           // Don't remove it!
    return;
  }

  IRBuilder<> irb(getInsertPointAfter(gep));

  handleGEP(gep, irb, "store");

  if (!dyn_cast<AllocaInst>(si->getOperand(1))) {
    //allocainst인 경우 포인터를 저장하기 위한 변수이므로 태그 클리어 과정이 필요없음
    newPtr = si->getPointerOperand();
    typePrint(si->getOperand(1)->getType(), "ptr_ type");
    clearTagPointer = getClearTagPointer(irb, newPtr);
    replaceInst = irb.CreateStore(si->getValueOperand(), clearTagPointer);
    si->replaceAllUsesWith(replaceInst);
    si->eraseFromParent(); // For use this statement for debug, annotate this.
                           // Don't remove it!
  }
}

void MPAvailable::handleLoad(LoadInst* li){
  //LOAD->LOAD하는 패턴도 있음
  GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(li->getPointerOperand());
  Value *newPtr;
  Value *clearTagPointer;
  Value *replaceInst;
  if (!gep) {
    //변수로 부터 load한거면 클리어할 필요 없음
    //변수가 아니다? 그럼 무조건 클리어
    if (isa<AllocaInst>(li->getPointerOperand())) return;
    IRBuilder<> irb(getInsertPointAfter(li));
    newPtr = li->getPointerOperand();
    clearTagPointer = getClearTagPointer(irb, newPtr);
    replaceInst = irb.CreateLoad(clearTagPointer, "clear.bit");
    li->replaceAllUsesWith(replaceInst);
    li->eraseFromParent();
    return;
  }

  IRBuilder<> irb(getInsertPointAfter(gep));
  handleGEP(gep, irb, "load");

  newPtr = li->getPointerOperand();
  clearTagPointer = getClearTagPointer(irb, newPtr);
  replaceInst = irb.CreateLoad(clearTagPointer, "clear.bit");
  li->replaceAllUsesWith(replaceInst);
  li->eraseFromParent(); // For use this statement for debug, annotate this.
                        // Don't remove it!
}

void MPAvailable::initFunction(Module& M){
  Type *PtrIntTy = getPtrIntTy(M.getContext());
  AddWithOverflowFunc =
      Intrinsic::getDeclaration(&M, Intrinsic::uadd_with_overflow, PtrIntTy);
}
static RegisterPass<MPAvailable> MPAVAILABLE("mpav", "MPAvailable");