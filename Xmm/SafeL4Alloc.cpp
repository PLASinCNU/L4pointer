#include "SafeL4Alloc.h"

static void registerSafeAllocPass(const PassManagerBuilder&,
                                  legacy::PassManagerBase& PM) {
  PM.add(new SafeL4Alloc());
}

bool SafeL4Alloc::runOnModule(Module& M) {
  for (Function& F : M) {
    runOnFunction(F);
  }
  return false;
}

bool SafeL4Alloc::runOnFunction(Function& F) {
  std::set<Instruction*> before;
  std::set<Instruction*> L4Candidates;
  bool changed = true;
  while (changed) {
    before = L4Candidates;
    for (Instruction& I : instructions(F)) {
      switch (I.getOpcode()) {
        case Instruction::Alloca: {
          AllocaInst* ai = dyn_cast<AllocaInst>(&I);
          if (!isFunctionPtrTy(ai->getAllocatedType())) break;
          if (ai->getAllocatedType()->isPointerTy()) {
            L4Candidates.insert(&I);
            for (Value* use : ai->users()) {
              if (Instruction* useInst = dyn_cast<Instruction>(use))
                L4Candidates.insert(useInst);
            }
          }
          break;
        }
        case Instruction::Store:
        case Instruction::Load: {
          // Store instruction is not used;
          // Load 하면 그 값은 포인터가 아니기 때문에 use 볼 필요 없음(double
          // pointer X)
          // double pointer는 L4의 영역이 아님
          if (L4Candidates.count(&I) > 0) break;
          Value* op2 = I.getOperand(1);
          if (Instruction* op2Inst = dyn_cast<Instruction>(op2)) {
            if (L4Candidates.count(op2Inst)) {
              L4Candidates.insert(&I);
            }
          }
          break;
        }
        case Instruction::Call: {
          if (isAllocation(&I)) {
            if (isMalloc(&I)) {
              L4Candidates.insert(&I);
              for (User* use : I.users()) {
                if (Instruction* useInst = dyn_cast<Instruction>(use)) {
                  if (StoreInst* si = dyn_cast<StoreInst>(useInst)) {
                    if (L4Candidates.count(si) > 0) {
                      mallocL4s.insert(si);
                    }
                  }
                  if (BitCastInst* bci = dyn_cast<BitCastInst>(useInst)) {
                    for (User* use : bci->users()) {
                      if (StoreInst* si = dyn_cast<StoreInst>(use)) {
                        if (L4Candidates.count(si) > 0) {
                          mallocL4s.insert(si);
                          mallocL4s.insert(bci);
                        }
                      }
                    }
                  }
                }
              }
            } else if (isRealloc(&I)) {
              CallInst* CI = dyn_cast<CallInst>(&I);
              Value* arg0 = CI->getArgOperand(0);
              if (Instruction* argInst = dyn_cast<Instruction>(arg0)) {
                if (L4Candidates.count(argInst) > 0) {
                  L4Candidates.insert(CI);
                }
              }
            }
          } else {
            CallInst* CI = dyn_cast<CallInst>(&I);
            for (unsigned int i = 0; i < CI->getNumArgOperands(); i++) {
              if (Instruction* argInst =
                      dyn_cast<Instruction>(CI->getArgOperand(i))) {
                if (L4Candidates.count(argInst) > 0) L4Candidates.insert(&I);
              }
            }
          }
          break;
        }
        case Instruction::GetElementPtr: {
          GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(&I);

          Value* ptr = gep->getPointerOperand();
          if (Instruction* ptrInst = dyn_cast<Instruction>(ptr)) {
            if (L4Candidates.count(ptrInst) > 0) {
              L4Candidates.insert(&I);
              for (Value* use : I.users()) {
                if (Instruction* useInst = dyn_cast<Instruction>(use))
                  L4Candidates.insert(useInst);
              }
              break;
            }
          }
          break;
        }
        case Instruction::PtrToInt:
        case Instruction::BitCast: {
          // 이 두 인스트럭션에서 L4를 --> ptr로 바꾸기
          Value* op = I.getOperand(0);
          if (Instruction* opInst = dyn_cast<Instruction>(op)) {
            if (L4Candidates.count(opInst) > 0) {
              L4Candidates.insert(&I);
              break;
            }
          }
          break;
        }
        default: {
          break;
        }
      }
    }
    if (before == L4Candidates) changed = false;
  }
  results[&F] = L4Candidates;
  return false;
}

bool SafeL4Alloc::isChanged(std::set<Instruction*>& aSet,
                            std::set<Instruction*>& bSet) {
  if (aSet.size() != bSet.size()) return false;
  for (Instruction* aInst : aSet) {
    if (bSet.count(aInst) == 0) return false;
  }
  return true;
}

bool SafeL4Alloc::isPtrToL4(Instruction& I) {
  // I should be Load or Store,
  if (results.count(I.getParent()->getParent()) == 0) return false;
  std::set<Instruction*> L4s = results[I.getParent()->getParent()];
  if (isa<StoreInst>(&I)) {
    Value* val = I.getOperand(0);
    Value* ptr = I.getOperand(1);
    if (Instruction* ptrInst = dyn_cast<Instruction>(ptr)) {
      if (L4s.count(ptrInst) > 0) {
        if (Instruction* valInst = dyn_cast<Instruction>(val)) {
          if (L4s.count(valInst) > 0)
            return false;
          else
            return true;
        } else
          return true;
      }
    } else
      return false;
  }
  return false;
}
bool SafeL4Alloc::isL4ToPtr(Instruction& I) {
  // L4 type will be saved as Ptr at I;
  if (results.count(I.getParent()->getParent()) == 0) return false;
  std::set<Instruction*> L4s = results[I.getParent()->getParent()];
  if (isa<StoreInst>(&I)) {
    Value* val = I.getOperand(0);
    Value* ptr = I.getOperand(1);
    if (Instruction* ptrInst = dyn_cast<Instruction>(ptr)) {
      if (L4s.count(ptrInst) > 0) return false;
      if (Instruction* valInst = dyn_cast<Instruction>(val)) {
        if (L4s.count(valInst)) return true;
      }
    }
    return false;
  }
}

bool SafeL4Alloc::isStructGEP(Instruction& I) {
  if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(&I)) {
    if (gep->getType() != gep->getPointerOperand()->getType()) return true;
  }
  return false;
}

bool SafeL4Alloc::isMallocL4(Instruction& I) { return mallocL4s.count(&I) > 0; }

static RegisterPass<SafeL4Alloc> SAFEL4ALLOC("safel4", "SafeL4Alloc");