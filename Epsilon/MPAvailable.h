#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ScalarEvolutionExpander.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/ADT/TinyPtrVector.h>
#include <llvm/IR/NoFolder.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>

#include <initializer_list>
#include <llvm/IR/Value.h>
#include <llvm/Transforms/Utils/LoopUtils.h>

#include "AddressSpace.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "util.h"

using namespace llvm;

static void setSafeName(Value *V);

class MPAvailable : public ModulePass {
//to avoid tagging
public:
  static char ID;
  MPAvailable() : ModulePass(ID) {}

  virtual bool runOnModule(Module &M) override;
  bool needsTag(Value *Alloacation);
  bool needsMask(Instruction *I, Value *Operand);
  bool needsPropagation(GetElementPtrInst *GEP);
  inline bool hasTag(Value *Ptr){ return needsTag(Ptr);}
  inline bool needsPropagation(Instruction* I){
    return hasTag(I);
  }
  GetElementPtrInst *getPreemptedOffset(GetElementPtrInst *GEP);

private:
  DenseSet<Value *> SafeAllocations;
  DenseSet<GetElementPtrInst *> SafeGEPs;
  DenseSet<std::pair<Instruction *, Value *>> SafeMaskSites;
  DenseMap<GetElementPtrInst *, GetElementPtrInst *> PreemptedArithOffsets;
  DenseSet<Value* > TagPtrOrigin;
  DenseSet<Instruction *> AllocMpUses;


  const DataLayout* DL;
  ScalarEvolution *SE;
  DominatorTree *DT;
  LoopInfo *LI;

  Function* AddWithOverflowFunc;

  void getAnalysisUsage(AnalysisUsage &AU) const override;

  virtual void findSafeAllocations(Function &F);
  virtual bool isNotDereferencedBeyonedNBytes(Value *Ptr, const SCEV *DistanceToEndOfObject);
  virtual void setTag(Value *Allocation);
  virtual void setMaskSite(Instruction *I, Value *Operand);
  virtual void propagateSafeTags();
  virtual bool compareSCEVs(ICmpInst::Predicate Pred, const SCEV *LHS, const SCEV *RHS);
  virtual bool compareSCEVs(ICmpInst::Predicate Pred, Value *LHS, Value *RHS);
  void findSafeGEPs(Function &F, DenseMap<Value*, const SCEV*> &PointerBounds);
  void setNoPropagation(GetElementPtrInst *GEP);
  void propagateAllocationBounds(Function &F, DenseMap<Value *, const SCEV *> &PointerBounds);
  void preemptBoundChecks(Function &F);

  bool libCallReturnsSameObjectPointer(CallSite &CS, Value *Param);
  bool isNotDereferencedInLastLoopIteration(GetElementPtrInst *GEP, InductionDescriptor &D);
  Value *getComparedLoopExitValue(const Loop *L, Value *V, BranchInst *&Br);
  bool findAllDereferencedBytes(Value *Ptr,
                                SmallVectorImpl<const SCEV *> &DerefBytes);
  const SCEV *getSizeOfSCEV(Type *Ty);
  const SCEV *addSCEVs(const SCEV *LHS, const SCEV *RHS) ;
  const SCEV *getPointerCastOrArithOffset(Instruction *UI, Value *I);
  const SCEV *getGEPOffsetSCEV(GetElementPtrInst *GEP, bool NoWrap = false);
  const SCEV *addNoWrapFlags(const SCEV *V);

  bool compareGEPs(ICmpInst::Predicate Pred, GetElementPtrInst *LHS,
                   GetElementPtrInst *RHS);

  bool eliminateCommonOperandsForComparison(const SCEV *&A, const SCEV *&B);

  void setPreemptedOffset(GetElementPtrInst *CheckGEP,
                                       GetElementPtrInst *OffsetGEP);

  void allocation(Module& M);
  void allocOnFunction(Function& F);

  void allocMPointer(Instruction& I);
  Value* maskMallocWrapper(IRBuilder<> &B, Instruction& I);
  Constant *getNullPtr(PointerType *Ty) ;

  void memAccess(Instruction& I);
  void propagateTagMem(Function& F);
  void handleUse(Instruction& I);
  void unwrapTag(Instruction& I);

  void propagateGEP(Module& M);
  void handleGEP(GetElementPtrInst* gep, IRBuilder<>& irb, std::string prefix);
  void handleStore(StoreInst* si);
  void handleLoad(LoadInst* li);
  bool hasNegativeOffset(GetElementPtrInst* gep);

  void initFunction(Module& M);
};


