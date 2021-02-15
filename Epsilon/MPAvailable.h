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

//#include "llvm-sra/SRA/SymbolicRangeAnalysis.h"
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


private:
  DenseSet<Value *> SafeAllocations;
  DenseSet<GetElementPtrInst *> SafeGEPs;
  DenseSet<std::pair<Instruction *, Value *>> SafeMaskSites;
  DenseMap<GetElementPtrInst *, GetElementPtrInst *> PreemptedArithOffsets;
  DenseSet<Value* > TagPtrOrigin;
  DenseSet<Instruction *> AllocMpUses;
  DenseSet<Instruction *> NonAllocMp;


  const DataLayout* DL;
  ScalarEvolution *SE;
  DominatorTree *DT;
  LoopInfo *LI;
  //SymbolicRangeAnalysis *SRA;

  Function* AddWithOverflowFunc;

  void getAnalysisUsage(AnalysisUsage &AU) const override;


  void propagateAllocationBounds(Function &F, DenseMap<Value *, const SCEV *> &PointerBounds);

  bool libCallReturnsSameObjectPointer(CallSite &CS, Value *Param);
  bool isNotDereferencedInLastLoopIteration(GetElementPtrInst *GEP, InductionDescriptor &D);
  Value *getComparedLoopExitValue(const Loop *L, Value *V, BranchInst *&Br);


  bool isInnerTagPossible(Value* size);

  const SCEV *getSizeOfSCEV(Type *Ty);
  const SCEV *addSCEVs(const SCEV *LHS, const SCEV *RHS) ;
  const SCEV *getPointerCastOrArithOffset(Instruction *UI, Value *I);
  const SCEV *getGEPOffsetSCEV(GetElementPtrInst *GEP, bool NoWrap = false);
  const SCEV *addNoWrapFlags(const SCEV *V);

  void allocation(Module& M);
  void allocOnFunction(Function& F);

  void allocMPointer(Instruction& I, ScalarEvolution* SE);
  Value* maskMallocWrapper(IRBuilder<> &B, Instruction& I);
  Constant *getNullPtr(PointerType *Ty) ;

  void propagateGEP(Module& M);
  void handleGEP(GetElementPtrInst* gep, IRBuilder<>& irb, std::string prefix);
  void handleStore(StoreInst* si);
  void handleLoad(LoadInst* li);
  bool hasNegativeOffset(GetElementPtrInst* gep);
  void isInnerTagAnalysis(Function& F);

  void propagateTagModule(Module& M);
  void propagateTAg(Function& F);

  void initFunction(Module& M);

  class EPTagAnalysis
  {
  public:
    EPTagAnalysis(Function *inF, DenseSet<Instruction *> inAllocEPSet, DenseSet<Instruction *> &inNonAllocEPSet): F(inF), AllocEPSet(inAllocEPSet), NonAllocEPSet(inNonAllocEPSet){
      init();
    }
    DenseSet<Instruction *>& AllocEPSet;
    DenseSet<Instruction *>& NonAllocEPSet;
    enum EPTag
    {
      NONP,
      NONEP,
      EP,
      UNKNOWN,
      NOINT
    };
    void runOnFunction();
    bool checkMP(Instruction* I);
  private:
    Function *F;
    //Remeber! std::set cannot be pointer
    DenseMap<Instruction *, std::set<EPTag>> TagSet;
    void init();
    void setUnion(Value* src, Value* dst, bool& isChanged);
    bool isEqual(DenseMap<Instruction *, std::set<EPTag>>& oldState, DenseMap<Instruction *, std::set<EPTag>>& newState);
    void printState();
  };
};


