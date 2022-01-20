#include <llvm/ADT/TinyPtrVector.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ScalarEvolutionExpander.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/NoFolder.h>
#include <llvm/IR/Value.h>
#include <llvm/Transforms/Utils/LoopUtils.h>

#include <initializer_list>
#include <map>

//#include "llvm-sra/SRA/SymbolicRangeAnalysis.h"
#include <llvm/IR/InstIterator.h>

#include "AddressSpace.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "util.h"

using namespace llvm;

static Constant* cloneConstantExpr(ConstantExpr* cExpr);
class SafeL4Alloc : public ModulePass {
 public:
  static char ID;
  SafeL4Alloc() : ModulePass(ID) {}

  virtual bool runOnModule(Module& M) override;

  std::set<Instruction*>& getL4AllocsInFunction(Function& F) {
    return results[&F];
  }
  bool isPtrToL4(Instruction& I);
  bool isL4ToPtr(Instruction& I);
  bool isStructGEP(Instruction& I);
  bool isMallocL4(Instruction& I);

 private:
  std::map<Function*, std::set<Instruction*>> results;
  std::set<Instruction*> mallocL4s;
  bool runOnFunction(Function& F);
  bool isChanged(std::set<Instruction*>& aSet, std::set<Instruction*>& bSet);
};