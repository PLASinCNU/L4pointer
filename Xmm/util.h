#ifndef M_UTIL
#define M_UTIL

#include <llvm/Analysis/ConstantFolding.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/IR/CallSite.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>

#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"

#define ifncast(ty, var, val)  \
  ty *var = dyn_cast<ty>(val); \
  if (var == nullptr)
#define ifcast(ty, var, val) if (ty *var = dyn_cast<ty>(val))
#define foreach_func_inst(fn, var)                                       \
  for (inst_iterator _II = inst_begin(fn), _E = inst_end(fn); _II != _E; \
       ++_II)                                                            \
    if (Instruction *var = &*_II)

#define foreach(ty, var, arr) \
  for (auto *_I : (arr))      \
    if (ty *var = cast<ty>(_I))

using namespace llvm;
enum AllocationType { Malloc, Calloc, Realloc, Alloca, AllocaNone };
enum Possibility { No, Yes, Maybe };

void deleteFunction(Function *F);
bool isFunctionPtrPtrTy(Type *type);
void traceUses(Function *F);
bool isHeapAllocation(CallSite &CS);
bool isHeapAlloc(Instruction &I);
bool isMalloc(Function *F);
bool isCalloc(Function *F);
bool isRealloc(Function *F);
bool isFree(Function *F);
bool isMallocWrapper(Function *F);
bool isCallocWrapper(Function *F);
bool isReallocWrapper(Function *F);
bool isFreeWrapper(Function *F);
bool isAllocationFunc(Function *F);
bool isFreeFunc(Function *F);
bool isAllocation(Instruction *I);
bool isStackValue(Instruction *I);
Value *createMask(IRBuilder<> &irb, Value *size, LLVMContext &ctx);
Value *getClearTagPointer(IRBuilder<> &irb, Value *MAllocP,
                          std::string prefix = "");
void valuePrint(Value *value, std::string prefix);
void typePrint(Type *type, std::string prefix);
void instPrint(Instruction *inst, std::string prefix);
bool isAllUseSelf(Function *F);
bool isUsedFunctionPointer(Function *F);
void deleteFunctionInst(Function &F);
bool isExternalStruct(std::string name);
bool isFunctionPtrTy(Type *type);
bool isI128TypeEqual(Type *type1);
bool isMalloc(Instruction *I);
bool isRealloc(Instruction *I);
Constant *createConstantMask(Value *size, LLVMContext &ctx);
enum LibPtr {
  None,
  Ignore,
  CopyFromArg,
  PtrDiff,
  RetSizeStatic,
  Strlen,
  Strtok,
};

enum LibPtr getLibPtrType(Function *F, int *dat);

inline Value *otherOperand(Instruction *I, Value *Op) {
  assert(I->getNumOperands() == 2);

  if (I->getOperand(0) == Op) return I->getOperand(1);

  assert(I->getOperand(1) == Op);
  return I->getOperand(0);
}

unsigned long long getAddressSpaceMask(bool overflowbit = false);
Instruction *getInsertPointBefore(Instruction *I);
Instruction *getInsertPointAfter(Instruction *I);
AllocationType getCallType(Instruction *I);

const SCEV *getSizeSCEV(Instruction *I, ScalarEvolution &SE);
Value *instrumentWithByteSize(IRBuilder<> &B, Instruction *I,
                              const DataLayout &DL, AllocationType CallType);
Value *instrumentWithByteSize(IRBuilder<> &B, Instruction *I,
                              const DataLayout &DL);
const SCEV *getGlobalSizeSCEV(GlobalVariable *GV, ScalarEvolution &SE);
static bool instUsesInst(Instruction *I, Instruction *Needle) {
  SmallVector<Instruction *, 8> Worklist;
  SmallPtrSet<Instruction *, 8> Visited;
  Worklist.push_back(I);

  do {
    I = Worklist.pop_back_val();

    if (I == Needle) return true;

    if (!Visited.insert(I).second) continue;

    for (Use &U : I->operands()) {
      ifcast(Instruction, UI, U.get()) Worklist.push_back(UI);
    }
  } while (!Worklist.empty());

  return false;
}

int getSizeArg(Instruction *I);
int getSizeArg(Function *F);
void collectPHIOrigins(PHINode *PN, std::vector<Value *> &Origins);

inline llvm::IntegerType *getPtrIntTy(llvm::LLVMContext &C) {
  return llvm::Type::getIntNTy(C, 64);
}

template <typename T = User>
inline T *getSingleUser(Value *V) {
  assert(V->getNumUses() == 1);
  return cast<T>(*V->user_begin());
}

#endif