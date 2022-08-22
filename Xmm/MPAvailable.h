#include <llvm/ADT/DenseMap.h>
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
#include "AddressSpace.h"
#include "SafeL4Alloc.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "util.h"

using namespace llvm;

static Constant* cloneConstantExpr(ConstantExpr* cExpr);
class MPAvailable : public ModulePass {
  // to avoid tagging
 public:
  static char ID;
  MPAvailable() : ModulePass(ID) {}

  virtual bool runOnModule(Module& M) override;

 private:
  DenseMap<GetElementPtrInst*, GetElementPtrInst*> PreemptedArithOffsets;
  DenseMap<AllocaInst*, AllocaInst*> ptrToXMM;
  DenseMap<AllocaInst*, Type*> xmmToType;
  DenseMap<GlobalVariable*, GlobalVariable*> gToGV;
  DenseMap<Value*, Type*> valueToType;  // Use를 통해서 type을 바꾸어주자
  DenseMap<GetElementPtrInst*, Value*> gepToValue;  // offset 계산을 위함
  DenseMap<GetElementPtrInst*, ConstantInt*>
      gepToOffset;  // offset이 constant로 나올 경우

  DenseMap<StructType*, StructType*> strucTyToStructTy;
  DenseMap<GetElementPtrInst*, bool> gepToPositive;
  DenseMap<Function*, Function*> funcToFunc;
  DenseSet<Value*> TagPtrOrigin;
  DenseSet<CallInst*> doublePtrMallocs;
  DenseSet<Instruction*> AllocMpUses;
  DenseSet<Instruction*> NonAllocMp;
  DenseSet<Instruction*> willBeRemoveSet;
  DenseSet<Instruction*> replaceInst;
  DenseSet<Value*> allocaGEPSet;
  DenseSet<Value*> xmmLoadSet;
  DenseSet<Function*> usedFunctionPointer;

  DenseSet<Function*> transformFunctions;
  DenseSet<Function*> wrappingFunctions;
  DenseSet<Function*> willBeDeletedFunctions;
  DenseSet<Function*> usedFunctions;
  DenseSet<ConstantExpr*> checks;

  DenseSet<Instruction*>
      continueList;  // 내가 추가하는 모든 instruction을 여기 추가하기,
                     // 내가 추가하는 instruction 은 건들지 못하게.... ex)
                     // handleLoad로 추가한 instruction 을 handleGEP에서 건들지
                     // 않기

  Module* module;

  const DataLayout* DL;
  ScalarEvolution* SE;
  DominatorTree* DT;
  LoopInfo* LI;
  SafeL4Alloc* L4Alloc;
  VectorType* XMM;
  PointerType* XMM_POINTER;
  Constant* constantNullXMM;
  // SymbolicRangeAnalysis *SRA;

  Function* AddWithOverflowFunc;
  FunctionCallee printFunction;

  void transformAlloc(Function& F);
  bool isXMMPtrTy(Type* type);
  void getAnalysisUsage(AnalysisUsage& AU) const override;
  void findDoublePtrMalloc(Function& F);
  void createXmmStructTy(Module& M);
  BasicBlock* cloneBB(Function* cloneFunc, BasicBlock* orig,
                      std::map<StringRef, int>& argToArg,
                      std::map<Value*, Value*>& valToVal,
                      std::map<Value*, Value*>& arrToPtr);

  void replaceStructTy(Module& M);  //  이 함수에서는 그냥 struct 타입에
  // 대해서만 바꿔줌, 그리고 gep 쪼개기 void replaceStructTyInFunction(Function&
  // F ); //  이 함수에서는 그냥 struct 타입에 대해서만 바꿔줌, 그리고 gep
  // 쪼개기
  void replaceStructTyInFunction(Function& F);
  std::set<StructType*> transStructs;

  StructType* createStructureType(StructType* st);
  void replaceFunction(Function* newFunc, Function* oldFunc);
  void eraseFunction(Function* function);
  void eraseRemoveInstruction();
  void createGlobalValue();
  void createWrappingFunction(Function& F);
  void declareWrappingFunction(Function& F);
  void createWrappingMain(Function& F);
  Value* createL4Ptr(Value* ptr, IRBuilder<>& irb);

  Instruction* handleAlloca(AllocaInst* alloca, IRBuilder<>& irb);

  void verifyFunctionType(FunctionType* FTy, ArrayRef<Value*> array);
  bool isInnerTagPossible(Value* size);
  Value* createOffsetMask(IRBuilder<>& irb, Value* offset);

  void allocation(Module& M);
  void allocOnFunction(Function& F);

  void allocEpsilon(Instruction& I, ScalarEvolution* SE);
  void l4Alloc(Instruction& I, ScalarEvolution* SE, IRBuilder<>& irb);
  Constant* getNullPtr(PointerType* Ty);

  void propagateGEP(Module& M);
  void handleGEP(GetElementPtrInst* gep);
  void handleStore(StoreInst* si);
  void handleLoad(LoadInst* li);
  void handleIcmp(ICmpInst* iCmpI);
  void debugBCI(BitCastInst* bci);
  bool hasNegativeOffset(GetElementPtrInst* gep);
  void isInnerTagAnalysis(Function& F);

  void propagateTagModule(Module& M);
  void propagateTAg(Function& F);
  FunctionType* createFunctionType(FunctionType* ft);
  void verifyModule(Module& M);
  std::vector<Value*> getCallArgs(CallInst* CI, FunctionType* ft,
                                  std::map<Value*, Value*>& valToVal,
                                  IRBuilder<>& irb);
  void initFunction(Module& M);
  bool fixParamAllocInst(Instruction& I, std::map<Value*, Value*>& valToVal,
                         IRBuilder<>& irb, bool isNeededNewInst = false);
  bool fixGEPforStruct(GetElementPtrInst* gep,
                       std::map<Value*, Value*>& valToVal, IRBuilder<>& irb,
                       bool needReplace = false);
  void transFormation(Function* F);

  void transFunction(Module& M);
  void transformFunction(Function* F);

  void replaceAll(Value* orig, Value* replacer);

  void analyzeGEPforFunction(Function& F);
  void verifyGlobalValue(Module& M);

  // if CalledFunction is declared, pointer should be unwrapped
  // 이렇게 하는 이유 printf 같은 가변인자를 가지는 함수때문에
  DenseMap<CallInst*, std::list<Type*>> infoCallArguType;
  void analyzeCall(CallInst* CI);
  void handleCall(CallInst* CI);
  //해제된 포인터는 플래그 세팅해놓기
  void handleFree(CallInst* CI);

  Value* clearTag_1(Value* xmmPtr, IRBuilder<>& irb, std::string prefix);
  Value* clearTag_2(Value* xmmPtr, IRBuilder<>& irb, std::string prefix);
  Value* unTag(Value* xmmPtr, IRBuilder<>& irb, std::string prefix);
  void preprocessGEP(GetElementPtrInst* gep);
  void preprocessModule(Module& M);

  Value* ununTag(Value* xmmPtr, Type* origType, IRBuilder<>& irb,
                 std::string prefix = "");
  Value* ununTag(Value* xmmPtr, Type* origType, IRBuilder<>& irb,
                 DenseSet<Instruction*>& conList, std::string prefix = "");
  Value* createXmmTag(IRBuilder<>& irb, Value* size, std::string prefix);

  bool isXMMTy(Type* type);
  Value* createOffset(Value* index, Type* type, IRBuilder<>& irb);
  Value* emitGEPOffset(IRBuilder<>& irb, const DataLayout& DL, User* GEP,
                       std::map<Value*, Value*>& valToVal);

  void preAnalyzeGEP(Function* F);
  std::set<Instruction*> instructionToL4;
  void handlePtrToInt(PtrToIntInst* pti);
  void handleIntToPtr(IntToPtrInst* itp);
  void handleSubOrAdd(Instruction* i);
  Value* instrumentWithByteSize(IRBuilder<>& B, Instruction* I,
                                std::map<Value*, Value*>& valToVal);
  bool checkShouldBeWrapped(Function& F);
  Value* splatGEP2(GetElementPtrInst* gep, std::map<Value*, Value*>& valToVal,
                   IRBuilder<>& irb);

 private:
  std::set<StructType*> externStructs;
  bool isExternStruct(Type* type);
  void valuePrintGenerate(Value* val, IRBuilder<>& irb);

  void runOnStructInstrument(Module& M);

  std::set<StructType*> globalSTs;
  Value* splatGEP(GetElementPtrInst* gep, std::map<Value*, Value*>& valToVal,
                  IRBuilder<>& irb);
  StructType* findStruct(StructType* st);
  inline void assertGEP(Value* newGEP) {
    // valuePrint(newGEP, "Assert GEP");
    GetElementPtrInst* newGEPInst = dyn_cast<GetElementPtrInst>(newGEP);

    SmallVector<Value*, 16> Idxs(newGEPInst->indices());
    Type* ElTy = GetElementPtrInst::getIndexedType(
        newGEPInst->getSourceElementType(), Idxs);
    if (!newGEPInst->getType()->isPtrOrPtrVectorTy()) {
      errs() << "!newGEPInst->getType()->isPtrOrPtrVectorTy()\n";
      exit(0);
    }
    if (!(newGEPInst->getResultElementType() == ElTy)) {
      errs() << "!(newGEPInst->getResultElementType() == ElTy)\n";
      exit(0);
    }

    if (newGEPInst->getParent()->getParent()->getName() ==
        "Wrapping_hashtable_getlock") {
      valuePrint(newGEP, "Assert GEP");
      typePrint(ElTy, "ElTy");
      typePrint(newGEPInst->getResultElementType(), "result");
      typePrint(newGEP->getType(), "newGEP type");
    }
  };
};
