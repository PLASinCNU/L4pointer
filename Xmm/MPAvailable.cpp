#include "MPAvailable.h"

#include <llvm/ADT/TinyPtrVector.h>
#include <llvm/Analysis/DependenceAnalysis.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ScalarEvolutionExpander.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/NoFolder.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Transforms/Utils/Local.h>
#include <llvm/Transforms/Utils/LoopUtils.h>
#include <stdio.h>

#include <fstream>
#include <initializer_list>
#include <iostream>

#include "AddressSpace.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "util.h"

#define DEBUG_TYPE "EPSILON"
#define GETCONSTANTINT(CTX, BITWIDTH, VALUE) \
  ConstantInt::get(IntegerType::get(CTX, BITWIDTH), VALUE)

// #define constantNullXMM Constant::getNullValue(XMM)

using namespace llvm;

char MPAvailable::ID = 0;

#if (!LLVM_ENABLE_STATS)

#undef STATISTIC
#define CUSTOM_STATISTICS 1
#define STATISTIC(X, Y) \
  unsigned long X;      \
  const char* X##_desc = Y;

#define STATISTICS_DUMP(X) errs() << "    " << X << " : " << X##_desc << "\n";

#endif

STATISTIC(NEpsilon, "Number of Epsilon");
STATISTIC(VALUE_NOT_L4, "Number of Not L4 Value ");

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerSkeletonPass(const PassManagerBuilder&,
                                 legacy::PassManagerBase& PM) {
  PM.add(new DominatorTreeWrapperPass());
  PM.add(new LoopInfoWrapperPass());
  PM.add(new ScalarEvolutionWrapperPass());
  PM.add(new DependenceAnalysisWrapperPass());
  // PM.add(createVerifierPass());
  PM.add(new MPAvailable());
}
static RegisterStandardPasses RegisterMyPass(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerSkeletonPass);

void MPAvailable::getAnalysisUsage(AnalysisUsage& AU) const {
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<ScalarEvolutionWrapperPass>();
  AU.addRequired<DependenceAnalysisWrapperPass>();
  // AU.addUsedIfAvailable<VerifierAnalysis>();
  // AU.addRequired<DominanceFrontier>();
  // AU.addRequired<SymbolicRangeAnalysis>();
  // AU.addRequired<>();
  AU.setPreservesAll();
}

void MPAvailable::createXmmStructTy(Module& M) {
  // std::list<Type> xmm_elements = {Type::getInt64Ty(M.getContext()),
  // Type::getInt64Ty(M.getContext())};
  ArrayRef<Type*> xmm_element_types(
      {Type::getInt64Ty(M.getContext()), Type::getInt64Ty(M.getContext())});
  XMM = FixedVectorType::get(Type::getInt64Ty(M.getContext()), 2);
  XMM_POINTER = XMM->getPointerTo();
  constantNullXMM = Constant::getNullValue(XMM);
}

StructType* MPAvailable::createStructureType(StructType* st) {
  if (st->hasName() && isExternalStruct(st->getName().str())) {
    return st;
  }
  if (isExternStruct(st)) return st;
  if (strucTyToStructTy.count(st) > 0) {
    StructType* newSt = strucTyToStructTy[st];
    std::vector<Type*> types;
    for (Type* type : newSt->elements()) {
      if (type->isStructTy()) {
        StructType* stElement = dyn_cast<StructType>(type);
        if (strucTyToStructTy.count(stElement) > 0) {
          StructType* newStElement = strucTyToStructTy[stElement];
          types.push_back(newStElement);
        } else
          types.push_back(type);
      } else if (isFunctionPtrTy(type)) {
        FunctionType* ft = dyn_cast<FunctionType>(
            dyn_cast<PointerType>(type)->getPointerElementType());
        FunctionType* newFt = createFunctionType(ft);
        types.push_back(newFt->getPointerTo());
        // types.push_back(type);
      } else if (type->isPointerTy()) {
        types.push_back(XMM);
      } else {
        types.push_back(type);
      }
    }
    StructType* newStructTy = StructType::create(types, newSt->getName());

    strucTyToStructTy[st] = newStructTy;
    return newStructTy;
  }
  std::vector<Type*> plist;
  bool recursive = false;
  bool isNeededTransform = false;
  for (Type* type : st->elements()) {
    if (type->isPointerTy()) isNeededTransform = true;
    if (type->isStructTy()) {
      if (!isExternStruct(type)) isNeededTransform = true;
    }
  }

  if (!isNeededTransform) return st;
  bool isLater = false;
  for (Type* type : st->elements()) {
    if (isFunctionPtrTy(type)) {
      plist.push_back(type);
    } else if (type->isPointerTy()) {
      PointerType* pt = dyn_cast<PointerType>(type);

      // it is linked list, maybe it is not spatial memory pointer.
      plist.push_back(XMM);
    } else if (type->isStructTy()) {
      if (type == st) {
        plist.push_back(st);
        recursive = true;
      } else if (strucTyToStructTy.count(dyn_cast<StructType>(type)) == 0) {
        Type* newType = createStructureType(dyn_cast<StructType>(type));
        plist.push_back(newType);
        isLater = true;
      } else
        plist.push_back(type);
    } else
      plist.push_back(type);
  }
  std::string newStName = st->isLiteral() ? "" : st->getName().str();
  StructType* newStructTy =
      StructType::create(plist, newStName + ".new.struct");
  strucTyToStructTy[st] = newStructTy;
  typePrint(newStructTy, "new struct");
  transStructs.insert(newStructTy);
  return newStructTy;
}
void MPAvailable::transformAlloc(Function& F) {
  transformFunction(&F);
  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E;) {
    // Iterator 형태 바뀌는 것 주의
    // 교수님 말씀에 의하면 원래는 Iterator는 복사형태로 작동하기 때문에 처음
    // 생성할 때 원본이 바뀌어도 원본으로 작동함 하지만 LLVM 4.0.0의 Iterator는
    // 그렇지 않기 때문에 내가 주의해서 해야 됨 List가 바뀐다? -> Iterator 바뀜
    // 주의 (오로지 개발자의 책임)

    // Input: i8* 타입의 Value , Target: AllocaInst
    // Output: i64 Array[2]
    // Replace: 기존의 i8*을 사용하는 instruction을 i64 array[2]로 바꾸어 줌
    // i128-> V2i64로 바꾸기
    inst_iterator vI = I;
    I++;

    switch (vI->getOpcode()) {
      case Instruction::Alloca:
        AllocaInst* ai = dyn_cast<AllocaInst>(&*vI);
        if (ai->getAllocatedType()->isPointerTy()) {
          IRBuilder<> irb(getInsertPointAfter(&*vI));
          AllocaInst* xmm_ai = irb.CreateAlloca(
              XMM, nullptr, dyn_cast<Value>(ai)->getName() + "_XMM");
          continueList.insert(xmm_ai);

          ptrToXMM[ai] = xmm_ai;
          xmmToType[ai] = ai->getAllocatedType();
          // replaceAllUsesWith는 타입이 같아야만 이루어짐

          Value* initV = Constant::getNullValue(XMM);
          Value* flagCons = ConstantInt::get(Type::getInt64Ty(irb.getContext()),
                                             0x8000000000000000);
          Value* setFlagV =
              irb.CreateInsertElement(initV, flagCons, (uint64_t)0);
          irb.CreateStore(setFlagV, xmm_ai);

          replaceAll(ai, xmm_ai);
          ai->eraseFromParent();
          //여기서 바로 지우지 말고 모든 인스트럭션이 교체된 후에 지울것,
          //왜냐하면 포인터가 어떤 타입의 포인터인지 알기 위해서임 기존의 AI는
          // allocMPointer에서 삭제됨
        }
        break;
    }
  }
}

void MPAvailable::createGlobalValue() {
  Module& M = *this->module;
  std::set<GlobalVariable*> addingGVs;
  for (GlobalVariable& GV : M.getGlobalList()) {
    if (GV.getType()->isFunctionTy()) continue;
    if (GV.isConstant()) continue;
    if (addingGVs.count(&GV) > 0) continue;
    if (!GV.hasInitializer()) continue;
    GV.print(errs());
    errs() << "\n";

    if (GV.isDSOLocal()) {
      GV.print(errs());
      errs() << "\n";

      if (GV.getValueType()->isPointerTy()) {
        if (Constant* initCons = GV.getInitializer()) {
          errs() << "여기는 오나? \n";
          if (initCons->isNullValue()) {
            GlobalVariable* gvar_ptr_abc = new GlobalVariable(
                /*Module=*/M,
                /*Type=*/XMM,
                /*isConstant=*/false,
                /*Linkage=*/GlobalValue::InternalLinkage,
                /*Initializer=*/constantNullXMM,  // has initializer, specified
                                                  // below
                /*Name=*/GV.getName() + "_XMM");
            gToGV[&GV] = gvar_ptr_abc;

          } else {
            errs() << " 여긴가?\n";
          }
        } else {
          errs() << "TEST\n";
          GlobalVariable* gvar_ptr_abc = new GlobalVariable(
              /*Module=*/M,
              /*Type=*/XMM,
              /*isConstant=*/false,
              /*Linkage=*/GlobalValue::InternalLinkage,
              /*Initializer=*/0,  // has initializer, specified below
              /*Name=*/GV.getName() + "_XMM");
          gvar_ptr_abc->copyAttributesFrom(&GV);
          gToGV[&GV] = gvar_ptr_abc;
          addingGVs.insert(gvar_ptr_abc);
        }
        continue;
      }
      if (Constant* initCons = GV.getInitializer()) {
        Constant* nullXMM = Constant::getNullValue(XMM);
        valuePrint(initCons, "initCons");
        if (dyn_cast<PointerType>(initCons->getType())
                ? dyn_cast<PointerType>(initCons->getType())
                      ->getElementType()
                      ->isArrayTy()
                : false) {
          Constant* addr = ConstantExpr::getBitCast(
              initCons, IntegerType::getInt64Ty(M.getContext()));
          unsigned int arrayIntSize = this->DL->getTypeAllocSize(
              dyn_cast<PointerType>(initCons->getType())->getElementType());
          Value* size = ConstantInt::get(
              IntegerType::getInt64Ty(M.getContext()), arrayIntSize);
          Constant* mask = createConstantMask(size, M.getContext());
          Constant* zero = ConstantInt::get(Type::getInt8Ty(M.getContext()), 0);
          Constant* one = ConstantInt::get(Type::getInt8Ty(M.getContext()), 1);
          Constant* vec1 = ConstantExpr::getInsertElement(nullXMM, mask, zero);
          Constant* vec2 = ConstantExpr::getInsertElement(vec1, addr, one);
          GlobalVariable* gvar_ptr_abc = new GlobalVariable(
              /*Module=*/M,
              /*Type=*/XMM,
              /*isConstant=*/false,
              /*Linkage=*/GlobalValue::InternalLinkage,
              /*Initializer=*/vec2,  // has initializer, specified below
              /*Name=*/GV.getName() + "_XMM");
          errs() << "NOTEST\n";
          gToGV[&GV] = gvar_ptr_abc;
          addingGVs.insert(gvar_ptr_abc);
        } else if (GV.getType()->isPointerTy()) {
          if (Constant* initCons = GV.getInitializer()) {
          } else {
            errs() << "TEST\n";
            GlobalVariable* gvar_ptr_abc = new GlobalVariable(
                /*Module=*/M,
                /*Type=*/XMM,
                /*isConstant=*/false,
                /*Linkage=*/GlobalValue::InternalLinkage,
                /*Initializer=*/0,  // has initializer, specified below
                /*Name=*/GV.getName() + "_XMM");
            gToGV[&GV] = gvar_ptr_abc;
            addingGVs.insert(gvar_ptr_abc);
          }
        }
      }
    }
  }
}
bool MPAvailable::runOnModule(Module& M) {
  DL = &M.getDataLayout();
  errs() << "Run On Module\n";
  module = &M;
  runOnStructInstrument(M);
  createXmmStructTy(M);
  replaceStructTy(M);
  createGlobalValue();

  printFunction = M.getOrInsertFunction(
      "printf",
      FunctionType::get(IntegerType::getInt32Ty(M.getContext()),
                        PointerType::get(Type::getInt8Ty(M.getContext()), 0),
                        true /* this is var arg func type*/));
  // verifyGlobalValue(M);
  // preprocessModule(M);
  for (StructType* st : M.getIdentifiedStructTypes()) {
    if (st->isOpaque()) continue;
    if (isExternStruct(st)) continue;
    if (st->isPacked()) errs() << "is Pack : ";
    if (strucTyToStructTy.count(st) > 0) {
      typePrint(st, "original");
      typePrint(strucTyToStructTy[st], "transform");
    }
  }

  for (auto& F : M) {
    if (!F.hasName()) {
      errs() << "F has no name \n";
      continue;
    }
    if (F.isDeclaration()) continue;
    declareWrappingFunction(F);
  }
  for (auto& F : M) {
    if (!F.hasName()) {
      errs() << "F has no name \n";
      continue;
    }
    if (wrappingFunctions.count(&F) > 0) continue;
    if (!(&F)) continue;
    if (F.isDeclaration()) continue;
    DT = &getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
    LI = &getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
    SE = &getAnalysis<ScalarEvolutionWrapperPass>(F).getSE();
    errs() << F.getName() << "\n";
    createWrappingFunction(F);
  }
  errs() << "create wrapping main\n";
  // for (auto& F : M) {
  //   if (!(&F)) continue;
  //   if (F.isDeclaration()) continue;

  //   // createWrappingMain(F);
  // }
  std::vector<Function*> workList(willBeDeletedFunctions.begin(),
                                  willBeDeletedFunctions.end());

  int count = 0;
  int beforeSize = workList.size();
  verifyModule(M);

  while (!workList.empty()) {
    Function* F = workList.front();
    if (usedFunctions.count(F) > 0) {
      workList.erase(workList.begin());
      continue;
    }
    if (F->users().empty()) {
      workList.erase(workList.begin());
      // deleteFunctionInst(*F);
      deleteFunction(F);
      F->dropDroppableUses();
      F->eraseFromParent();
    } else {
      if (F->doesNotRecurse()) {
        workList.erase(workList.begin());
        workList.push_back(F);
      } else {
        workList.erase(workList.begin());
        workList.push_back(F);
        deleteFunction(F);
      }
    }
    if (workList.size() == beforeSize) {
      count++;
    } else
      count = 0;
    if (count > 1000) {
      errs() << "무한루프\n";
      break;
    }
    beforeSize = workList.size();
  }
  for (Function* F : workList) {
    errs() << "안지워지는 함수 : " << F->getName() << "\n";
    traceUses(F);
  }
  errs() << "Deleting process finished!\n";

  eraseRemoveInstruction();
  verifyModule(M);
  errs() << "VerifyModule ! \n";
  return false;
}

void MPAvailable::analyzeGEPforFunction(Function& F) {
  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E;) {
    inst_iterator vI = I;
    I++;
  }
}
void MPAvailable::allocation(Module& M) {
  for (Function& F : M) {
    allocOnFunction(F);
  }
}

void MPAvailable::propagateGEP(Module& M) {
  for (Function& F : M) {
    if (F.isDeclaration()) continue;
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E;) {
      // errs() <<"GEP무한루프?????\n";
      // instPrint(&*I, "GEP무한");
      inst_iterator vI = I;
      I++;

      if (continueList.find(&*vI) != continueList.end()) {
        continue;
      }

      switch (vI->getOpcode()) {
        case Instruction::Store: {
          StoreInst* si = dyn_cast<StoreInst>(&*vI);
          handleStore(si);
          break;
        }
        case Instruction::PtrToInt: {
          PtrToIntInst* pti = dyn_cast<PtrToIntInst>(&*vI);
          handlePtrToInt(pti);
          break;
        }
        case Instruction::IntToPtr: {
          IntToPtrInst* itp = dyn_cast<IntToPtrInst>(&*vI);
          handleIntToPtr(itp);
          break;
        }
        case Instruction::ICmp: {
          ICmpInst* iCmp = dyn_cast<ICmpInst>(&*vI);
          handleIcmp(iCmp);
          break;
        }
        case Instruction::BitCast: {
          BitCastInst* bci = dyn_cast<BitCastInst>(&*vI);
          //          debugBCI(bci);
          break;
        }
        case Instruction::Sub:
        case Instruction::Add: {
          handleSubOrAdd(&*vI);
          break;
        }

        case Instruction::GetElementPtr: {
        }
        case Instruction::Call: {
          CallInst* ci = dyn_cast<CallInst>(&*vI);
          handleCall(ci);
          break;
        }

        case Instruction::Load: {
          LoadInst* li = dyn_cast<LoadInst>(&*vI);
          handleLoad(li);
          break;
        }
      }
    }
    transformFunction(&F);
  }
}

void MPAvailable::allocOnFunction(Function& F) {
  // SRA = &getAnalysis<SymbolicRangeAnalysis>(F);
  // ScalarEvolution *SE = &getAnalysis<ScalarEvolutionWrapperPass>(F).getSE();
  for (Instruction& I : instructions(F)) {
    if (isAllocation(&I)) allocEpsilon(I, SE);

    if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
      Function* F = CallSite(&I).getCalledFunction();
      if (F && F->isDeclaration()) continue;
    }
  }
}

void MPAvailable::allocEpsilon(Instruction& I, ScalarEvolution* SE) {
  if (isa<BitCastInst>(I.getNextNode())) {
    IRBuilder<> irb(getInsertPointAfter(I.getNextNode()));
    l4Alloc(I, SE, irb);
  } else {
    IRBuilder<> irb(getInsertPointAfter(&I));
    l4Alloc(I, SE, irb);
  }
}

void MPAvailable::l4Alloc(Instruction& I, ScalarEvolution* SE,
                          IRBuilder<>& irb) {}

Constant* MPAvailable::getNullPtr(PointerType* Ty) {
  IntegerType* IntTy = IntegerType::get(Ty->getContext(), 64);
  ConstantInt* IntVal = ConstantInt::get(IntTy, BOUND_MASK_HIGH);
  return ConstantExpr::getIntToPtr(IntVal, Ty);
}

Value* MPAvailable::createOffset(Value* index, Type* type, IRBuilder<>& irb) {
  uint64_t typeSize = DL->getTypeAllocSize(type->getPointerElementType());
  ConstantInt* typeSizeToValue =
      ConstantInt::get(IntegerType::get(irb.getContext(), 64), typeSize);
  Value* offset = irb.CreateMul(index, typeSizeToValue, "offset");
  return offset;
}

Value* MPAvailable::emitGEPOffset(IRBuilder<>& irb, const DataLayout& DL,
                                  User* GEP,
                                  std::map<Value*, Value*>& valToVal) {
  GEPOperator* GEPOp = cast<GEPOperator>(GEP);
  Type* IntIdxTy = DL.getIndexType(GEP->getType());
  Value* Result = nullptr;

  // If the GEP is inbounds, we know that none of the addressing operations will
  // overflow in a signed sense.
  bool isInBounds = GEPOp->isInBounds();

  // Build a mask for high order bits.
  unsigned IntPtrWidth = IntIdxTy->getScalarType()->getIntegerBitWidth();
  uint64_t PtrSizeMask =
      std::numeric_limits<uint64_t>::max() >> (64 - IntPtrWidth);

  gep_type_iterator GTI = gep_type_begin(GEP);
  for (User::op_iterator i = GEP->op_begin() + 1, e = GEP->op_end(); i != e;
       ++i, ++GTI) {
    Value* Op;
    Value* Val = *i;
    if (valToVal.count(Val) > 0)
      Op = valToVal[Val];
    else {
      // assert(isa<Constant>(Val) && "Val must be constant!");
      Op = Val;
    }
    uint64_t Size = DL.getTypeAllocSize(GTI.getIndexedType()) & PtrSizeMask;
    Value* Offset;
    if (Constant* OpC = dyn_cast<Constant>(Op)) {
      if (OpC->isZeroValue()) continue;

      // Handle a struct index, which adds its field offset to the pointer.
      if (StructType* STy = GTI.getStructTypeOrNull()) {
        if (strucTyToStructTy.count(STy) > 0) STy = strucTyToStructTy[STy];
        uint64_t OpValue = OpC->getUniqueInteger().getZExtValue();
        Size = DL.getStructLayout(STy)->getElementOffset(OpValue);
        if (!Size) continue;

        Offset = ConstantInt::get(IntIdxTy, Size);
      } else {
        // Splat the constant if needed.
        if (IntIdxTy->isVectorTy() && !OpC->getType()->isVectorTy())
          OpC = ConstantVector::getSplat(
              cast<VectorType>(IntIdxTy)->getElementCount(), OpC);

        Constant* Scale = ConstantInt::get(IntIdxTy, Size);
        Constant* OC =
            ConstantExpr::getIntegerCast(OpC, IntIdxTy, true /*SExt*/);
        Offset =
            ConstantExpr::getMul(OC, Scale, false /*NUW*/, isInBounds /*NSW*/);
      }
    } else {
      // Splat the index if needed.
      if (IntIdxTy->isVectorTy() && !Op->getType()->isVectorTy())
        Op = irb.CreateVectorSplat(
            cast<FixedVectorType>(IntIdxTy)->getNumElements(), Op);

      // Convert to correct type.
      if (Op->getType() != IntIdxTy)
        Op = irb.CreateIntCast(Op, IntIdxTy, true, Op->getName().str() + ".c");
      if (Size != 1) {
        // We'll let instcombine(mul) convert this to a shl if possible.
        Op = irb.CreateMul(Op, ConstantInt::get(IntIdxTy, Size),
                           GEP->getName().str() + ".idx", false /*NUW*/,
                           isInBounds /*NSW*/);
      }
      Offset = Op;
    }

    if (Result)
      Result = irb.CreateAdd(Result, Offset, GEP->getName().str() + ".offs",
                             false /*NUW*/, isInBounds /*NSW*/);
    else
      Result = Offset;
  }
  return Result ? Result : Constant::getNullValue(IntIdxTy);
}

void MPAvailable::handleGEP(GetElementPtrInst* gep) {
  IRBuilder<> irb(getInsertPointAfter(gep));

  Value* xmm_pointer;
  Value* xmm_offset;
  GetElementPtrInst* PreemptedGep = nullptr;

  if (!gep) return;

  if (instructionToL4.find(dyn_cast<Instruction>(gep)) == instructionToL4.end())
    return;

  // if (gep->getPointerOperand()->getType()->getContainedType(0) !=
  // XMM_POINTER) return ; XMM 포인터는 기존의 포인터 변수 대신에 내가 만든
  // 구조체로 할당되기 때문에 gep 이전의 load도 다시 해야 됨

  bool isPositive = gepToPositive[gep];

  Value* base =
      gep->getPointerOperand()
          ->stripPointerCasts();  // base는 load 인스트럭션, 그리고 int128

  if (!isXMMTy(base->getType())) return;
  LoadInst* origLoad = dyn_cast<LoadInst>(base);
  Type* type = valueToType[base];
  // willBeRemoveSet.insert(origLoad);

  Value* tag;
  uint64_t constOffset;

  std::string Prefix = std::string(base->getName()) + "." + ".array.";
  // cast<Instruction>(irb.CreatePtrToInt(ptrToXMM[base], PtrIntTy, Prefix +
  // "int"));

  // const 일경우 -1. 양수, 2. 음수
  // const 아닐 경우 - 1. 양수, 음수

  //속도를 위해선 메모리 load나 레지스터 거쳐가는 것을 최대한 줄일것

  // 오프셋 만드는 건 보류
  // 이거를 내가 직접 만들어보자...
  Value* Offset = EmitGEPOffset(&irb, *DL, gep);

  Value* replacePointer = nullptr;
  Value* emptyVec = Constant::getNullValue(XMM);

  // 어차피 vector 계산이니까
  // 양수, 음수 계산 따로 할 필요가 없음
  // 그럼 constoffset이냐 아니냐로만 구분하고

  // IRBuilder<> irbOffset(getInsertPointAfter(dyn_cast<Instruction>(Offset)));
  Value* element1 = irb.CreateInsertElement(emptyVec, Offset, (uint64_t)0);
  Value* element2 = irb.CreateInsertElement(element1, Offset, 1);
  replacePointer =
      irb.CreateAdd(base, element2, gep->getName() + ".TYPEPTR.sub");

  // irb.CreateInsertElement(emptyVec, , 0);
  // 일단 L4포인터로 생성이 안되고 있음
  // 이것먼저 되게 고쳐야함

  // tag를 만들고 나서 보수하는거니까 tag하고 나서 확인하고 해도 되지

  //이거를 고쳐야 함
  // continueList.insert(dyn_cast<Instruction>(P));

  // replacePointer is v2i64
  replaceAll(gep, replacePointer);
  gep->eraseFromParent();
}

void MPAvailable::handlePtrToInt(PtrToIntInst* pti) {
  Value* op = pti->getPointerOperand();
  if (isXMMTy(op->getType())) {
    replaceAll(pti, op);
    pti->eraseFromParent();
  }
}

void MPAvailable::handleIntToPtr(IntToPtrInst* itp) {
  Value* op = itp->getOperand(0);

  if (isXMMTy(op->getType())) {
    replaceAll(itp, op);
    itp->eraseFromParent();
  }
}

void MPAvailable::handleIcmp(ICmpInst* iCmpI) {
  // null 인지 아닌지 확인해야해서 복구해야 됨
  //즉 load나 스토어처럼 동작
  IRBuilder<> irb(iCmpI);
  Value* xmmPointer;
  Value* iCmpValue;
  if (isXMMTy(iCmpI->getOperand(0)->getType())) {
    xmmPointer = iCmpI->getOperand(0);
    iCmpValue = iCmpI->getOperand(1);
    Value* unWrapValue = ununTag(xmmPointer, iCmpValue->getType(), irb);
    iCmpI->setOperand(0, unWrapValue);
  } else if (isXMMTy(iCmpI->getOperand(1)->getType())) {
    xmmPointer = iCmpI->getOperand(1);
    iCmpValue = iCmpI->getOperand(0);
    Value* unWrapValue = ununTag(xmmPointer, iCmpValue->getType(), irb);
    iCmpI->setOperand(1, unWrapValue);
  } else
    return;
}
void MPAvailable::handleSubOrAdd(Instruction* i) {
  IRBuilder<> irb(i);
  Value* replacer;
  if (isXMMTy(i->getOperand(0)->getType())) {
    Value* op1 = i->getOperand(1);
    Value* nullVector = Constant::getNullValue(XMM);
    Value* vec0 = irb.CreateInsertElement(nullVector, op1, (uint64_t)0);
    Value* vec1 = irb.CreateInsertElement(vec0, op1, 1);

    if (i->getOpcode() == Instruction::Add)
      replacer = irb.CreateAdd(i->getOperand(0), vec1);
    else
      replacer = irb.CreateSub(i->getOperand(0), vec1);
  } else if (isXMMTy(i->getOperand(1)->getType())) {
    Value* op0 = i->getOperand(0);
    Value* nullVector = Constant::getNullValue(XMM);
    Value* vec0 = irb.CreateInsertElement(nullVector, op0, (uint64_t)0);
    Value* vec1 = irb.CreateInsertElement(vec0, op0, 1);

    if (i->getOpcode() == Instruction::Add)
      replacer = irb.CreateAdd(i->getOperand(1), vec1);
    else
      replacer = irb.CreateSub(i->getOperand(1), vec1);
  }
  replaceAll(i, replacer);
  i->eraseFromParent();
}

bool MPAvailable::hasNegativeOffset(GetElementPtrInst* gep) {
  // 먼저 gep에 대해서 분석을 해놓자

  APInt ConstOffset(64, 0);
  if (gep->accumulateConstantOffset(*DL, ConstOffset))
    return ConstOffset.isNegative();

  // For synamid offsets, look for the pattern "gep %base, (sub 0, %idx)"
  // XXX this is best-effort and may not catch all cases
  for (int i = 1, l = gep->getNumOperands(); i < l; i++) {
    Value* Index = gep->getOperand(i);

    Instruction* I = dyn_cast<Instruction>(Index);
    if (I == nullptr) continue;
    if (I->getOpcode() != Instruction::Sub) continue;

    ConstantInt* PossibleZero = dyn_cast<ConstantInt>(I->getOperand(0));
    if (PossibleZero == nullptr) continue;
    if (PossibleZero->getSExtValue() == 0) return true;
  }

  return false;
}

void MPAvailable::handleStore(StoreInst* si) {
  // GEP->STORE
  // LOAD->STORE
  // TYPE 검사
  // Input: i128이 ptr 로 오는 StoreInst
  // Output: i128 타입의 ptr이 포인터(i8*) 로 변경된 StoreInst
  // Replace: 없음

  // 포인터가 전파될때 store %1, %a 이런 식
  // 그런게 아니면 store %1, %2 이런 식

  // ununtag에 타입 변환이 들어갈 것
  //  Type* origType = si->getValu

  Value* addr = si->getOperand(1);

  IRBuilder<> irb(getInsertPointAfter(si));

  if (isa<AllocaInst>(addr)) {
    IRBuilder<> irbefore(getInsertPointBefore(si));
    if (isXMMTy(dyn_cast<AllocaInst>(addr)->getAllocatedType())) {
      if (isXMMTy(si->getValueOperand()->getType()))
        irb.CreateStore(si->getValueOperand(), si->getPointerOperand());
      else {
        // 이건 일종의 에러 핸들링 케이스..? 이런 경우가 많으면 안좋음
        // 카운트 체크 하게 바꿀 것
        VALUE_NOT_L4++;
        Value* nullVector = Constant::getNullValue(XMM);
        Value* valueVector;
        if (si->getValueOperand()->getType()->isIntegerTy()) {
          if (!si->getValueOperand()->getType()->isIntegerTy(64)) {
            Value* bitCast = irb.CreateBitCast(
                si->getValueOperand(), Type::getInt64Ty(si->getContext()));
            valueVector =
                irb.CreateInsertValue(nullVector, si->getValueOperand(), 1);
          } else
            valueVector =
                irb.CreateInsertElement(nullVector, si->getValueOperand(), 1);
        } else if (si->getValueOperand()->getType()->isPointerTy()) {
          Value* ptrToInt = irb.CreatePtrToInt(
              si->getValueOperand(), Type::getInt64Ty(si->getContext()));
          Value* bitCast =
              irb.CreateBitCast(ptrToInt, Type::getInt64Ty(si->getContext()));
          typePrint(nullVector->getType(), "nullvector");
          typePrint(bitCast->getType(), "bitCast");
          valueVector =
              irb.CreateInsertElement(nullVector, bitCast, (uint64_t)1);
        }
        irb.CreateStore(valueVector, si->getPointerOperand());
      }
      //여기에 타입이 퍼져나가는 것을 놓자

      si->eraseFromParent();
    }
  } else if (isXMMTy(addr->getType())) {
    Type* valueType = si->getValueOperand()->getType();
    Type* toPointer = valueType->getPointerTo();
    Value* clearTagPointer = ununTag(addr, toPointer, irb, "store");
    Value* replaceInst = irb.CreateStore(si->getOperand(0), clearTagPointer);
    si->eraseFromParent();
    // instPrint(dyn_cast<Instruction>(replaceInst), "i128llvm");
    // continueList.insert(dyn_cast<Instruction>(replaceInst));
  }
  return;
}

void MPAvailable::handleLoad(LoadInst* li) {
  //  %0 = load i8*, i8** %ptr, align 8

  //오퍼랜드가 GEP인지 아니면 AllocaInst 인지 확인해야함
  // GEP->LOAD
  // AllocaInst->LOAD
  // LOAD->LOAD

  // i128 -> 18*
  // v2i64의 LOAD로 바꾸기

  //먼저 포인터로 타입변환
  // load
  Type* origType = li->getType();
  Value* liOp = li->getPointerOperand();

  IRBuilder<> irb(getInsertPointAfter(li));

  if (isa<AllocaInst>(liOp)) {
    AllocaInst* ai = dyn_cast<AllocaInst>(liOp);
    if (!isXMMTy(ai->getAllocatedType())) return;
    // type 비교 equal은 없는거 같음 없으면 내가 구현 ㅇㅋ?
    // array[2] :i64 를 i128로 load 하기

    //새로운 load 생성

    LoadInst* newLoad =
        irb.CreateLoad(XMM, liOp, liOp->getName() + ".TYPEPTRLOAD");
    continueList.insert(cast<Instruction>(newLoad));
    xmmLoadSet.insert(dyn_cast<Value>(newLoad));
    replaceAll(li, newLoad);
    valueToType[newLoad] = xmmToType[ai];
    li->eraseFromParent();
  } else if (isXMMTy(liOp->getType())) {
    //태그 클리어 및 로드하는 인스트럭션으로 바꿔주기
    //타입 확인도 할것
    Type* type = valueToType[liOp];
    Value* clearTagPointer =
        ununTag(liOp, origType->getPointerTo(), irb, liOp->getName().str());
    Value* replaceInst =
        irb.CreateLoad(clearTagPointer, liOp->getName() + "clear.bit");
    continueList.insert(dyn_cast<Instruction>(replaceInst));
    li->replaceAllUsesWith(replaceInst);
    li->eraseFromParent();
  }
}

bool MPAvailable::isInnerTagPossible(Value* size) {
  if (ConstantInt* intSize = dyn_cast<ConstantInt>(size)) {
    int realSize = intSize->getSExtValue();
    if (realSize <= 128)
      return true;
    else
      return false;
  } else {
    // SRA->
    const SCEV* sc = SE->getSCEV(size);
    if (sc->isAllOnesValue()) {
      ConstantRange cr = SE->getUnsignedRange(sc);
      if (cr.isEmptySet()) return false;
      APInt ai = cr.getUnsignedMax();
      int64_t intSize = ai.getSExtValue();
      if (intSize > 128)
        return false;  // if(>128) return false;
      else
        return true;
    } else
      return false;
  }
  return false;
}

void MPAvailable::initFunction(Module& M) {
  Type* PtrIntTy = getPtrIntTy(M.getContext());
  AddWithOverflowFunc =
      Intrinsic::getDeclaration(&M, Intrinsic::uadd_with_overflow, PtrIntTy);
}

void MPAvailable::eraseRemoveInstruction() {
  for (Instruction* inst : willBeRemoveSet) {
    instPrint(inst, "erase");
    inst->eraseFromParent();
  }
}

Value* MPAvailable::clearTag_2(Value* xmmPtr, IRBuilder<>& irb,
                               std::string prefix) {
  // xmmPtr 은 XMMP 구조체
  // 먼저, tag 갖고 오기 tag 가공해야됨 그 이유는 상위 17bit으로 몰아주기 위해서
  // 그 다음 메모리 주소 bitcast 하기
  // and 연산해서 바꿔주기

  // Load를 두개를 만들자
  //하나는 128로 load 하는 것
  //하나는 각각 64bit으로 load 하는 것
  Value* xmmPtr_ = cast<LoadInst>(xmmPtr)->getOperand(0);
  Value* indexListTag[2] = {
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       0),
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       0)};
  Value* XmmTag =
      irb.CreateInBoundsGEP(xmmPtr, indexListTag, xmmPtr->getName() + ".tag");

  Value* indexListOffset[2] = {
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       0),
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       1)};
  Value* xmmOffset =
      irb.CreateInBoundsGEP(xmmPtr, indexListOffset, prefix + ".offset");

  Value* XmmTagLoad = irb.CreateLoad(XmmTag);
  Value* XmmOffsetLoad = irb.CreateLoad(xmmOffset);

  Value* xmmTagAnd = irb.CreateAnd(
      XmmTagLoad, 0x8000000080000000,
      prefix + ".tag.and");  //여기서 이미 태그를 제외한 메타데이터 클리어가 됨
  Value* xmmTagOverShl = irb.CreateShl(xmmTagAnd, 31, prefix + ".tag.over.shl");
  Value* xmmTagAssemble =
      irb.CreateOr(xmmTagAnd, xmmTagOverShl, prefix + "tag.assemble");
  Value* xmmTagResult =
      irb.CreateAnd(xmmTagAssemble, 0xC000000000000000, prefix + ".result");

  Value* clearPointer =
      irb.CreateOr(xmmTagResult, XmmOffsetLoad, prefix + ".clear");
  Value* result =
      irb.CreateBitCast(clearPointer, xmmToType[dyn_cast<AllocaInst>(xmmPtr)],
                        prefix + ".unwrap");

  return result;
}

Value* MPAvailable::unTag(Value* xmmPtr, IRBuilder<>& irb, std::string prefix) {
  Value* xmmPtr_ = cast<LoadInst>(xmmPtr)->getOperand(0);
  Value* indexListTag[2] = {
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       0),
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       0)};
  Value* XmmTag =
      irb.CreateInBoundsGEP(xmmPtr, indexListTag, xmmPtr->getName() + ".tag");

  Value* indexListOffset[2] = {
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       0),
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       1)};
  Value* xmmOffset =
      irb.CreateInBoundsGEP(xmmPtr, indexListOffset, prefix + ".offset");

  Value* XmmTagLoad = irb.CreateLoad(XmmTag);
  Value* XmmOffsetLoad = irb.CreateLoad(xmmOffset);

  Value* xmmTagAnd = irb.CreateAnd(
      XmmTagLoad, 0x8000000080000000,
      prefix + ".tag.and");  //여기서 이미 태그를 제외한 메타데이터 클리어가 됨
  Value* xmmTagOverShl = irb.CreateShl(xmmTagAnd, 31, prefix + ".tag.over.shl");
  Value* xmmTagAssemble =
      irb.CreateOr(xmmTagAnd, xmmTagOverShl, prefix + "tag.assemble");
  Value* xmmTagResult =
      irb.CreateAnd(xmmTagAssemble, 0xC000000000000000, prefix + ".result");

  Value* clearPointer =
      irb.CreateOr(xmmTagResult, XmmOffsetLoad, prefix + ".clear");
  Value* result =
      irb.CreateIntToPtr(clearPointer, xmmToType[dyn_cast<AllocaInst>(xmmPtr)],
                         prefix + ".unwrap");

  return result;
}

Value* MPAvailable::ununTag(Value* xmmPtr, Type* origType, IRBuilder<>& irb,
                            std::string prefix) {
  // i128 -> i64 -> i64* -> T* (T is original Type)
  // Trunc instruction 이용
  // oritType must be Pointer
  assert(isXMMTy(xmmPtr->getType()) && "origType must be XMMTy.");
  APInt oneAPInt(64, 1);
  ConstantInt::get(irb.getInt64Ty(), 1);
  Constant* one = ConstantInt::get(irb.getInt64Ty(), 1);

  Value* lowerSignal = irb.CreateShl(one, 63);
  Value* upperSignal = irb.CreateShl(one, 31);

  Value* signal = irb.CreateOr(lowerSignal, upperSignal);

  Value* tag =
      irb.CreateExtractElement(xmmPtr, (uint64_t)0, prefix + ".tag.extract");

  Value* pointer = irb.CreateExtractElement(xmmPtr, 1, prefix + ".ptr");

  Value* removeTag = irb.CreateAnd(signal, tag);
  Constant* cons = dyn_cast<Constant>(removeTag);

  Value* lower = irb.CreateAnd(removeTag, lowerSignal);
  Value* upper = irb.CreateShl(removeTag, 32);
  Value* resultTag = irb.CreateOr(lower, upper);

  //상위 태그만 남겨두고 나머지는 0으로 만들기
  // result_ptr = ptr || tag    ----> 실제 주소만 남고 상위 시그널 비트가 1일
  // 경우에만 세팅이 됨
  Value* resultPtr = irb.CreateOr(resultTag, pointer, prefix + ".ptr.result");

  Value* ptr = irb.CreateIntToPtr(
      resultPtr, Type::getInt8PtrTy(irb.getContext()), prefix + "unun_ptr");
  Value* res;
  if (origType->isPointerTy()) {
    PointerType* pointerType = dyn_cast<PointerType>(origType);

    if (pointerType->getPointerElementType()->isStructTy()) {
      Type* elementType = pointerType->getPointerElementType();
      StructType* st = dyn_cast<StructType>(elementType);
      if (strucTyToStructTy.count(st) > 0) {
        StructType* newSt = strucTyToStructTy[st];
        res = irb.CreateBitCast(ptr, newSt->getPointerTo(),
                                prefix + "new.strcut.unwrap");
      } else
        res = irb.CreateBitCast(ptr, origType, prefix + "old.struct.unwrap");
    } else if (isFunctionPtrTy(origType)) {
      // errs() << "HERE?\n";
      FunctionType* ft =
          dyn_cast<FunctionType>(pointerType->getPointerElementType());
      FunctionType* newFt = createFunctionType(ft);
      res = irb.CreateBitCast(ptr, newFt->getPointerTo(), prefix + ".fpunwrap");
      // res = irb.CreateBitCast(ptr, origType, prefix + ".fpunwrap");
    } else if (isFunctionPtrPtrTy(origType)) {
      PointerType* pt =
          dyn_cast<PointerType>(pointerType->getPointerElementType());
      FunctionType* ft = dyn_cast<FunctionType>(pt->getPointerElementType());
      FunctionType* newFt = createFunctionType(ft);
      res = irb.CreateBitCast(ptr, newFt->getPointerTo()->getPointerTo(),
                              prefix + ".fpunwrap");
      // res = irb.CreateBitCast(ptr, origType, prefix + ".fpunwrap");
    } else {
      res = irb.CreateBitCast(ptr, origType, prefix + ".unwrap");
    }
  } else {
    res = irb.CreateBitCast(ptr, origType, prefix + ".unwrap");
  }
  return res;
}
Value* MPAvailable::createL4Ptr(Value* ptr, IRBuilder<>& irb) {
  assert(ptr->getType()->isPointerTy() && "Ptr must be PointerTy");
  Constant* nullValue = Constant::getNullValue(XMM);

  Value* vec1 = irb.CreateInsertElement(
      nullValue, ConstantInt::get(irb.getInt64Ty(), 0), (uint64_t)0);
  Value* ptrToInt64 = irb.CreatePtrToInt(ptr, irb.getInt64Ty());
  Value* vec2 = irb.CreateInsertElement(vec1, ptrToInt64, 1);
  return vec2;
}

Value* MPAvailable::ununTag(Value* xmmPtr, Type* origType, IRBuilder<>& irb,
                            DenseSet<Instruction*>& conList,
                            std::string prefix) {
  // i128 -> i64 -> i64* -> T* (T is original Type)
  // Trunc instruction 이용
  // oritType must be Pointer
  assert(isXMMTy(xmmPtr->getType()) && "origType must be XMMTy.");
  APInt oneAPInt(64, 1);
  ConstantInt::get(irb.getInt64Ty(), 1);
  Constant* one = ConstantInt::get(irb.getInt64Ty(), 1);

  Value* lowerSignal = irb.CreateShl(one, 63);
  conList.insert(dyn_cast<Instruction>(lowerSignal));
  Value* upperSignal = irb.CreateShl(one, 31);
  conList.insert(dyn_cast<Instruction>(upperSignal));
  Value* signal = irb.CreateOr(lowerSignal, upperSignal);
  conList.insert(dyn_cast<Instruction>(signal));
  Value* tag =
      irb.CreateExtractElement(xmmPtr, (uint64_t)0, prefix + ".tag.extract");
  conList.insert(dyn_cast<Instruction>(tag));
  Value* pointer = irb.CreateExtractElement(xmmPtr, 1, prefix + ".ptr");
  conList.insert(dyn_cast<Instruction>(pointer));

  Value* removeTag = irb.CreateAnd(signal, tag);
  Constant* cons = dyn_cast<Constant>(removeTag);
  conList.insert(dyn_cast<Instruction>(removeTag));

  Value* lower = irb.CreateAnd(removeTag, lowerSignal);
  Value* upper = irb.CreateShl(removeTag, 32);
  Value* resultTag = irb.CreateOr(lower, upper);
  conList.insert(dyn_cast<Instruction>(lower));
  conList.insert(dyn_cast<Instruction>(upper));
  conList.insert(dyn_cast<Instruction>(resultTag));
  //상위 태그만 남겨두고 나머지는 0으로 만들기
  // result_ptr = ptr || tag    ----> 실제 주소만 남고 상위 시그널 비트가 1일
  // 경우에만 세팅이 됨
  Value* resultPtr = irb.CreateOr(resultTag, pointer, prefix + ".ptr.result");
  conList.insert(dyn_cast<Instruction>(resultPtr));
  Value* ptr = irb.CreateIntToPtr(
      resultPtr, Type::getInt8PtrTy(irb.getContext()), prefix + "realloc_ptr");
  conList.insert(dyn_cast<Instruction>(ptr));
  Value* res = irb.CreateBitCast(ptr, origType, prefix + ".unwrap");
  conList.insert(dyn_cast<Instruction>(res));
  return res;
}
// void MPAvailable::replaceGEP(Value* orig, Value* replacer){
//   assert(isa<GetElementPtrInst>(orig) &&"orig must be a GetElementPtrInst");
//   for( Value::user_iterator ui = orig->user_begin(); ui != orig->user_end() ;
//   ){
//     errs() <<"USER : ";
//     ui->print(errs()); errs() <<"\n";
//     Value::user_iterator vui = ui;
//     ui++;

//     Instruction* inst = dyn_cast<Instruction>(*vui);
//     switch(inst->getOpcode()){
//     case Instruction::Load:
//       inst->setOperand(0, replacer);
//       break;
//     case Instruction::Store:
//       if(inst->getOperand(0) == orig) inst->setOperand(0, replacer);
//       else if (inst->getOperand(1) == orig) inst->setOperand(1, replacer);
//       break;
//     case Instruction::GetElementPtr:
//       inst->setOperand(0, replacer);
//       break;
//     }
//   }
// }

void MPAvailable::replaceAll(Value* orig, Value* replacer) {
  for (Value::user_iterator ui = orig->user_begin(); ui != orig->user_end();) {
    Value::user_iterator vui = ui;
    ui++;
    Instruction* inst = dyn_cast<Instruction>(*vui);
    for (int i = 0; i < inst->getNumOperands(); i++) {
      if (inst->getOperand(i) == orig) {
        inst->setOperand(i, replacer);
      }
    }
  }
}

void MPAvailable::verifyModule(Module& M) {
  std::string filePath = M.getName().str() + ".ll";

  raw_ostream* out = &outs();
  std::error_code EC;
  out = new raw_fd_ostream(filePath, EC);

  for (Function& F : M) {
    if (F.isDeclaration()) continue;
    *out << F.getName().str() << "\n";
    F.getFunctionType()->print(*out);
    *out << "\n";
    F.print(*out);
    // for (Instruction& I : instructions(F)) {
    //   I.print(*out);
    //   *out << "\n";
    // }
  }

  // delete out;
}

void MPAvailable::preprocessGEP(GetElementPtrInst* gep) {
  ConstantInt* ConstOffset = nullptr;
  APInt ConstOffsetVal(64, 0);
  if (gep->accumulateConstantOffset(*DL, ConstOffsetVal))
    ConstOffset = dyn_cast<ConstantInt>(
        GETCONSTANTINT(gep->getContext(), 64, ConstOffsetVal));

  gepToOffset[gep] = ConstOffset;
  gepToPositive[gep] = hasNegativeOffset(gep);
}

void MPAvailable::transFormation(Function* F) {}

void MPAvailable::preprocessModule(Module& M) {
  for (Function& F : M) {
    for (Instruction& I : instructions(F)) {
      switch (I.getOpcode()) {
        case Instruction::GetElementPtr:
          preprocessGEP(dyn_cast<GetElementPtrInst>(&I));
          break;
      }
    }
  }
}
bool MPAvailable::isXMMTy(Type* type) {
  // XMM Type 인지, XMMTYPE의 포인터는 FALSE
  if (type->isVectorTy()) {
    VectorType* vt = dyn_cast<VectorType>(type);
    return vt->getElementType()->isIntegerTy(64);
  }
  return false;
}

bool MPAvailable::isXMMPtrTy(Type* type) {
  // XMM Type 인지, XMMTYPE의 포인터는 FALSEf
  if (type->isPointerTy()) {
    PointerType* pt = dyn_cast<PointerType>(type);
    if (isXMMTy(pt->getElementType())) return true;
  }
  return false;
}

Value* MPAvailable::createXmmTag(IRBuilder<>& irb, Value* size,
                                 std::string prefix = "") {
  //이 메소드는 태그만 만듬
  //리턴후에 원래의 offet과 and 해야됨
  // gep 전용
  // size는 64bit
  Constant* nullValue = Constant::getNullValue(XMM);

  Value* tagVal;
  Value* UnderOffset = irb.CreateShl(size, 32, prefix + ".under");

  tagVal = irb.CreateOr(UnderOffset, size, prefix + ".tag");
  irb.CreateInsertElement(nullValue, tagVal, (uint64_t)0);

  Value* sizeAnd =
      irb.CreateAnd(size,
                    ConstantInt::get(IntegerType::get(irb.getContext(), 64),
                                     0xffffffffffffffff),
                    "size");

  Value* result = irb.CreateInsertElement(nullValue, sizeAnd, (uint64_t)1);
  return result;
}

void MPAvailable::handleCall(CallInst* CI) {
  if (!CI) return;
  IRBuilder<> irb(CI);
  Function* calledFunc = CI->getCalledFunction();
  CallBase* cb = CI;

  if (calledFunc->getName() == "free") {
    handleFree(CI);
    return;
  }

  FunctionType* calledFuncType = calledFunc->getFunctionType();

  if (!calledFunc->isDeclaration()) {
    if (transformFunctions.find(calledFunc) != transformFunctions.end()) {
      errs() << "Create New Call! : " << calledFunc->getName() << "\n";
      typePrint(calledFunc->getType(), "Func Type");

      Value* ret = nullptr;
      std::vector<Value*> args;

      for (unsigned int i = 0; i < CI->arg_size(); i++) {
        args.push_back(CI->getArgOperand(i));
        ArrayRef<Value*> array = args;
        Type* fType = calledFuncType->getParamType(i);
        Type* aType = array[i]->getType();
        assert((i <= calledFuncType->getNumParams() || (fType == aType)) &&
               "Calling a function with a bad signature!");
      }

      if (!calledFuncType->getReturnType()->isVoidTy())
        ret = irb.CreateCall(calledFunc, args);
      else {
        CallInst* newCI = irb.CreateCall(calledFunc, args);
        typePrint(CI->getCalledOperand()->getType(), "CI Called Operand");
        typePrint(newCI->getCalledOperand()->getType(),
                  "What is Called Operand()?");
      }
      if (ret != nullptr) {
        CI->replaceAllUsesWith(ret);
      }
      CI->eraseFromParent();
    }
  } else if (calledFunc->isDeclaration()) {
    for (unsigned int i = 0; i < CI->arg_size(); i++) {
      Type* argType;
      if (calledFuncType->isVarArg() && i >= calledFuncType->getNumParams()) {
        argType =
            calledFuncType->getParamType(calledFuncType->getNumParams() - 1);
      } else {
        argType = calledFuncType->getParamType(i);
      }
      Value* arg = CI->getArgOperand(i);
      if (isXMMTy(arg->getType())) {
        Value* noPointer = ununTag(arg, argType, irb, arg->getName().str());
        CI->setArgOperand(i, noPointer);
      }
    }
  }
}
void MPAvailable::debugBCI(BitCastInst* bci) {
  instPrint(bci, "bci print");
  for (User* user : bci->users()) {
    Value* userV = dyn_cast<Value>(user);
    valuePrint(userV, "userV");
  }
}
void MPAvailable::handleFree(CallInst* CI) {
  errs() << "Handle Free\n";
  Function* calledFunc = CI->getCalledFunction();
  IRBuilder<> irb(CI);

  Value* arg = CI->getArgOperand(0);
  valuePrint(arg, "Free");
  Value* unWrapValue;
  if (BitCastInst* bci = dyn_cast<BitCastInst>(arg)) {
    Value* orig = bci->getOperand(0);
    if (isXMMTy(orig->getType())) {
      unWrapValue = ununTag(orig, Type::getInt8PtrTy(CI->getContext()), irb);
      CI->setArgOperand(0, unWrapValue);
      bci->eraseFromParent();
    }
  } else {
    if (!isXMMTy(arg->getType())) return;
    Value* unWrapValue =
        ununTag(arg, Type::getInt8PtrTy(CI->getContext()), irb);
    CI->setArgOperand(0, unWrapValue);
  }

  // irb.CreateStore(xmm_ai, setFlagV);
}

void MPAvailable::preAnalyzeGEP(Function* F) {
  bool changed = true;

  while (changed) {
    changed = false;
    for (Instruction& I : instructions(F)) {
      switch (I.getOpcode()) {
        case Instruction::Alloca:
          if (I.getType()->getPointerElementType()->isPointerTy()) {
            if (instructionToL4.find(&I) == instructionToL4.end()) {
              changed = true;
              instructionToL4.insert(&I);
            }
          }
          break;
        case Instruction::Load:
        case Instruction::GetElementPtr:
          if (Instruction* opInst = dyn_cast<Instruction>(I.getOperand(0))) {
            if (instructionToL4.find(opInst) != instructionToL4.end() &&
                instructionToL4.find(&I) == instructionToL4.end()) {
              changed = true;
              instructionToL4.insert(&I);
            }
          }
          break;
        default:
          continue;
      }
    }
  }
}

void MPAvailable::transformFunction(Function* F) {
  if (F->getName().find("main") != std::string::npos) return;
  if (F->isDeclaration()) return;
  if (transformFunctions.find(F) != transformFunctions.end()) return;
  transformFunctions.insert(F);
  errs() << "Transform Function " << F->getName() << "\n";
  FunctionType* funcType = F->getFunctionType();
  FunctionType* newFuncType;
  std::vector<Type*> plist;
  for (int i = 0; i < funcType->getNumParams(); i++) {
    Type* paramType = funcType->getParamType(i);
    if (paramType->isPointerTy()) {
      plist.push_back(XMM);
    } else
      plist.push_back(paramType);
  }
  newFuncType =
      FunctionType::get(funcType->getReturnType(), plist, funcType->isVarArg());
}
void MPAvailable::createWrappingFunction(Function& F) {
  // if (F.getName().find("main") != std::string::npos) {
  //   usedFunctionPointer.insert(&F);
  //   return;
  // }
  // if (!checkShouldBeWrapped(F)) {
  //   return;
  // }
  bool isNeedTransform = true;
  // if (isUsedFunctionPointer(&F)) {
  //   // usedFunctionPointer.insert(&F);
  //   isNeedTransform = false;
  //   // return;
  // }
  errs() << "Wrapping ... " << F.getName() << "\n";
  // if (isa<Constant>(&F)) return;
  bool mustWrapped = false;

  std::map<Value*, Value*> valToVal;
  std::map<StringRef, int> argToArg;
  std::map<BasicBlock*, BasicBlock*> basicToBasic;
  std::map<Value*, Type*> valToType;
  std::map<Value*, Value*> arrToPtr;
  Function* newFunc = funcToFunc[&F];
  int i = 0;
  // std::vector<Type*> plist;

  if (isNeedTransform) {
    for (Argument& arg : F.args()) {
      Value* vArg = dyn_cast<Value>(&arg);
      if (isFunctionPtrTy(arg.getType())) {
        argToArg[vArg->getName()] = i;
      } else if (arg.getType()->isPointerTy()) {
        argToArg[vArg->getName()] = i;
      } else {
        argToArg.insert(std::pair<StringRef, int>(vArg->getName(), i));
      }
      i++;
    }
  }
  // } else {
  //   for (Argument& arg : F.args()) {
  //     Value* vArg = dyn_cast<Value>(&arg);
  //     argToArg[vArg->getName()] = i;
  //   }
  // }
  for (BasicBlock& BB : F.getBasicBlockList()) {
    BasicBlock* clone =
        BasicBlock::Create(newFunc->getContext(), BB.getName(), newFunc);
    valToVal[&BB] = clone;
    basicToBasic[&BB] = clone;
  }
  for (detail::DenseMapPair<GlobalVariable*, GlobalVariable*> gPair : gToGV) {
    Value* key = gPair.first;
    Value* value = gPair.second;
    valToVal[key] = value;
  }
  for (detail::DenseMapPair<Function*, Function*> fPair : funcToFunc) {
    Value* key = fPair.first;
    Value* value = fPair.second;
    valToVal[key] = value;
  }
  for (BasicBlock& BB : F.getBasicBlockList()) {
    cloneBB(newFunc, &BB, argToArg, valToVal, arrToPtr);
  }

  // replaceFunction(newFunc, &F);
  // F.eraseFromParent();
}

void MPAvailable::replaceFunction(Function* newFunc, Function* oldFunc) {
  errs() << "Replace Function\n";
  for (User* user : oldFunc->users()) {
    if (CallInst* CI = dyn_cast<CallInst>(user)) {
      AttributeList PAL = CI->getAttributes();
      AttributeList newAttr;
      for (unsigned int ArgNo = 0; ArgNo < CI->getNumArgOperands(); ArgNo++) {
        errs() << "What is ATTR?:  "
               << PAL.getAttributes(ArgNo).getNumAttributes() << "\n";
        newAttr = PAL.removeAttributes(CI->getContext(), ArgNo);
      }
      IRBuilder<> irb(CI);
      std::vector<Value*> args;
      for (int i = 0; i < CI->getNumArgOperands(); i++) {
        Value* arg = CI->getArgOperand(i);
        if (isFunctionPtrTy(arg->getType()))
          args.push_back(arg);
        else if (arg->getType()->isPointerTy()) {
          Value* ptrToInt =
              irb.CreatePtrToInt(arg, Type::getInt64Ty(CI->getContext()));
          args.push_back(ptrToInt);
          Value* nullValue =
              Constant::getNullValue(Type::getInt64Ty(CI->getContext()));
          args.push_back(nullValue);
        } else
          args.push_back(arg);
      }
      typePrint(newFunc->getFunctionType(), "newFuncType");
      Value* returnValue = irb.CreateCall(newFunc, args, CI->getName());
      for (User* ciUser : CI->users()) {
        if (Instruction* inst = dyn_cast<Instruction>(ciUser)) {
          for (int i = 0; i < inst->getNumOperands(); i++) {
            if (inst->getOperand(i) == CI) {
              inst->setOperand(i, returnValue);
            }
          }
        }
      }
      const AttrBuilder attrBuilder;
      for (int i = 0; i < args.size(); i++) {
        newAttr =
            newAttr.addAttributes(returnValue->getContext(), i, attrBuilder);
      }
      CallBase* CB = dyn_cast<CallBase>(returnValue);
      CB->setAttributes(PAL);
      CI->eraseFromParent();
      AttributeList Attrs = CI->getAttributes();
      errs() << "Print Attrs Number : " << Attrs.getNumAttrSets() << "\n";

      for (unsigned i = 0; i < Attrs.getNumAttrSets(); ++i) {
        for (Attribute::AttrKind TypedAttr :
             {Attribute::ByVal, Attribute::StructRet, Attribute::ByRef}) {
          errs() << "Test ATTRS:: "
                 << Attrs.getAttribute(i, TypedAttr).getAsString() << "\n";
          // if (Type* Ty = Attrs.getAttribute(i, TypedAttr).getValueAsType())
          // { Attrs = Attrs.replaceAttributeType(CI->getContext(), i,
          // TypedAttr,
          //                                    TypeMapper->remapType(Ty));
          break;
        }
      }

      // CI->setAttributes(Attrs);
    } else {
    }
  }
}
BasicBlock* MPAvailable::cloneBB(Function* cloneFunc, BasicBlock* orig,
                                 std::map<StringRef, int>& argToArg,
                                 std::map<Value*, Value*>& valToVal,
                                 std::map<Value*, Value*>& arrToPtr) {
  BasicBlock* clone = dyn_cast<BasicBlock>(valToVal[orig]);

  IRBuilder<> irb(clone);

  for (Instruction& I : orig->getInstList()) {
    // clone->getInstList().push_back(newInst);
    // Reset the insert point of IRB
    if (cloneFunc->getName() == "Wrapping_hashtable_getlock")
      instPrint(&I, cloneFunc->getName().str());
    switch (I.getOpcode()) {
      case Instruction::Alloca: {
        // PASS
        AllocaInst* allocaInst = dyn_cast<AllocaInst>(&I);
        if (allocaInst->getName() == "saved_stack") {
          Instruction* newInst = I.clone();
          newInst->setName(I.getName());
          valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
          clone->getInstList().push_back(newInst);
          break;
        }
        if (isFunctionPtrTy(allocaInst->getAllocatedType())) {
          FunctionType* ft = dyn_cast<FunctionType>(
              dyn_cast<PointerType>(allocaInst->getAllocatedType())
                  ->getPointerElementType());
          FunctionType* newFt = createFunctionType(ft);
          Value* newInst =
              irb.CreateAlloca(newFt->getPointerTo(), nullptr, I.getName());
          // Instruction* newInst = I.clone();
          newInst->setName(I.getName());
          valToVal[dyn_cast<Value>(&I)] = newInst;
        } else if (allocaInst->getAllocatedType()->isPointerTy()) {
          if (allocaInst->isArrayAllocation()) {
            Value* size = instrumentWithByteSize(irb, &I, valToVal);

            Value* newPointer =
                irb.CreateAlloca(XMM, nullptr, I.getName().str() + ".l4");
            Value* newArray = irb.CreateAlloca(allocaInst->getAllocatedType(),
                                               size, allocaInst->getName());
            Value* OvSz = createMask(irb, size, irb.getContext());
            Value* PtrInt = irb.CreatePtrToInt(newArray, irb.getInt64Ty());
            Value* emptyVec = Constant::getNullValue(XMM);

            Value* vec0 = irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
            Value* vec1 = irb.CreateInsertElement(vec0, PtrInt, 1);

            irb.CreateStore(vec1, newPointer);
            valToVal[dyn_cast<Value>(&I)] = newPointer;
            arrToPtr[dyn_cast<Value>(&I)] = newPointer;
          } else {
            Value* replace = irb.CreateAlloca(XMM, nullptr, I.getName());

            valToVal[dyn_cast<Value>(&I)] = replace;
          }
        } else if (allocaInst->getAllocatedType()->isArrayTy()) {
          Value* newArray = irb.CreateAlloca(allocaInst->getAllocatedType(),
                                             nullptr, allocaInst->getName());

          Value* newPointer =
              irb.CreateAlloca(XMM, nullptr, I.getName().str() + ".l4.arrayty");
          AllocaInst* newAI = dyn_cast<AllocaInst>(newArray);
          newAI->setAlignment(allocaInst->getAlign());

          Type* type = allocaInst->getAllocatedType();
          ArrayType* arrType = dyn_cast<ArrayType>(type);
          Value* arrTypeSize = irb.getInt64(
              DL->getTypeAllocSize(arrType->getArrayElementType()));
          Value* arrSize = irb.getInt64(arrType->getArrayNumElements());
          Value* allocSize = irb.CreateMul(arrTypeSize, arrSize);

          Value* OvSz = createMask(irb, allocSize, irb.getContext());
          Value* PtrInt = irb.CreatePtrToInt(newArray, irb.getInt64Ty());
          Value* emptyVec = Constant::getNullValue(XMM);

          Value* vec0 = irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
          Value* vec1 = irb.CreateInsertElement(vec0, PtrInt, 1);

          irb.CreateStore(vec1, newPointer);
          valToVal[dyn_cast<Value>(&I)] = newPointer;
          arrToPtr[dyn_cast<Value>(&I)] = newPointer;
        } else if (allocaInst->isArrayAllocation()) {
          Value* size = instrumentWithByteSize(irb, &I, valToVal);

          Value* newPointer =
              irb.CreateAlloca(XMM, nullptr, I.getName().str() + ".l4");
          Value* newArray = irb.CreateAlloca(allocaInst->getAllocatedType(),
                                             size, allocaInst->getName());
          Value* OvSz = createMask(irb, size, irb.getContext());
          Value* PtrInt = irb.CreatePtrToInt(newArray, irb.getInt64Ty());
          Value* emptyVec = Constant::getNullValue(XMM);

          Value* vec0 = irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
          Value* vec1 = irb.CreateInsertElement(vec0, PtrInt, 1);

          irb.CreateStore(vec1, newPointer);
          valToVal[dyn_cast<Value>(&I)] = newPointer;
          arrToPtr[dyn_cast<Value>(&I)] = newPointer;
        } else if (allocaInst->getAllocatedType()->isStructTy()) {
          StructType* st = dyn_cast<StructType>(allocaInst->getAllocatedType());
          if (strucTyToStructTy.count(st) > 0) {
            StructType* newSt = strucTyToStructTy[st];
            Value* newAlloc = irb.CreateAlloca(newSt, nullptr, I.getName());
            valToVal[dyn_cast<Value>(&I)] = newAlloc;
          } else {
            Instruction* newInst = I.clone();
            newInst->setName(I.getName());
            valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
            clone->getInstList().push_back(newInst);
          }
        } else {
          Instruction* newInst = I.clone();
          newInst->setName(I.getName());
          valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
          clone->getInstList().push_back(newInst);
        }

        break;
      }
      case Instruction::Store: {
        Value* v0 = I.getOperand(0);  // value
        Value* v1 = valToVal.count(I.getOperand(1)) > 0
                        ? valToVal[I.getOperand(1)]
                        : I.getOperand(1);  // pointer
        if (argToArg.count(v0->getName())) {
          // Argument를 저장하는 과정
          // Argument 저장 통과
          int index = argToArg[v0->getName()];

          if (v0->getType()->isPointerTy()) {
            if (isFunctionPtrTy(v0->getType())) {
              Value* arg = cloneFunc->getArg(index);
              irb.CreateStore(arg, v1);
              break;
            }
            if (AllocaInst* newAI = dyn_cast<AllocaInst>(I.getOperand(1))) {
              Value* tag = cloneFunc->getArg(index);
              Value* bitcast = irb.CreateBitCast(tag, XMM_POINTER);
              Value* loadArg = irb.CreateLoad(bitcast);
              irb.CreateStore(loadArg, v1);
              // Value* ptr = cloneFunc->getArg(index + 1);
              // Value* nullL4 = Constant::getNullValue(XMM);
              // Value* tagVec = irb.CreateInsertElement(nullL4, tag,
              // (uint64_t)0); Value* ptrToInt =
              //     irb.CreatePtrToInt(ptr,
              //     Type::getInt64Ty(ptr->getContext()));
              // Value* L4 = irb.CreateInsertElement(tagVec, ptrToInt, 1);

              // Instruction* inst = dyn_cast<Instruction>(v1);
              // irb.CreateStore(L4, v1);
            } else if (isXMMPtrTy(v1->getType())) {
              // Value* tag = cloneFunc->getArg(index);

              // Value* ptr = cloneFunc->getArg(index + 1);
              // Value* nullL4 = Constant::getNullValue(XMM);
              // Value* tagVec = irb.CreateInsertElement(nullL4, tag,
              // (uint64_t)0); Value* ptrToInt =
              //     irb.CreatePtrToInt(ptr,
              //     Type::getInt64Ty(ptr->getContext()));
              // Value* L4 = irb.CreateInsertElement(tagVec, ptrToInt, 1);

              // Instruction* inst = dyn_cast<Instruction>(v1);
              Value* tag = cloneFunc->getArg(index);
              Value* bitcast = irb.CreateBitCast(tag, XMM_POINTER);
              Value* loadArg = irb.CreateLoad(bitcast);
              irb.CreateStore(loadArg, v1);
            } else if (isXMMTy(v1->getType())) {
              Value* ptr = cloneFunc->getArg(index);
              Value* newV1 = ununTag(v1, I.getOperand(1)->getType(), irb);
              irb.CreateStore(ptr, newV1);
            } else {
              // v1 is pointer Ty;
              Value* ptr = cloneFunc->getArg(index);

              Value* intToPtr = irb.CreateIntToPtr(
                  ptr, v1->getType()->getPointerElementType());
              irb.CreateStore(intToPtr, v1);
            }
          } else {
            Value* arg = cloneFunc->getArg(index);
            instPrint(&I, "arg I ");
            irb.CreateStore(arg, v1);
          }

          break;
        }

        Value* value = I.getOperand(0);
        Value* pointer = I.getOperand(1);
        if (valToVal.count(pointer) > 0) {
          Value* newPointer = valToVal[pointer];
          Value* newValue;

          if (valToVal.count(value) > 0)
            newValue = valToVal[value];
          else
            newValue = value;  // value is Constant
          // if(!newPointer ) newPointer = pointer;

          if (value->getType()->isPointerTy()) {
            // double pointer 인 경우
            // value 가 포인터인 경우를 여기서 처리하게 바꾸자
            // 밑에 있는 코드를 위로 끌어오기
            // null 넣는 코드는 밑에 있음
            if (isXMMTy(newValue->getType())) {
              if (isXMMTy(newPointer->getType())) {
                Value* replacePointer = ununTag(newPointer, XMM_POINTER, irb);
                irb.CreateStore(newValue, replacePointer);
                // Value* replaceValue = ununTag(newValue, value->getType(),
                // irb);

                // Value* replacePointer = ununTag(
                //     newPointer, replaceValue->getType()->getPointerTo(),
                //     irb);
                // // valuePrintGenerate(newPointer, irb);
                // typePrint(replaceValue->getType(), "replaceValue");
                // typePrint(replacePointer->getType(), "replacePointer");
                // irb.CreateStore(replaceValue, replacePointer);
              } else if (isXMMPtrTy(newPointer->getType())) {
                // valuePrintGenerate(newPointer, irb);
                irb.CreateStore(newValue, newPointer);
              } else {
                // Pointer is not XMM TYPE
                // so value untag
                Value* replaceValue = ununTag(newValue, value->getType(), irb);

                if (replaceValue->getType()->getPointerTo() !=
                    newPointer->getType()) {
                  newPointer = irb.CreateBitCast(
                      newPointer, replaceValue->getType()->getPointerTo());
                }
                // valuePrintGenerate(newPointer, irb);
                irb.CreateStore(replaceValue, newPointer);
              }
            } else {
              if (isXMMTy(newPointer->getType())) {
                Value* replacePointer = ununTag(
                    newPointer, newValue->getType()->getPointerTo(), irb);
                // valuePrintGenerate(replacePointer, irb);
                irb.CreateStore(newValue, replacePointer);
              } else if (isXMMPtrTy(newPointer->getType())) {
                Value* castVal = newValue;
                if (!newValue->getType()->isIntegerTy()) {
                  castVal = irb.CreatePtrToInt(newValue, irb.getInt64Ty());
                }
                Constant* nullVec = Constant::getNullValue(XMM);
                Constant* nullValue = Constant::getNullValue(
                    Type::getInt64Ty(clone->getContext()));
                Value* vec1 =
                    irb.CreateInsertElement(nullVec, nullValue, uint64_t(0));
                Value* vec2 =
                    irb.CreateInsertElement(vec1, castVal, uint64_t(1));
                irb.CreateStore(vec2, newPointer);
              } else if (isFunctionPtrTy(newValue->getType())) {
              } else {
                // Ex) store i8* %84, i8** %saved_stack, align 8
                irb.CreateStore(newValue, newPointer);
              }
            }
          } else if (isXMMTy(newPointer->getType())) {
            // 통과

            Value* clearTag = ununTag(newPointer, pointer->getType(), irb);
            if (isXMMTy(newValue->getType())) {
              Value* clearVal = ununTag(newValue, value->getType(), irb);

              irb.CreateStore(clearVal, clearTag);
            } else
              irb.CreateStore(newValue, clearTag);
          } else {
            if (isXMMTy(newPointer->getType()->getPointerElementType())) {
              // 포인터의 element type이 XMM type임
              if (isXMMTy(newValue->getType())) {
                irb.CreateStore(newValue, newPointer);
              } else {
                Value* castVal = newValue;
                if (!newValue->getType()->isIntegerTy()) {
                  castVal = irb.CreatePtrToInt(newValue, irb.getInt64Ty());
                }
                Constant* nullVec = Constant::getNullValue(XMM);
                Constant* nullValue = Constant::getNullValue(
                    Type::getInt64Ty(clone->getContext()));
                Value* vec1 =
                    irb.CreateInsertElement(nullVec, nullValue, uint64_t(0));
                Value* vec2 =
                    irb.CreateInsertElement(vec1, castVal, uint64_t(1));
                irb.CreateStore(vec2, newPointer);
              }
            } else {
              // 이 경우 거의 더블 포인터

              if (isXMMTy((newValue->getType()))) {
                Value* replaceValue =
                    ununTag(newValue, I.getOperand(0)->getType(), irb);

                irb.CreateStore(replaceValue, newPointer);
              } else {
                StoreInst* si = irb.CreateStore(newValue, newPointer);
              }
            }
          }
        } else {
          // 글로벌 변수
          // ptr이 글로벌 변수
          //
          // 글로벌도 이제 그냥 변수처럼 취급해주기
          // 다 바꿨으니까

          StoreInst* si = dyn_cast<StoreInst>(&I);
          Value* ptr = si->getPointerOperand();
          if (GlobalVariable* gv = dyn_cast_or_null<GlobalVariable>(ptr)) {
            Value* value = si->getValueOperand();
            Value* newValue = valToVal.count(value) ? valToVal[value] : value;

            if (gToGV.count(gv) > 0) {
              errs() << " 여기다\n";
              exit(0);
            }
            if (isXMMTy(newValue->getType())) {
              newValue = ununTag(newValue, value->getType(), irb);
            }

            irb.CreateStore(newValue, ptr);
          } else {
            // Ptr is ConstantExpr.
            Value* newValue = valToVal.count(value) ? valToVal[value] : value;

            StoreInst* si = irb.CreateStore(newValue, ptr);
          }
        }
        break;
      }
      case Instruction::Load: {
        // Load 는 오히려 심플
        Value* origPointer = I.getOperand(0);

        if (valToVal.count(origPointer) > 0) {
          Value* pointer = valToVal[origPointer];
          if (isXMMTy(pointer->getType())) {
            // 여기서 포인터의 포인터일경우 에는 다르게 해야함
            Type* loadType = origPointer->getType();
            Value* clearTagPointer;
            if (I.getType()->isPointerTy() && !isFunctionPtrTy(I.getType())) {
              clearTagPointer =
                  ununTag(pointer, XMM_POINTER, irb,
                          origPointer->hasName()
                              ? origPointer->getName().str() + "XMM_POINTER_GET"
                              : "XMM_POINTER_GET");
              // clearTagPointer = ununTag(
              //     pointer, loadType, irb,
              //     origPointer->hasName() ? origPointer->getName().str() :
              //     "");
            } else {
              clearTagPointer = ununTag(
                  pointer, loadType, irb,
                  origPointer->hasName() ? origPointer->getName().str() : "");
            }
            Value* replaceInst;

            replaceInst = irb.CreateLoad(clearTagPointer,
                                         origPointer->hasName()
                                             ? origPointer->getName().str()
                                             : "unwrap_pointer");

            valToVal[dyn_cast<Value>(&I)] = replaceInst;
          } else {
            Value* newLoad = irb.CreateLoad(pointer);
            valToVal[dyn_cast<Value>(&I)] = newLoad;
          }
        } else {
          Value* op = I.getOperand(0);
          if (GlobalValue* gv = dyn_cast_or_null<GlobalValue>(op)) {
            Instruction* newInst = I.clone();
            clone->getInstList().push_back(newInst);
            valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
          } else {
            // 찾앗다 시발
            // example  %95 = load i32, i32* getelementptr inbounds
            // (%struct.stats_t, %struct.stats_t* @stats, i32 0, i32 5), align
            // 8 ConstantExpr
            Instruction* newInst = I.clone();
            clone->getInstList().push_back(newInst);
            valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
          }
        }

        break;
      }
      case Instruction::GetElementPtr: {
        // 일단 GEP-> 타겟 포인터
        // GEP 복사 X
        // GEP의 Base Pointer 가 Struct Type 이라면,
        // Struct -> Struct' 로 매핑 (Struct 는 원래의 Struct, 변형된 것이
        // Struct') Struct' 의 멤버로 매핑되게... 하기 Struct' 의 멤버가
        // Double Pointer 에 대해서 하는 방법 생각하기

        GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(&I);
        Value* base = gep->getPointerOperand();
        Value* realBase = gep->getPointerOperand();

        if (fixGEPforStruct(gep, valToVal, irb)) {
          break;
        }
        if (valToVal.count(base) > 0) {
          // 여기는 변환되지 않은 구조체들에 대해서 처리 하는 곳
          PointerType* baseType = dyn_cast<PointerType>(base->getType());
          Value* tempPointer = valToVal[base];
          if (argToArg.count(tempPointer->getName())) {
            // argument
            // by value
            std::vector<Value*> plist;

            for (auto i = gep->idx_begin(); i != gep->idx_end(); i++) {
              Value* val = *i;
              if (valToVal.count(val) > 0) {
                plist.push_back(valToVal[val]);
              } else {
                plist.push_back(val);
              }
            }
            Value* newGEP;
            if (gep->isInBounds()) {
              newGEP = irb.CreateInBoundsGEP(
                  tempPointer, plist,
                  gep->hasName() ? gep->getName() + "arg" : "arg");
            } else {
              newGEP = irb.CreateGEP(
                  tempPointer, plist,
                  gep->hasName() ? gep->getName() + "arg" : "arg");
            }
            valToVal[gep] = newGEP;
            break;
          }
          if (baseType->getPointerElementType()->isStructTy()) {
            // 이것도 마찬가지
            // SSA의 특성을 이용하자
            StructType* origStruct =
                dyn_cast<StructType>(baseType->getPointerElementType());

            StructType* newStruct = origStruct;
            Value* newBase = valToVal[base];
            if (isXMMTy(newBase->getType())) {
              Value* unTagBase =
                  ununTag(newBase, newStruct->getPointerTo(), irb, "here?");
              std::vector<Value*> plist;
              for (auto i = gep->idx_begin(); i != gep->idx_end(); i++) {
                Value* val = *i;
                if (valToVal.count(val) > 0) {
                  plist.push_back(valToVal[val]);
                } else {
                  plist.push_back(val);
                }
              }
              if (gep->isInBounds()) {
                Value* newGEP = irb.CreateInBoundsGEP(
                    unTagBase, plist,
                    gep->hasName() ? gep->getName() + "struct.inbound"
                                   : "struct.inbound");
                GetElementPtrInst* NewGEP = dyn_cast<GetElementPtrInst>(newGEP);

                assertGEP(newGEP);
                valToVal[dyn_cast<Value>(&I)] = newGEP;
              } else {
                Value* newGEP = irb.CreateGEP(unTagBase, plist);
                assertGEP(newGEP);
                valToVal[dyn_cast<Value>(&I)] = newGEP;
              }
            } else {
              Value* newBase = valToVal[base];
              if (arrToPtr.count(base) > 0) {
                Value* wrapPtr = arrToPtr[base];
                Value* l4Ptr = irb.CreateLoad(wrapPtr);
                Value* unWrapPtr = ununTag(l4Ptr, base->getType(), irb);

                Value* offset = emitGEPOffset(irb, *DL, gep, valToVal);

                Constant* nullVec = Constant::getNullValue(XMM);
                Value* tag = createOffsetMask(irb, offset);
                Value* v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
                Value* v1 = irb.CreateInsertElement(v0, offset, 1);
                Value* replaceInst =
                    irb.CreateAdd(l4Ptr, v1,
                                  gep->hasName() ? gep->getName() + ".array"
                                                 : l4Ptr->getName() + ".array");
                valToVal[dyn_cast<Value>(&I)] = replaceInst;
              } else {
                std::vector<Value*> plist;
                for (auto i = gep->idx_begin(); i != gep->idx_end(); i++) {
                  Value* val = *i;
                  if (valToVal.count(val) > 0)
                    plist.push_back(valToVal[val]);
                  else
                    plist.push_back(val);
                }
                if (gep->isInBounds()) {
                  // 문제 찾았음 여기가 문제고

                  Value* newGEP =
                      irb.CreateInBoundsGEP(newBase, plist, "HERE.PROBLEM");
                  assertGEP(newGEP);
                  valToVal[dyn_cast<Value>(&I)] = newGEP;
                } else {
                  Value* newGEP = irb.CreateGEP(newBase, plist);
                  assertGEP(newGEP);
                  valToVal[dyn_cast<Value>(&I)] = newGEP;
                }
              }
            }
          } else if (base->getType()->getPointerElementType()->isArrayTy()) {
            if (arrToPtr.count(base)) {
              Value* wrapPtr = arrToPtr[base];
              Value* l4Ptr = irb.CreateLoad(wrapPtr);
              Value* unWrapPtr = ununTag(l4Ptr, base->getType(), irb);

              Value* offset = emitGEPOffset(irb, *DL, gep, valToVal);

              Constant* nullVec = Constant::getNullValue(XMM);
              Value* tag = createOffsetMask(irb, offset);
              Value* v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
              Value* v1 = irb.CreateInsertElement(v0, offset, 1);
              Value* replaceInst =
                  irb.CreateAdd(l4Ptr, v1,
                                gep->hasName() ? gep->getName() + ".array"
                                               : l4Ptr->getName() + ".array");
              valToVal[dyn_cast<Value>(&I)] = replaceInst;
            } else {
              //이 경우 ARRAY 인데 구조체의 배열일경우에 여기로 옴
              // 그냥 똑같이 해야할 듯
              // 여기서 그거 구현해서 할라면 할 수 있음
              // 하지만 안함
              Value* newBase = valToVal[base];
              if (isXMMTy(newBase->getType())) {
                Value* newGEP = splatGEP(gep, valToVal, irb);
                valToVal[dyn_cast<Value>(gep)] = newGEP;
                break;
              }
              if (gep->isInBounds()) {
                Value* newBase = valToVal[base];
                std::vector<Value*> plist;
                for (auto i = gep->idx_begin(); i != gep->idx_end(); i++) {
                  Value* val = *i;
                  Type* type = gep->getTypeAtIndex(
                      cast<PointerType>(
                          gep->getPointerOperand()->getType()->getScalarType())
                          ->getElementType(),
                      val);
                  if (valToVal.count(val) > 0)
                    plist.push_back(valToVal[val]);
                  else
                    plist.push_back(val);
                }
                instPrint(&I, "I");
                Value* newGEP = irb.CreateInBoundsGEP(newBase, plist, "ARRAY");
                assertGEP(newGEP);
                valToVal[dyn_cast<Value>(gep)] = newGEP;
              }
            }

          } else if (AllocaInst* ai = dyn_cast<AllocaInst>(base)) {
            if (ai->getAllocatedType()->isArrayTy()) {
              Value* wrapPtr = arrToPtr[base];
              Value* l4Ptr = irb.CreateLoad(wrapPtr);
              Value* unWrapPtr = ununTag(l4Ptr, base->getType(), irb);

              Value* offset = emitGEPOffset(irb, *DL, gep, valToVal);

              Constant* nullVec = Constant::getNullValue(XMM);
              Value* tag = createOffsetMask(irb, offset);
              Value* v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
              Value* v1 = irb.CreateInsertElement(v0, offset, 1);
              Value* replaceInst =
                  irb.CreateAdd(l4Ptr, v1,
                                gep->hasName() ? gep->getName() + ".array"
                                               : l4Ptr->getName() + ".array");
              valToVal[dyn_cast<Value>(&I)] = replaceInst;
            } else if (ai->isArrayAllocation()) {
              Value* wrapPtr = arrToPtr[base];
              Value* l4Ptr = irb.CreateLoad(wrapPtr);

              Value* offset = emitGEPOffset(irb, *DL, gep, valToVal);

              Constant* nullVec = Constant::getNullValue(XMM);
              Value* tag = createOffsetMask(irb, offset);
              Value* v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
              Value* v1 = irb.CreateInsertElement(v0, offset, 1);
              Value* replaceInst = irb.CreateAdd(
                  l4Ptr, v1,
                  gep->hasName() ? gep->getName() : l4Ptr->getName() + ".idx");
              valToVal[dyn_cast<Value>(&I)] = replaceInst;
            } else {
              // 레퍼런스 변수 일수도 있음
              errs() << "error!\n";
              exit(0);
            }
          } else {
            // 배열도 아니고
            // 구조체도 아닌 곳
            Value* newBase = valToVal[base];

            if (isXMMPtrTy(newBase->getType())) {
              Value* offset = emitGEPOffset(irb, *DL, gep, valToVal);
              Value* ConstOffset = nullptr;
              bool isPositive = hasNegativeOffset(gep);

              Constant* nullVec = Constant::getNullValue(XMM);
              Value* tag = createOffsetMask(irb, offset);
              Value* v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
              Value* v1 = irb.CreateInsertElement(v0, offset, 1);
              Value* replaceInst =
                  irb.CreateAdd(newBase, v1,
                                gep->hasName() ? gep->getName()
                                               : newBase->getName() + ".idx");

              valToVal[dyn_cast<Value>(&I)] = replaceInst;
            } else if (isXMMTy(newBase->getType())) {
              Value* unTagBase =
                  ununTag(newBase, base->getType(), irb, "100.here");
              std::vector<Value*> plist;
              for (auto i = gep->idx_begin(); i != gep->idx_end(); i++) {
                Value* val = *i;
                if (valToVal.count(val) > 0)
                  plist.push_back(valToVal[val]);
                else
                  plist.push_back(val);
              }
              Value* newGEP;
              if (gep->isInBounds()) {
                newGEP = irb.CreateInBoundsGEP(unTagBase, plist);
                assertGEP(newGEP);
              } else {
                newGEP = irb.CreateGEP(unTagBase, plist);
                assertGEP(newGEP);
              }

              Value* offset = emitGEPOffset(irb, *this->DL, gep, valToVal);
              Constant* nullVec = Constant::getNullValue(XMM);
              Value* tag = createOffsetMask(irb, offset);
              Value* v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
              Value* v1 = irb.CreateInsertElement(v0, offset, 1);
              Value* replaceInst =
                  irb.CreateAdd(newBase, v1,
                                gep->hasName() ? gep->getName()
                                               : newBase->getName() + ".idx");
              valToVal[dyn_cast<Value>(&I)] = replaceInst;

            } else {
              std::vector<Value*> plist;
              for (auto i = gep->idx_begin(); i != gep->idx_end(); i++) {
                Value* val = *i;
                Type* type = gep->getTypeAtIndex(
                    cast<PointerType>(
                        gep->getPointerOperand()->getType()->getScalarType())
                        ->getElementType(),
                    val);
                if (valToVal.count(val) > 0)
                  plist.push_back(valToVal[val]);
                else
                  plist.push_back(val);
              }
              if (gep->isInBounds()) {
                Value* newGEP =
                    irb.CreateInBoundsGEP(newBase, plist, "isDouble?");
                assertGEP(newGEP);
                valToVal[dyn_cast<Value>(&I)] = newGEP;
              } else {
                Value* newGEP = irb.CreateGEP(newBase, plist);
                assertGEP(newGEP);
                valToVal[dyn_cast<Value>(&I)] = newGEP;
              }
            }
          }
        } else {
          // Base Pointer is global variable;
          // Value* newBase = valToVal[base];
          std::vector<Value*> plist;
          for (auto i = gep->idx_begin(); i != gep->idx_end(); i++) {
            Value* val = *i;
            if (valToVal.count(val) > 0)
              plist.push_back(valToVal[val]);
            else
              plist.push_back(val);
          }
          if (gep->isInBounds()) {
            // valuePrint(newBase, "newBase");
            Value* newGEP = irb.CreateInBoundsGEP(base, plist, "global");
            assertGEP(newGEP);
            valToVal[dyn_cast<Value>(&I)] = newGEP;
          } else {
            Value* newGEP = irb.CreateGEP(base, plist);
            assertGEP(newGEP);
            valToVal[dyn_cast<Value>(&I)] = newGEP;
          }
        }
        break;
      }
      case Instruction::Call: {
        CallInst* CI = dyn_cast<CallInst>(&I);
        Function* callee = CI->getCalledFunction();
        Instruction* cloneI;
        if (!callee) {
          // if callee is null, callee is declaration.
          // 왜 인지 모르겠으나 declaration 함수가  null 인 경우가 있음
          // 이제 왜인지 알지
          // Caller에 해당하는 opearand가 ConstantExpr 인 경우임

          // cloneI = I.clone();
          // clone->getInstList().push_back(cloneI);

          Value* newCons;
          std::vector<Value*> args;
          for (unsigned int i = 0; i < CI->getNumArgOperands(); i++) {
            Value* arg = CI->getArgOperand(i);
            if (valToVal.count(arg) > 0) {
              Value* newArg = valToVal[arg];
              valuePrint(newArg, "newArg");
              if (isXMMPtrTy(newArg->getType())) {
                if (arrToPtr.count(arg) > 0) {
                  Value* wrapPtr = arrToPtr[arg];
                  Value* l4Ptr = irb.CreateLoad(wrapPtr);
                  Value* unWrapPtr = ununTag(l4Ptr, arg->getType(), irb);
                  args.push_back(unWrapPtr);
                } else {
                  Value* ptr = irb.CreateBitCast(
                      newArg, irb.getInt64Ty()->getPointerTo());
                  Value* idx = ConstantInt::get(irb.getInt64Ty(), 1);
                  Value* newPtr =
                      irb.CreateInBoundsGEP(irb.getInt64Ty(), ptr, idx);
                  Value* newInsertArg =
                      irb.CreateBitCast(newPtr, arg->getType(), "HERE");
                  args.push_back(newInsertArg);
                }
              } else if (isXMMTy(newArg->getType())) {
                Value* tempArg = irb.CreateAlloca(XMM, nullptr, "temp.arg");
                irb.CreateStore(newArg, tempArg);

                Value* p = irb.CreateBitCast(tempArg, arg->getType());
                args.push_back(p);
              } else
                args.push_back(newArg);
            } else
              args.push_back(arg);
          }
          if (ConstantExpr* cExpr =
                  dyn_cast<ConstantExpr>(CI->getCalledOperand())) {
            switch (cExpr->getOpcode()) {
              case Instruction::BitCast:
                Value* op;
                if (valToVal.count(cExpr->getOperand(0)) > 0)
                  op = valToVal[cExpr->getOperand(0)];
                else
                  op = cExpr->getOperand(0);
                newCons = ConstantExpr::getBitCast(dyn_cast<Constant>(op),
                                                   cExpr->getType());
                break;
              default:
                break;
            }
          } else if (Value* calleeVal =
                         dyn_cast<Value>(CI->getCalledOperand())) {
            newCons = valToVal[calleeVal];
          }
          FunctionType* ft = dyn_cast<FunctionType>(newCons->getType());
          instPrint(CI, "CallInst");

          typePrint(CI->getFunctionType(), "callee");
          valuePrint(newCons, "newCons");
          Value* newCI = irb.CreateCall(CI->getFunctionType(), newCons, args,
                                        CI->getName());
          valToVal[dyn_cast<Value>(CI)] = newCI;

          break;
        }
        if (callee->isDeclaration()) {
          // 포인터들 다 언랩핑하기
          // 여기서는 오퍼랜드만 교체하기

          // 순서만 바꾸면 될듯
          cloneI = I.clone();
          clone->getInstList().push_back(cloneI);
          bool isPthread = false;
          CI = dyn_cast<CallInst>(cloneI);
          for (unsigned int i = 0; i < CI->getNumArgOperands(); i++) {
            Value* arg = CI->getArgOperand(i);
            if (arg->getType()->isPointerTy()) {
              PointerType* pt = dyn_cast<PointerType>(arg->getType());
              if (pt->getPointerElementType()->isFunctionTy()) isPthread = true;
            }
          }
          if (CI->getCalledFunction()->getName() == "pthread_create")
            isPthread = true;

          IRBuilder<> tempIRB(cloneI);
          if (isPthread) {
            for (unsigned int i = 0; i < CI->getNumArgOperands(); i++) {
              Value* arg = CI->getArgOperand(i);
              Value* newOp;
              switch (i) {
                case 0:
                case 1: {
                  if (valToVal.count(arg) > 0) {
                    Value* newArg = valToVal[arg];
                    if (isXMMTy(newArg->getType())) {
                      newOp = ununTag(newArg, arg->getType(), tempIRB);

                    } else {
                      newOp = newArg;
                    }

                  } else {
                    newOp = arg;
                  }

                  CI->setOperand(i, newOp);

                  break;
                }

                case 2: {
                  if (valToVal.count(arg) > 0) {
                    newOp = valToVal[arg];
                  } else {
                    // arg is global function
                    newOp = arg;
                  }
                  CI->setOperand(i, newOp);
                  break;
                }
                case 3: {
                  if (valToVal.count(arg) > 0) {
                    Value* newArg = valToVal[arg];
                    if (isXMMTy(newArg->getType())) {
                      Value* tempArg =
                          tempIRB.CreateAlloca(XMM, nullptr, "temp.arg");
                      tempIRB.CreateStore(newArg, tempArg);
                      newOp = tempIRB.CreateBitCast(tempArg, arg->getType());
                    } else {
                      Constant* nullXMM = Constant::getNullValue(XMM);
                      Value* intToPtr = tempIRB.CreatePtrToInt(
                          newArg, Type::getInt64Ty(arg->getContext()));
                      Value* newArg = tempIRB.CreateInsertElement(
                          nullXMM, intToPtr, (uint64_t)1);
                      Value* tempArg =
                          tempIRB.CreateAlloca(XMM, nullptr, "temp.arg");
                      tempIRB.CreateStore(newArg, tempArg);
                      newOp = tempIRB.CreateBitCast(tempArg, arg->getType());
                    }
                  } else {
                    Constant* nullXMM = Constant::getNullValue(XMM);

                    Value* tempArg =
                        tempIRB.CreateAlloca(XMM, nullptr, "temp.arg");
                    tempIRB.CreateStore(arg, tempArg);
                    newOp = tempIRB.CreateBitCast(tempArg, arg->getType());
                  }
                  CI->setOperand(i, newOp);
                  break;
                }
                default: {
                  if (valToVal.count(arg) > 0) {
                  } else {
                  }
                  break;
                }
              }
            }
            break;
          }
          for (unsigned int i = 0; i < CI->getNumArgOperands(); i++) {
            Value* arg = CI->getArgOperand(i);

            if (valToVal.count(arg) > 0) {
              Value* newArg = valToVal[arg];
              if (arg->getType()->isPointerTy()) {
                if (isXMMTy(newArg->getType())) {
                  Value* newOp;

                  newOp = ununTag(newArg, arg->getType(), tempIRB);
                  CI->setArgOperand(i, newOp);
                } else if (Function* funcPointer = dyn_cast<Function>(newArg)) {
                  CI->setArgOperand(i, newArg);
                } else if (isXMMPtrTy(newArg->getType())) {
                  // untag  안하는 이유
                  // int * a;
                  // &a가 인자로 넘어가서
                  // if(arrToPtr.count(arg) > 0){
                  //   // 배열 언랩핑후 하면 됨

                  // } else {
                  //   // not array
                  // }

                  if (arrToPtr.count(arg) > 0) {
                    Value* wrapPtr = arrToPtr[arg];
                    Value* l4Ptr = tempIRB.CreateLoad(wrapPtr);
                    Value* unWrapPtr = ununTag(l4Ptr, arg->getType(), tempIRB);
                    CI->setArgOperand(i, unWrapPtr);
                  } else {
                    std::list<Value*> plist;
                    Value* idx = ConstantInt::get(irb.getInt64Ty(), 1);
                    // Value* newPtr = irb.CreateInBoundsGEP(
                    //     irb.getInt64Ty()->getPointerTo(), newArg, idx);
                    IRBuilder<> tempIRB(getInsertPointBefore(CI));
                    Value* newPtr =
                        tempIRB.CreateBitCast(newArg, arg->getType(), "HERE2");
                    CI->setArgOperand(i, newPtr);
                  }
                } else {
                  if (isPthread) {
                  } else {
                    CI->setArgOperand(i, newArg);
                  }
                }
              } else {
                if (isXMMPtrTy(newArg->getType())) {
                  // untag  안하는 이유
                  // int * a;
                  // &a가 인자로 넘어가서
                  // if(arrToPtr.count(arg) > 0){
                  //   // 배열 언랩핑후 하면 됨

                  // } else {
                  //   // not array
                  // }

                  if (arrToPtr.count(arg) > 0) {
                    Value* wrapPtr = arrToPtr[arg];
                    Value* l4Ptr = tempIRB.CreateLoad(wrapPtr);
                    Value* unWrapPtr = ununTag(l4Ptr, arg->getType(), tempIRB);
                    CI->setArgOperand(i, unWrapPtr);
                  } else {
                    std::list<Value*> plist;
                    Value* idx = ConstantInt::get(irb.getInt64Ty(), 1);
                    // Value* newPtr = irb.CreateInBoundsGEP(
                    //     irb.getInt64Ty()->getPointerTo(), newArg, idx);
                    IRBuilder<> tempIRB(getInsertPointBefore(CI));
                    Value* newPtr =
                        tempIRB.CreateBitCast(newArg, arg->getType(), "HERE2");
                    CI->setArgOperand(i, newPtr);
                  }
                } else
                  CI->setArgOperand(i, newArg);
              }
            }
          }
          valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(cloneI);
          // malloc 때문에 break; 안함

          if (isAllocation(&I)) {
            Value* ptr = dyn_cast<Value>(cloneI);  // maskMallocWrapper(irb, I);

            if (isStackValue(&I)) break;
            Value* Size = instrumentWithByteSize(
                irb, dyn_cast<Instruction>(valToVal[dyn_cast<Value>(&I)]),
                valToVal);
            if (isMalloc(callee)) {
              bool isNeedFix = fixParamAllocInst(I, valToVal, irb, true);
              if (isNeedFix) {
                cloneI->eraseFromParent();
                Size = instrumentWithByteSize(
                    irb, dyn_cast<Instruction>(valToVal[dyn_cast<Value>(&I)]),
                    valToVal);
              }
              ptr = valToVal[dyn_cast<Value>(&I)];
              Instruction* next = I.getNextNode();

              Value* allocaVar;
              BitCastInst* bci = nullptr;
              Instruction* origStore;

              //일단 태그 만들기

              Value* OvSz = createMask(irb, Size, module->getContext());
              Value* PtrInt = irb.CreatePtrToInt(ptr, irb.getInt64Ty());
              Value* emptyVec = Constant::getNullValue(XMM);

              Value* vec0 =
                  irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
              Value* vec1 =
                  irb.CreateInsertElement(vec0, PtrInt, 1, "malloc.result");
              valToVal[dyn_cast<Value>(&I)] = vec1;
            } else if (isRealloc(callee)) {
              // 여기서 스토어까지 다해야됨
              CallInst* origCI = dyn_cast<CallInst>(&I);

              Value* arg1 = origCI->getArgOperand(0);
              Value* arg2 = CI->getArgOperand(1);

              if (isXMMTy(arg1->getType())) {
                Value* OvSz = createMask(irb, Size, module->getContext());
                Value* idx = ConstantInt::get(irb.getInt64Ty(), 1);

                Value* newTagAddress =
                    irb.CreateInBoundsGEP(irb.getInt64Ty()->getPointerTo(),
                                          CI->getArgOperand(0), idx);
                Instruction* newStore = irb.CreateStore(OvSz, newTagAddress);
              } else if (isXMMPtrTy(arg1->getType())) {
              }
              Value* newArg = arg1;
            }
          }
          break;
        }
        if (funcToFunc.count(callee) > 0) {
          // 함수가 대체되는 경우
          Function* newCallee = funcToFunc[callee];
          std::vector<Value*> plist;

          for (unsigned int i = 0; i < CI->arg_size(); i++) {
            Value* funcArg = callee->getArg(i);
            Value* arg = CI->getArgOperand(i);
            // 일단 타입별로
            //
            //
            if (isFunctionPtrTy(funcArg->getType())) {
              Value* newArg = valToVal.count(arg) ? valToVal[arg] : arg;
              plist.push_back(newArg);
            } else if (funcArg->getType()->isPointerTy()) {
              if (valToVal.count(arg) > 0) {
                Value* newArg = valToVal[arg];
                Value* tempArg = irb.CreateAlloca(XMM, nullptr, "temp.arg");
                if (isXMMTy(newArg->getType())) {
                  irb.CreateStore(newArg, tempArg);
                  Value* bitCast = irb.CreateBitCast(tempArg, arg->getType());
                  plist.push_back(bitCast);
                  // Value* ptr = irb.CreateExtractElement(newArg, (uint64_t)1);
                  // Value* tag = irb.CreateExtractElement(newArg, (uint64_t)0);
                  // plist.push_back(tag);
                  // plist.push_back(ptr);
                } else {
                  Value* ptr =
                      newArg->getType()->isPointerTy()
                          ? irb.CreatePtrToInt(newArg, irb.getInt64Ty())
                          : irb.CreateBitCast(newArg, irb.getInt64Ty());

                  Constant* nullVec = Constant::getNullValue(XMM);
                  Value* vec2 =
                      irb.CreateInsertElement(nullVec, ptr, uint64_t(1));
                  irb.CreateStore(vec2, tempArg);
                  Value* bitCast = irb.CreateBitCast(tempArg, arg->getType());
                  plist.push_back(bitCast);
                  // constant null 채워서 주기
                  // Value* ptr =
                  //     newArg->getType()->isPointerTy()
                  //         ? irb.CreatePtrToInt(newArg, irb.getInt64Ty())
                  //         : irb.CreateBitCast(newArg, irb.getInt64Ty());
                  // Value* tag = ConstantInt::get(irb.getInt64Ty(), 0);
                  // plist.push_back(tag);
                  // plist.push_back(ptr);
                }
              } else {
                Value* newArg;
                if (isa<Instruction>(arg)) {
                  Instruction* newInst = I.clone();
                  clone->getInstList().push_back(newInst);

                  newArg = irb.CreatePtrToInt(newInst, irb.getInt64Ty());
                } else
                  newArg = irb.CreatePtrToInt(arg, irb.getInt64Ty());

                Value* nullValue = Constant::getNullValue(irb.getInt64Ty());
                Constant* nullVec = Constant::getNullValue(XMM);
                Value* v1 =
                    irb.CreateInsertElement(nullVec, nullValue, (uint64_t)0);
                Value* v2 = irb.CreateInsertElement(v1, newArg, (uint64_t)1);
                Value* tempArg = irb.CreateAlloca(XMM, nullptr, "temp.arg");
                irb.CreateStore(v2, tempArg);

                Value* p = irb.CreateBitCast(tempArg, arg->getType());
                plist.push_back(p);
                // 여기서는 포인터에 원래값
                // 태그에는 널 넣기
              }
            } else {
              if (valToVal.count(arg) > 0) {
                plist.push_back(valToVal[arg]);
              } else {
                plist.push_back(arg);
                // 그냥 arg 넣어주기
                // 거의 왠만하면 constant 일듯
              }
            }
          }

          Value* newVal = irb.CreateCall(newCallee, plist, I.getName());
          valToVal[dyn_cast<Value>(&I)] = newVal;
        } else if (!callee->isDeclaration()) {
          // if callee is normal function (param are not pointerty.) and not
          // declaration function!
          Instruction* cloneI = I.clone();
          clone->getInstList().push_back(cloneI);
          IRBuilder<> irb(cloneI);
          CI = dyn_cast<CallInst>(cloneI);
          for (unsigned int i = 0; i < CI->getNumArgOperands(); i++) {
            Value* arg = CI->getArgOperand(i);
            if (valToVal.count(arg) > 0) {
              Value* newArg = valToVal[arg];
              CI->setArgOperand(i, newArg);
            }
          }
          valToVal[dyn_cast<Value>(&I)] = cloneI;
        }
        break;
      }
      case Instruction::ICmp: {
        Instruction* newInst = I.clone();
        newInst->setName(I.getName());
        ICmpInst* iCmp = dyn_cast<ICmpInst>(&I);

        Value* op1 = iCmp->getOperand(0);
        Value* op2 = iCmp->getOperand(1);
        op1 = valToVal.count(op1) > 0 ? valToVal[op1] : op1;
        op2 = valToVal.count(op2) > 0 ? valToVal[op2] : op2;

        if (isXMMTy(op1->getType())) {
          op1 = ununTag(op1, I.getOperand(0)->getType(), irb);

        } else {
          // may be null
          if (op1->getType()->isPointerTy()) {
            PointerType* pointerType = dyn_cast<PointerType>(op1->getType());
            if (pointerType->getPointerElementType()->isStructTy()) {
              StructType* st =
                  dyn_cast<StructType>(pointerType->getPointerElementType());
              Type* targetType =
                  strucTyToStructTy.count(st) > 0 ? strucTyToStructTy[st] : st;
              op1 = Constant::getNullValue(targetType->getPointerTo());
            }
          }
        }
        if (isXMMTy(op2->getType())) {
          op2 = ununTag(op2, I.getOperand(1)->getType(), irb);

        } else {
          // may be null
          if (op2->getType()->isPointerTy()) {
            PointerType* pointerType = dyn_cast<PointerType>(op2->getType());
            if (pointerType->getPointerElementType()->isStructTy()) {
              StructType* st =
                  dyn_cast<StructType>(pointerType->getPointerElementType());
              Type* targetType =
                  strucTyToStructTy.count(st) > 0 ? strucTyToStructTy[st] : st;

              op2 = Constant::getNullValue(targetType->getPointerTo());
            }
          }
        }
        newInst->setOperand(0, op1);
        newInst->setOperand(1, op2);

        clone->getInstList().push_back(newInst);
        valToVal[dyn_cast<Value>(&I)] = newInst;

        break;
      }
      case Instruction::BitCast:
        // If it is for malloc instruction, it should be deleted.
        // L4 pointer don't need bitcast instruction.
        // 그냥 배열일때 필요함, 하아 이걸 어떻게 고치나...

        if (valToVal.count(I.getOperand(0)) > 0) {
          if (isAllocation(getInsertPointBefore(&I))) {
            if (isMalloc(getInsertPointBefore(&I)))
              valToVal[dyn_cast<Value>(&I)] = valToVal[I.getOperand(0)];
            else if (isRealloc(getInsertPointBefore(&I))) {
              Instruction* newInst = I.clone();
              newInst->setOperand(0, valToVal[I.getOperand(0)]);
              clone->getInstList().push_back(newInst);
              valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
            }
            break;
          }
          BitCastInst* bci = dyn_cast<BitCastInst>(&I);

          Value* op = valToVal[I.getOperand(0)];
          // if (PointerType* pointerType =
          //         dyn_cast<PointerType>(bci->getDestTy())) {
          //   if (pointerType->getPointerElementType()->isStructTy()) {
          //     StructType* st =
          //         dyn_cast<StructType>(pointerType->getPointerElementType());
          //     StructType* newSt = st;
          //     Value* newOp = op;
          //     if (isXMMTy(op->getType()))
          //       newOp = ununTag(op, I.getOperand(0)->getType(), irb);

          //     Value* newInst = irb.CreateBitCast(newOp,
          //     newSt->getPointerTo()); valToVal[dyn_cast<Value>(&I)] =
          //     dyn_cast<Value>(newInst); break;
          //   }
          // }
          if (isXMMTy(op->getType())) {
            Value* newOp = ununTag(op, I.getOperand(0)->getType(), irb);
            Instruction* newInst = I.clone();
            clone->getInstList().push_back(newInst);
            newInst->setOperand(0, newOp);
            newInst->setName("WHY");
            valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
          } else if (isXMMPtrTy(op->getType())) {
            valToVal[&I] = op;
            arrToPtr[&I] = op;
            break;
          } else {
            Instruction* newInst = I.clone();

            newInst->setName("HEREBITCAST");
            newInst->setOperand(0, op);
            clone->getInstList().push_back(newInst);
            valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
          }
          break;
        } else {
        }
        break;
      case Instruction::PHI: {
        PHINode* phi = dyn_cast<PHINode>(&I);
        Instruction* newInst = I.clone();
        PHINode* newPhi = dyn_cast<PHINode>(newInst);

        for (int i = 0; i < I.getNumOperands(); i++) {
          if (valToVal.count(I.getOperand(i))) {
            if (isXMMTy(valToVal[I.getOperand(i)]->getType())) {
              if (I.getOperand(i)->getType() ==
                  valToVal[I.getOperand(i)]->getType()) {
                Value* newVal = ununTag(valToVal[I.getOperand(i)],
                                        I.getOperand(i)->getType(), irb);
                newInst->setOperand(i, newVal);
              }
            } else {
              newInst->setOperand(i, valToVal[I.getOperand(i)]);
            }
          }
        }
        instPrint(&I, "I?");
        for (int i = 0; i < phi->getNumIncomingValues(); i++) {
          BasicBlock* bb = newPhi->getIncomingBlock(i);
          BasicBlock* newBB = dyn_cast<BasicBlock>(valToVal[bb]);
          newPhi->replaceIncomingBlockWith(bb, newBB);
        }
        valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
        clone->getInstList().push_back(newInst);
        break;
      }
      case Instruction::Br: {
        Instruction* newInst = I.clone();
        newInst->setName(I.getName());
        BranchInst* newBr = dyn_cast<BranchInst>(newInst);
        if (newBr->isConditional()) {
          Value* oldCond = newBr->getCondition();
          Value* newCond = valToVal[oldCond];
          newBr->setCondition(newCond);
        }
        for (int i = 0; i < I.getNumOperands(); i++) {
          newInst->setOperand(i, valToVal[I.getOperand(i)]);
        }
        clone->getInstList().push_back(newInst);
        break;
      }
      case Instruction::ZExt: {
        Instruction* newInst = I.clone();
        newInst->setOperand(0, valToVal[I.getOperand(0)]);
        valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
        clone->getInstList().push_back(newInst);
        break;
      }
      case Instruction::Ret: {
        Type* returnType = cloneFunc->getReturnType();
        if (returnType->isVoidTy()) {
          Instruction* newInst = I.clone();
          clone->getInstList().push_back(newInst);
          break;
        }
        ReturnInst* ret = dyn_cast<ReturnInst>(&I);
        if (ret->getNumOperands() == 0) {
          Instruction* newInst = I.clone();
          clone->getInstList().push_back(newInst);
          break;
        }
        Value* returnValue = ret->getReturnValue();

        if (isa<ConstantPointerNull>(returnValue)) {
          if (isXMMTy(returnType)) {
            Value* newNullRet = Constant::getNullValue(XMM);
            irb.CreateRet(newNullRet);
          } else {
            Instruction* newInst = I.clone();
            clone->getInstList().push_back(newInst);
          }
          break;
        }

        Instruction* newInst = I.clone();
        if (valToVal.count(I.getOperand(0)) > 0) {
          Value* returnValue = valToVal[I.getOperand(0)];
          if (!isXMMTy(returnValue->getType()) && isXMMTy(returnType)) {
            Value* newReturn = createL4Ptr(returnValue, irb);
            newInst->setOperand(0, newReturn);
          } else if (isXMMTy(returnValue->getType()) && !isXMMTy(returnType)) {
            Value* newReturn = ununTag(returnValue, returnType, irb);
            newInst->setOperand(0, newReturn);
          } else
            newInst->setOperand(0, valToVal[I.getOperand(0)]);
        }
        clone->getInstList().push_back(newInst);
        break;
      }
      default:
        Instruction* newInst = I.clone();
        newInst->setName(I.getName());
        for (int i = 0; i < I.getNumOperands(); i++) {
          if (valToVal.count(I.getOperand(i))) {
            valuePrint(valToVal[I.getOperand(i)], "???");
            if (isXMMTy(valToVal[I.getOperand(i)]->getType())) {
              if (I.getOperand(i)->getType()->isPointerTy()) {
                Value* newVal = ununTag(valToVal[I.getOperand(i)],
                                        I.getOperand(i)->getType(), irb);
                newInst->setOperand(i, newVal);
              } else {
                errs() << "newVal should be PointerTy!\n";
                exit(0);
                // newInst->setOperand(i, newVal);
              }
            } else {
              newInst->setOperand(i, valToVal[I.getOperand(i)]);
            }
          }
        }
        clone->getInstList().push_back(newInst);
        if (Value* ov = dyn_cast<Value>(&I))
          valToVal[ov] = dyn_cast<Value>(newInst);
        break;
    }
  }

  return clone;
}
void MPAvailable::eraseFunction(Function* function) {
  for (Instruction& inst : instructions(function)) {
    if (function->getInstructionCount() == 0) break;
    for (User* use : inst.users()) {
    }
  }
}

Instruction* MPAvailable::handleAlloca(AllocaInst* alloca, IRBuilder<>& irb) {
  if (alloca->getAllocatedType()->isPointerTy()) {
  }
}

void MPAvailable::declareWrappingFunction(Function& F) {
  // if (F.getName() == "main") {
  //   usedFunctionPointer.insert(&F);
  //   return;
  // }
  bool isNeedTransform = false;
  if (isUsedFunctionPointer(&F)) {
    // usedFunctionPointer.insert(&F);
    isNeedTransform = true;
    // return;
  }
  bool mustWrapped = false;
  Function* newFunc;
  std::map<Value*, Value*> valToVal;
  std::map<StringRef, int> argToArg;
  std::map<BasicBlock*, BasicBlock*> basicToBasic;
  std::map<Value*, Type*> valToType;
  // if (isa<Constant>(&F)) return;

  int i = 0;
  std::vector<Type*> plist;

  for (Argument& arg : F.args()) {
    Value* vArg = dyn_cast<Value>(&arg);
    if (isFunctionPtrTy(arg.getType())) {
      PointerType* ptrTy = dyn_cast<PointerType>(arg.getType());
      Type* elementType = ptrTy->getPointerElementType();
      FunctionType* funcType = dyn_cast<FunctionType>(elementType);
      Type* newType = createFunctionType(funcType);
      plist.push_back(newType->getPointerTo());
    }
    // } else if (arg.getType()->isPointerTy()) {
    //   plist.push_back(XMM_POINTER);
    // } else {
    //   plist.push_back(arg.getType());
    // }
    // i++;
    else
      plist.push_back(arg.getType());
  }

  // else {
  //   for (Argument& arg : F.args()) {
  //     Value* vArg = dyn_cast<Value>(&arg);
  //     plist.push_back(arg.getType());
  //   }
  // }
  Type* returnType;
  if (F.getReturnType()->isPointerTy()) {
    if (isNeedTransform)
      returnType = F.getReturnType();
    else
      returnType = XMM;
  } else {
    returnType = F.getReturnType();
    if (returnType->isStructTy()) {
      StructType* st = dyn_cast<StructType>(returnType);
      returnType =
          strucTyToStructTy.count(st) > 0 ? strucTyToStructTy[st] : returnType;
    }
  }
  typePrint(F.getFunctionType(), F.getName().str());
  FunctionType* newFT = FunctionType::get(returnType, plist, F.isVarArg());
  typePrint(newFT, "Wrapping_" + F.getName().str());

  newFunc = Function::Create(newFT, F.getLinkage(), "Wrapping_" + F.getName());

  std::vector<AttributeSet> argAttrVec;
  Module* m = F.getParent();

  m->getFunctionList().insert(F.getIterator(), newFunc);
  // m->getFunctionList().insert(Module::iterator(F), newFunc);

  AttributeList pal = F.getAttributes();

  newFunc->copyAttributesFrom(&F);
  AttributeList newAttrList = newFunc->getAttributes();
  SmallVector<AttributeSet, 8> param_attrs_vec;

  for (int i = 0; i < F.arg_size(); i++) {
    newAttrList = newAttrList.removeParamAttributes(F.getContext(), i);
    AttributeSet attrs = pal.getParamAttributes(i);
    if (attrs.hasAttributes()) {
      AttrBuilder B(attrs);
    }
  }

  const AttrBuilder newAttrBuilder;

  for (int i = 0; i < newFunc->arg_size(); i++)
    newAttrList = newAttrList.addParamAttributes(newFunc->getContext(), i,
                                                 newAttrBuilder);
  const AttributeList resultAttrList = newAttrList;

  // newFunc->setAttributes(resultAttrList);

  funcToFunc[&F] = newFunc;
  wrappingFunctions.insert(newFunc);
  willBeDeletedFunctions.insert(&F);
  // replaceFunction(newFunc, &F);
  // F.eraseFromParent();
  if (F.getName() == "main")

  {
    F.replaceAllUsesWith(newFunc);
    F.setName("willbedeletemain");
    newFunc->setName("main");
  }
}

void MPAvailable::createWrappingMain(Function& F) {
  // This function wrap only main function or init function
  if (usedFunctionPointer.count(&F) == 0) return;

  // 여기서 해야할건 기존에 했던거 같은데
  // 다만 메인의 인자를 어떻게 받을것인가 고민하기
  // 메인 인자는 포인터만 받고 tag에는 걍 null value 넣기
  // 기존에 했던것을 clone 식으로 바꾸자
  // 그게 더 안정적인듯
  //
  // cloneBB 와 다른 점, 원래 있떤 함수를 고치는 것이라
  // 기존의 인스트럭션이 보존이 됨

  std::map<Value*, Value*> valToVal;
  for (detail::DenseMapPair<GlobalVariable*, GlobalVariable*> gPair : gToGV) {
    Value* key = gPair.first;
    Value* value = gPair.second;
    valToVal[key] = value;
  }
  for (detail::DenseMapPair<Function*, Function*> fPair : funcToFunc) {
    Value* key = fPair.first;
    Value* value = fPair.second;
    valToVal[key] = value;
  }
  DenseSet<Instruction*> willBeDeletedInsts;
  DenseSet<Instruction*> continueList;

  // if L4 should be bitcast ptr, but L4 will be needed,
  // this will be used. (bitcast)
  std::map<Value*, Value*> xmmToPtr;
  std::map<Value*, Value*> arrToPtr;

  for (Instruction& I : instructions(F)) {
    if (continueList.count(&I) > 0) continue;
    switch (I.getOpcode()) {
      case Instruction::Alloca: {
        // 통과
        AllocaInst* alloca = dyn_cast<AllocaInst>(&I);
        if (isFunctionPtrTy(alloca->getAllocatedType())) {
          FunctionType* ft = dyn_cast<FunctionType>(
              dyn_cast<PointerType>(alloca->getAllocatedType())
                  ->getPointerElementType());
          IRBuilder<> irb(getInsertPointAfter(&I));
          FunctionType* newFt = createFunctionType(ft);
          Value* newPointer = irb.CreateAlloca(newFt->getPointerTo(), nullptr,
                                               alloca->getName().str() + ".l4");
          continueList.insert(dyn_cast<Instruction>(newPointer));
          valToVal[dyn_cast<Value>(&I)] = newPointer;
        } else if (alloca->isArrayAllocation()) {
          IRBuilder<> irb(&I);
          Value* newPointer =
              irb.CreateAlloca(XMM, nullptr, alloca->getName().str() + ".l4");

          // 여기서 포인터에 저장까지 하자

          Value* allocSize = instrumentWithByteSize(irb, &I, valToVal);

          Value* OvSz = createMask(irb, allocSize, irb.getContext());
          Value* PtrInt = irb.CreatePtrToInt(alloca, irb.getInt64Ty());
          Value* emptyVec = Constant::getNullValue(XMM);

          Value* vec0 = irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
          Value* vec1 = irb.CreateInsertElement(vec0, PtrInt, 1);

          Instruction* storeI = irb.CreateStore(vec1, newPointer);

          continueList.insert(dyn_cast<Instruction>(PtrInt));
          continueList.insert(dyn_cast<Instruction>(newPointer));
          continueList.insert(dyn_cast<Instruction>(vec0));
          continueList.insert(dyn_cast<Instruction>(vec1));
          continueList.insert(dyn_cast<Instruction>(storeI));

          valToVal[dyn_cast<Value>(&I)] = newPointer;
          arrToPtr[dyn_cast<Value>(&I)] = newPointer;
        } else if (alloca->getAllocatedType()->isArrayTy()) {
          IRBuilder<> irb(getInsertPointAfter(&I));
          Value* newPointer =
              irb.CreateAlloca(XMM, nullptr, alloca->getName().str() + ".l4");

          // 여기서 포인터에 저장까지 하자
          Type* type = alloca->getAllocatedType();
          ArrayType* arrType = dyn_cast<ArrayType>(type);
          Value* arrTypeSize = irb.getInt64(
              DL->getTypeAllocSize(arrType->getArrayElementType()));
          Value* arrSize = irb.getInt64(arrType->getArrayNumElements());
          Value* allocSize = irb.CreateMul(arrTypeSize, arrSize);

          Value* OvSz = createMask(irb, allocSize, irb.getContext());
          Value* PtrInt = irb.CreatePtrToInt(alloca, irb.getInt64Ty());
          Value* emptyVec = Constant::getNullValue(XMM);

          Value* vec0 = irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
          Value* vec1 = irb.CreateInsertElement(vec0, PtrInt, 1);

          Instruction* storeI = irb.CreateStore(vec1, newPointer);

          continueList.insert(dyn_cast<Instruction>(PtrInt));
          continueList.insert(dyn_cast<Instruction>(newPointer));
          continueList.insert(dyn_cast<Instruction>(vec0));
          continueList.insert(dyn_cast<Instruction>(vec1));
          continueList.insert(dyn_cast<Instruction>(storeI));

          valToVal[dyn_cast<Value>(&I)] = newPointer;
          arrToPtr[dyn_cast<Value>(&I)] = newPointer;
        } else if (alloca->getAllocatedType()->isPointerTy()) {
          if (alloca->getName().find(".addr") != std::string::npos) {
            // It is function argument variable, so don't change xmm type
            break;
          }
          PointerType* pt = dyn_cast<PointerType>(alloca->getAllocatedType());
          if (pt->getPointerElementType()->isFunctionTy()) break;
          IRBuilder<> irb(&I);

          Value* newVal =
              irb.CreateAlloca(XMM, nullptr, alloca->getName() + ".xmm");
          valToVal[dyn_cast<Value>(&I)] = newVal;
          continueList.insert(dyn_cast<Instruction>(newVal));
          willBeDeletedInsts.insert(&I);
        }
        break;
      }
      case Instruction::Store: {
        Value* origPointer = I.getOperand(1);
        Value* val = valToVal.count(I.getOperand(0)) > 0
                         ? valToVal[I.getOperand(0)]
                         : I.getOperand(0);
        IRBuilder<> irb(&I);
        if (valToVal.count(origPointer) > 0) {
          Value* newPointer = valToVal[origPointer];

          if (isXMMTy(val->getType())) {
            if (isXMMTy(newPointer->getType())) {
              Value* replacePointer = ununTag(newPointer, XMM_POINTER, irb);
              irb.CreateStore(val, replacePointer);
              willBeDeletedInsts.insert(&I);

            } else if (isXMMPtrTy(newPointer->getType())) {
              irb.CreateStore(val, newPointer);
              willBeDeletedInsts.insert(&I);
            }
          } else if (isXMMTy(newPointer->getType())) {
            Value* unwrapPtr = ununTag(newPointer, origPointer->getType(), irb);

            Instruction* newSI = irb.CreateStore(val, unwrapPtr);
            continueList.insert(newSI);
            willBeDeletedInsts.insert(&I);
          } else if (AllocaInst* ai = dyn_cast<AllocaInst>(newPointer)) {
            if (isXMMTy(ai->getAllocatedType())) {
              if (isXMMTy(val->getType())) {
                Instruction* newSI = irb.CreateStore(val, newPointer);
                continueList.insert(newSI);
                willBeDeletedInsts.insert(&I);
              } else {
                Value* nullVec = Constant::getNullValue(XMM);
                Value* replaceVal;
                if (val->getType()->isPointerTy())
                  replaceVal = irb.CreatePtrToInt(val, irb.getInt64Ty());
                else if (isXMMTy(val->getType()))
                  replaceVal = val;
                Value* vecPtr = irb.CreateInsertElement(nullVec, replaceVal, 1);
                Instruction* newSI = irb.CreateStore(vecPtr, newPointer);
                continueList.insert(newSI);
                willBeDeletedInsts.insert(&I);
              }
            }
          } else {
            // Value가 포인터고, pointer가 xmm type 인경우
            //이런게 나오는 이유가 double pointer 에 대해서 구현을 못하였기
            //때문임
            if (isXMMPtrTy(newPointer->getType()) && !isXMMTy(val->getType())) {
              //그러면 val 을 xmm ty로 바꾸자
              Value* newVal = createL4Ptr(val, irb);
              irb.CreateStore(newVal, newPointer);
            } else if (!isXMMPtrTy(newPointer->getType()) &&
                       isXMMTy(val->getType())) {
              Value* newVal = ununTag(val, I.getOperand(0)->getType(), irb);
              Instruction* newSI = irb.CreateStore(newVal, newPointer);
              continueList.insert(newSI);
            } else {
              Instruction* newSI = irb.CreateStore(val, newPointer);
              continueList.insert(newSI);
            }
            willBeDeletedInsts.insert(&I);
          }
        } else {
          //  만약 local 포인터 -> global 포인터로 가는 경우에 대해서 해야 됨
          if (valToVal.count(I.getOperand(0)) > 0) {
            if (isXMMTy(val->getType())) {
              Value* newVal = ununTag(val, I.getOperand(0)->getType(), irb);
              I.setOperand(0, newVal);
            } else
              I.setOperand(0, valToVal[I.getOperand(0)]);
          }
        }
        break;
      }
      case Instruction::Load: {
        // 위의 코드 그대로 추가 되야 함
        Value* ptr = I.getOperand(0);
        if (valToVal.count(ptr) > 0) {
          IRBuilder<> irb(&I);
          Value* newPtr = valToVal[ptr];

          if (isXMMTy(newPtr->getType())) {
            // 포인터일 경우 아닐 경우,
            // 함수포인터일경우 아닐 경우,
            Value* unwrapPtr;
            if (I.getType()->isPointerTy() && !isFunctionPtrTy(I.getType())) {
              unwrapPtr = ununTag(newPtr, XMM_POINTER, irb, "load");
            } else {
              unwrapPtr = ununTag(newPtr, ptr->getType(), irb, "load");
            }

            Value* newLoad = irb.CreateLoad(unwrapPtr);
            valToVal[dyn_cast<Value>(&I)] = newLoad;
            willBeDeletedInsts.insert(&I);
          } else {
            Value* newLoad = irb.CreateLoad(newPtr);
            valToVal[dyn_cast<Value>(&I)] = newLoad;
            willBeDeletedInsts.insert(&I);
          }
        }
        break;
      }
      case Instruction::Call: {
        CallInst* CI = dyn_cast<CallInst>(&I);
        Function* callee = CI->getCalledFunction();

        if (!callee) {
          // if callee is null, callee is declaration.
          Value* val = CI->getCalledOperand();
          IRBuilder<> irb(CI);
          val = valToVal.count(val) > 0 ? valToVal[val] : val;
          CI->setCalledOperand(val);
          for (unsigned int i = 0; i < CI->getNumArgOperands(); i++) {
            Value* arg = CI->getArgOperand(i);
            if (valToVal.count(arg) > 0) {
              Value* newArg = valToVal[arg];
              if (isXMMTy(newArg->getType())) {
                Value* newXMM = ununTag(newArg, arg->getType(), irb, "call");
                CI->setArgOperand(i, newXMM);
              } else if (isXMMPtrTy(newArg->getType())) {
                if (arrToPtr.count(arg) > 0) {
                  Value* wrapPtr = arrToPtr[arg];
                  Value* l4Ptr = irb.CreateLoad(wrapPtr);
                  Value* unWrapPtr = ununTag(l4Ptr, arg->getType(), irb);
                  CI->setArgOperand(i, unWrapPtr);
                } else {
                  std::list<Value*> plist;
                  Value* idx = ConstantInt::get(irb.getInt64Ty(), 1);
                  // Value* newPtr = irb.CreateInBoundsGEP(
                  //     irb.getInt64Ty()->getPointerTo(), newArg, idx);
                  IRBuilder<> tempIRB(getInsertPointBefore(CI));
                  Value* newPtr =
                      irb.CreateBitCast(newArg, arg->getType(), "HERE2");
                  CI->setArgOperand(i, newPtr);
                }
              } else {
                CI->setArgOperand(i, newArg);
              }
            }
          }
          break;
        } else if (callee->isDeclaration()) {
          // 포인터들 다 언랩핑하기
          // 여기서는 오퍼랜드만 교체하기
          IRBuilder<> irb(CI);
          for (unsigned int i = 0; i < CI->getNumArgOperands(); i++) {
            Value* arg = CI->getArgOperand(i);
            if (valToVal.count(arg) > 0) {
              Value* newArg = valToVal[arg];
              if (isXMMTy(newArg->getType())) {
                Value* newXMM = ununTag(newArg, arg->getType(), irb);
                CI->setArgOperand(i, newXMM);
              } else {
                if (isXMMPtrTy(newArg->getType())) {
                  if (arrToPtr.count(arg) > 0) {
                    Value* wrapPtr = arrToPtr[arg];
                    Value* l4Ptr = irb.CreateLoad(wrapPtr);
                    Value* unWrapPtr = ununTag(l4Ptr, arg->getType(), irb);
                    CI->setArgOperand(i, unWrapPtr);

                  } else {
                    Value* ptr = irb.CreateBitCast(
                        newArg, irb.getInt64Ty()->getPointerTo());
                    Value* idx = ConstantInt::get(irb.getInt64Ty(), 1);
                    Value* newPtr = irb.CreateInBoundsGEP(irb.getInt64Ty(), ptr,
                                                          idx, "test");
                    Value* newInsertArg =
                        irb.CreateBitCast(newPtr, arg->getType());
                    CI->setArgOperand(i, newInsertArg);
                  }

                } else
                  CI->setArgOperand(i, newArg);
              }
            }
          }
        }

        if (isAllocation(&I)) {
          IRBuilder<> irb(getInsertPointAfter(&I));

          Value* ptr = dyn_cast<Value>(&I);  // maskMallocWrapper(irb, I);
          Value* Size = instrumentWithByteSize(irb, &I, valToVal);
          //역계산하자
          if (isMalloc(callee)) {
            IRBuilder<> tempIRB(&I);
            instPrint(&I, "I");
            fixParamAllocInst(I, valToVal, tempIRB);

            Instruction* next = I.getNextNode();
            Instruction* nextNext = next->getNextNode();
            if (next) {
              if (StoreInst* si = dyn_cast<StoreInst>(next)) {
                Value* pointer = si->getPointerOperand();
                if (isa<GlobalValue>(pointer)) break;
              }
            }
            if (nextNext) {
              if (StoreInst* si = dyn_cast<StoreInst>(nextNext)) {
                Value* pointer = si->getPointerOperand();
                if (isa<GlobalValue>(pointer)) break;
              }
            }

            if (isStackValue(&I)) break;

            // Value* newSize;

            Value* allocaVar;
            BitCastInst* bci = nullptr;
            Instruction* origStore;

            //일단 태그 만들기

            Value* OvSz = createMask(irb, Size, module->getContext());
            Value* PtrInt = irb.CreatePtrToInt(ptr, irb.getInt64Ty());
            continueList.insert(dyn_cast<Instruction>(PtrInt));
            Value* emptyVec = Constant::getNullValue(XMM);

            Value* vec0 = irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
            continueList.insert(dyn_cast<Instruction>(vec0));
            Value* vec1 = irb.CreateInsertElement(vec0, PtrInt, 1);
            continueList.insert(dyn_cast<Instruction>(vec1));
            valToVal[dyn_cast<Value>(&I)] = vec1;
          } else if (isRealloc(callee)) {
            // XMM PTR Type 이 아니라면 무시
            // 아 어차피 인자로 넣어줘야되서 여기서 untag 작업 해야 함
            // 그 때 다 수정해주어야 함
            IRBuilder<> irb(&I);

            Value* arg1 = CI->getArgOperand(0);
            Value* arg2 = CI->getArgOperand(1);
            Value* newArg = valToVal.count(arg2) > 0 ? valToVal[arg2] : arg2;

            CI->setArgOperand((unsigned)1, newArg);
            if (valToVal.count(arg1) > 0) {
              Value* newArg = valToVal[arg1];
              if (isXMMTy(newArg->getType())) {
                Value* newArg =
                    ununTag(newArg, arg1->getType(), irb, continueList);
                CI->setArgOperand(0, newArg);
                Value* OvSz = createMask(irb, Size, module->getContext());
                Value* idx = ConstantInt::get(irb.getInt64Ty(), 1);
                Value* newTagAddress =
                    irb.CreateInBoundsGEP(irb.getInt64Ty()->getPointerTo(),
                                          CI->getArgOperand(0), idx);
                continueList.insert(dyn_cast<Instruction>(newTagAddress));
                Instruction* newStore = irb.CreateStore(newArg, newTagAddress);
                continueList.insert(newStore);
              } else {
                if (isXMMPtrTy(newArg->getType())) {
                  // untag  안하는 이유
                  // int * a;
                  // &a가 인자로 넘어가서
                  std::list<Value*> plist;
                  Value* idx = ConstantInt::get(irb.getInt64Ty(), 1);
                  Value* newPtr = irb.CreateInBoundsGEP(
                      irb.getInt64Ty()->getPointerTo(), newArg, idx);
                  CI->setArgOperand(0, newPtr);
                } else
                  CI->setArgOperand(0, newArg);
              }
            }
          }

        } else if (funcToFunc.count(callee) > 0) {
          IRBuilder<> irb(&I);
          Function* newCallee = funcToFunc[callee];
          std::vector<Value*> plist;

          for (unsigned int i = 0; i < CI->arg_size(); i++) {
            Value* funcArg = callee->getArg(i);
            Value* arg = CI->getArgOperand(i);
            // 일단 타입별로
            //
            //
            if (funcArg->getType()->isPointerTy()) {
              if (valToVal.count(arg) > 0) {
                Value* newArg = valToVal[arg];
                if (isXMMPtrTy(newArg->getType())) {
                  if (arrToPtr.count(arg) > 0) {
                    Value* ptr = irb.CreateExtractElement(newArg, (uint64_t)1);
                    Value* tag = irb.CreateExtractElement(newArg, (uint64_t)0);
                    plist.push_back(tag);
                    plist.push_back(ptr);
                  } else {
                    errs() << "ERROR\n";
                  }
                } else if (isXMMTy(newArg->getType())) {
                  Value* tempArg = irb.CreateAlloca(XMM, nullptr, "temp.arg");
                  irb.CreateStore(newArg, tempArg);
                  Value* bitCast = irb.CreateBitCast(tempArg, arg->getType());
                  plist.push_back(bitCast);

                } else {
                  Value* ptr =
                      newArg->getType()->isPointerTy()
                          ? irb.CreatePtrToInt(newArg, irb.getInt64Ty())
                          : irb.CreateBitCast(newArg, irb.getInt64Ty());
                  Constant* nullVec = Constant::getNullValue(XMM);
                  Value* tempArg = irb.CreateAlloca(XMM, nullptr, "temp.arg");

                  Value* vec2 =
                      irb.CreateInsertElement(nullVec, ptr, uint64_t(1));
                  irb.CreateStore(vec2, tempArg);
                  Value* bitCast = irb.CreateBitCast(tempArg, arg->getType());
                  plist.push_back(bitCast);
                }
              } else {
                Value* newArg = irb.CreatePtrToInt(arg, irb.getInt64Ty());
                // if
                Value* nullValue = Constant::getNullValue(irb.getInt64Ty());
                Constant* nullVec = Constant::getNullValue(XMM);
                Value* v1 =
                    irb.CreateInsertElement(nullVec, nullValue, (uint64_t)0);
                Value* v2 = irb.CreateInsertElement(v1, newArg, (uint64_t)1);
                Value* tempArg = irb.CreateAlloca(XMM, nullptr, "temp.arg");
                irb.CreateStore(v2, tempArg);

                Value* p = irb.CreateBitCast(tempArg, arg->getType());
                plist.push_back(p);
                // 여기서는 포인터에 원래값
                // 태그에는 널 넣기
              }
            } else {
              if (valToVal.count(arg) > 0) {
                plist.push_back(valToVal[arg]);
              } else {
                plist.push_back(arg);
                // 그냥 arg 넣어주기
                // 거의 왠만하면 constant 일듯
              }
            }
          }
          Value* newVal = irb.CreateCall(newCallee, plist, I.getName());
          valToVal[dyn_cast<Value>(&I)] = newVal;
          willBeDeletedInsts.insert(&I);
        } else if (!callee->isDeclaration()) {
          // if callee is normal function (param are not pointerty.) and not
          // declaration function!
          for (unsigned int i = 0; i < CI->getNumArgOperands(); i++) {
            Value* arg = CI->getArgOperand(i);
            if (valToVal.count(arg) > 0) {
              Value* newArg = valToVal[arg];
              CI->setArgOperand(i, newArg);
            }
          }
        }
        break;
      }
      case Instruction::BitCast: {
        // don't need bitcast.

        if (valToVal.count(I.getOperand(0)) > 0) {
          Instruction* inst = dyn_cast<Instruction>(I.getOperand(0));
          if (inst && isAllocation(getInsertPointBefore(inst))) {
            valToVal[dyn_cast<Value>(&I)] = valToVal[I.getOperand(0)];
            willBeDeletedInsts.insert(&I);
            break;
          }
          Value* op = valToVal[I.getOperand(0)];
          if (isXMMTy(op->getType())) {
            IRBuilder<> irb(&I);
            // op = ununTag(op, I.getType(), irb);
            valToVal[&I] = op;
            willBeDeletedInsts.insert(&I);
            break;
          }
          if (isXMMPtrTy(op->getType())) {
            valToVal[&I] = op;
            willBeDeletedInsts.insert(&I);
            break;
          }
          I.setOperand(0, op);
          // willBeDeletedInsts.insert(&I);
          break;
        }
        break;
      }
      case Instruction::GetElementPtr: {
        // 구조체, 배열, 포인터에 해당하는 3가지를 구현할 것
        //
        //

        IRBuilder<> irb(&I);
        GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(&I);
        Value* base = gep->getPointerOperand();
        if (fixGEPforStruct(gep, valToVal, irb)) {
          willBeDeletedInsts.insert(&I);
          break;
        }
        if (valToVal.count(base) > 0) {
          Value* newBase = valToVal[base];
          if (isXMMTy(newBase->getType())) {
            Value* offset = emitGEPOffset(irb, *DL, gep, valToVal);
            Value* ConstOffset = nullptr;
            bool isPositive = hasNegativeOffset(gep);

            Constant* nullVec = Constant::getNullValue(XMM);
            Value* tag = createOffsetMask(irb, offset);
            Value* v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
            Value* v1 = irb.CreateInsertElement(v0, offset, 1);

            Value* replaceInst = irb.CreateAdd(
                newBase, v1,
                gep->hasName() ? gep->getName() : newBase->getName() + ".idx");
            valToVal[dyn_cast<Value>(gep)] = replaceInst;

            willBeDeletedInsts.insert(&I);
          } else if (AllocaInst* ai = dyn_cast<AllocaInst>(base)) {
            if (ai->getAllocatedType()->isArrayTy()) {
              Value* wrapPtr = arrToPtr[base];
              Value* l4Ptr = irb.CreateLoad(wrapPtr);
              Value* unWrapPtr = ununTag(l4Ptr, base->getType(), irb);

              Value* offset = emitGEPOffset(irb, *DL, gep, valToVal);

              Constant* nullVec = Constant::getNullValue(XMM);
              Value* tag = createOffsetMask(irb, offset);
              Value* v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
              Value* v1 = irb.CreateInsertElement(v0, offset, 1);
              Value* replaceInst = irb.CreateAdd(
                  l4Ptr, v1,
                  gep->hasName() ? gep->getName() : l4Ptr->getName() + ".idx");
              valToVal[dyn_cast<Value>(&I)] = replaceInst;

              // std::vector<Value*> plist;
              // for (auto i = gep->idx_begin(); i != gep->idx_end(); i++) {
              //   Value* val = *i;
              //   Type* type = gep->getTypeAtIndex(
              //       cast<PointerType>(
              //           gep->getPointerOperand()->getType()->getScalarType())
              //           ->getElementType(),
              //       val);
              //   if (valToVal.count(val) > 0)
              //     plist.push_back(valToVal[val]);
              //   else
              //     plist.push_back(val);
              // }
              // Value* newGEP = irb.CreateInBoundsGEP(valToVal[base], plist);
              // assertGEP(newGEP);
              // valToVal[dyn_cast<Value>(gep)] = newGEP;
              // willBeDeletedInsts.insert(&I);
            }
          } else {
            for (unsigned int i = 0; i < I.getNumOperands(); i++) {
              if (valToVal.count(I.getOperand(i)) > 0) {
                I.setOperand(i, valToVal[I.getOperand(i)]);
              }
            }
          }
        } else {
          for (unsigned int i = 0; i < I.getNumOperands(); i++) {
            if (valToVal.count(I.getOperand(i)) > 0) {
              I.setOperand(i, valToVal[I.getOperand(i)]);
            }
          }
        }
        break;
      }
      case Instruction::PtrToInt: {
        if (valToVal.count(I.getOperand(0)) > 0) {
          Value* op = valToVal[I.getOperand(0)];
          valToVal[dyn_cast<Value>(&I)] = op;
          willBeDeletedInsts.insert(&I);
        }
        break;
      }
      case Instruction::Add: {
        if (valToVal.count(I.getOperand(0)) > 0) {
          IRBuilder<> irb(&I);
          Value* op = valToVal[I.getOperand(0)];
          if (!isXMMTy(op->getType())) {
            I.setOperand(0, valToVal[op]);
          } else {
            Constant* nullVec = Constant::getNullValue(XMM);
            Value* vec1 =
                irb.CreateInsertElement(nullVec, I.getOperand(1), uint64_t(0));
            Value* vec2 =
                irb.CreateInsertElement(vec1, I.getOperand(1), uint64_t(1));

            Value* newAdd = irb.CreateAdd(op, vec2);
            valToVal[dyn_cast<Value>(&I)] = newAdd;
            willBeDeletedInsts.insert(&I);
          }
        }
        if (valToVal.count(I.getOperand(1)) > 0) {
          Value* op = valToVal[I.getOperand(1)];
          if (!isXMMTy(op->getType())) {
            I.setOperand(1, valToVal[op]);
          } else {
            IRBuilder<> irb(&I);
            Value* op = valToVal[I.getOperand(1)];
            Constant* nullVec = Constant::getNullValue(XMM);
            Value* vec1 =
                irb.CreateInsertElement(nullVec, I.getOperand(0), uint64_t(0));
            Value* vec2 =
                irb.CreateInsertElement(vec1, I.getOperand(0), uint64_t(1));
            Value* newAdd = irb.CreateAdd(op, vec2);
            valToVal[dyn_cast<Value>(&I)] = newAdd;
            willBeDeletedInsts.insert(&I);
          }
        }
        break;
      }
      case Instruction::Sub: {
        if (valToVal.count(I.getOperand(0)) > 0) {
          IRBuilder<> irb(&I);
          Value* op = valToVal[I.getOperand(0)];
          Constant* nullVec = Constant::getNullValue(XMM);
          Value* vec1 =
              irb.CreateInsertElement(nullVec, I.getOperand(1), uint64_t(0));
          Value* vec2 =
              irb.CreateInsertElement(vec1, I.getOperand(1), uint64_t(1));
          Value* newSub = irb.CreateSub(op, vec2);
          valToVal[dyn_cast<Value>(&I)] = newSub;
          willBeDeletedInsts.insert(&I);
        } else if (valToVal.count(I.getOperand(1)) > 0) {
          IRBuilder<> irb(&I);
          Value* op = valToVal[I.getOperand(1)];
          Constant* nullVec = Constant::getNullValue(XMM);
          Value* vec1 =
              irb.CreateInsertElement(nullVec, I.getOperand(0), uint64_t(0));
          Value* vec2 =
              irb.CreateInsertElement(vec1, I.getOperand(0), uint64_t(1));
          Value* newSub = irb.CreateSub(op, vec2);
          valToVal[dyn_cast<Value>(&I)] = newSub;
          willBeDeletedInsts.insert(&I);
        }
        break;
      }
      case Instruction::And: {
        if (valToVal.count(I.getOperand(0)) > 0) {
          IRBuilder<> irb(&I);
          Value* op = valToVal[I.getOperand(0)];
          Constant* nullVec = Constant::getNullValue(XMM);
          Value* vec1 =
              irb.CreateInsertElement(nullVec, I.getOperand(1), uint64_t(0));
          Value* vec2 =
              irb.CreateInsertElement(vec1, I.getOperand(1), uint64_t(1));
          Value* newAnd = irb.CreateAnd(op, vec2);
          valToVal[dyn_cast<Value>(&I)] = newAnd;
          willBeDeletedInsts.insert(&I);
        } else if (valToVal.count(I.getOperand(1)) > 0) {
          IRBuilder<> irb(&I);
          instPrint(&I, "I");
          Value* op = valToVal[I.getOperand(1)];
          Constant* nullVec = Constant::getNullValue(XMM);
          Value* vec1 =
              irb.CreateInsertElement(nullVec, I.getOperand(0), uint64_t(0));
          Value* vec2 =
              irb.CreateInsertElement(vec1, I.getOperand(0), uint64_t(1));
          Value* newAnd = irb.CreateAnd(op, vec2);
          valToVal[dyn_cast<Value>(&I)] = newAnd;
          willBeDeletedInsts.insert(&I);
        }
        break;
      }
      case Instruction::IntToPtr: {
        if (valToVal.count(I.getOperand(0)) > 0) {
          Value* op = valToVal[I.getOperand(0)];
          valToVal[dyn_cast<Value>(&I)] = op;
          willBeDeletedInsts.insert(&I);
        }
        break;
      }
      case Instruction::ICmp: {
        IRBuilder<> irb(&I);
        for (int i = 0; i < I.getNumOperands(); i++) {
          Value* op = I.getOperand(i);
          if (valToVal.count(op) > 0) {
            Value* newOp = valToVal[op];
            if (isXMMTy(newOp->getType())) {
              // it need only ptr in this instruction;
              // 포인터가 null 인지 아닌지 확인하기도 해서 그럼
              // 개선할 가능성 있을듯
              Value* replaceOp =
                  ununTag(newOp, I.getOperand(0)->getType(), irb, "icmp");
              I.setOperand(i, replaceOp);
            } else {
              I.setOperand(i, newOp);
            }
          }
        }
      }
      case Instruction::Ret: {
        if (I.getNumOperands() == 0) break;
        Value* op = I.getOperand(0);
        if (valToVal.count(op) > 0) {
          if (isXMMTy(valToVal[op]->getType())) {
            IRBuilder<> irb(&I);
            Value* newOp = ununTag(valToVal[op], op->getType(), irb);
            I.setOperand(0, newOp);
          } else
            I.setOperand(0, valToVal[op]);
        }
        break;
      }
      default: {
        // operand 들 다 교체해주기
        for (unsigned int i = 0; i < I.getNumOperands(); i++) {
          Value* op = I.getOperand(i);
          if (valToVal.count(op) > 0) {
            I.setOperand(i, valToVal[op]);
          }
        }
        break;
      }
    }
  }
  errs() << "WRapping main end \n";
  std::vector<Instruction*> workList(willBeDeletedInsts.begin(),
                                     willBeDeletedInsts.end());

  int size = workList.size();
  int counter = 0;
  while (!workList.empty()) {
    if (size == workList.size())
      counter++;
    else {
      counter = 0;
      size = workList.size();
    }
    if (counter > 100) {
      errs() << "infinit roop";
      errs() << "Function Name " << F.getName() << "\n";
      exit(1);
    }
    Instruction* inst = workList.front();
    if (inst->users().empty()) {
      workList.erase(workList.begin());
      inst->eraseFromParent();
    } else {
      instPrint(inst, "not delete");
      if (Value* v = dyn_cast<Value>(inst)) {
        if (valToVal.count(v) > 0) valuePrint(valToVal[v], "Inst ValToVal");
      }
      for (Value* user : inst->users()) {
        valuePrint(user, "user");
      }
      workList.erase(workList.begin());
      workList.push_back(inst);
    }
  }
  errs() << "Create Wrapping Main function end\n";
}

Value* MPAvailable::createOffsetMask(IRBuilder<>& irb, Value* offset) {
  Value* over = irb.CreateShl(offset, 32);
  Value* result = irb.CreateOr(over, offset);
  return result;
}

void MPAvailable::replaceStructTy(Module& M) {
  for (StructType* st : M.getIdentifiedStructTypes()) {
    createStructureType(st);
  }
  for (StructType* st : M.getIdentifiedStructTypes()) {
    createStructureType(st);
  }
}

void MPAvailable::replaceStructTyInFunction(Function& F) {
  // gep만 펼치기
  for (Instruction& I : instructions(F)) {
    if (I.getOpcode() == Instruction::GetElementPtr) {
      IRBuilder<> irb(&I);
      GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(&I);
      gep_type_iterator GTI = gep_type_begin(gep);
      Value* base = gep->getPointerOperand()->stripPointerCasts();
      instPrint(gep, "original gep: ");
      for (User::op_iterator i = gep->op_begin() + 1, e = gep->op_end(); i != e;
           ++i, ++GTI) {
        Value* Op = *i;

        base = irb.CreateGEP(GTI.getIndexedType(), base, Op);
        valuePrint(base, "split gep ");
      }
      if (base != gep->getPointerOperand()->stripPointerCasts()) {
        typePrint(gep->getType(), "orig gep type");
        typePrint(base->getType(), "replacing type");
        gep->replaceAllUsesWith(base);
        gep->eraseFromParent();
      }
    }
  }
}

static Constant* cloneConstantExpr(ConstantExpr* cExpr) {
  switch (cExpr->getOpcode()) {
    case Instruction::BitCast:
      cExpr->print(errs());
      errs() << "\n";
      cExpr->getOperand(0)->print(errs());
      exit(0);
      return ConstantExpr::getBitCast(cExpr->getOperand(0), cExpr->getType());
    default:
      return cExpr;
  }
}

Value* MPAvailable::instrumentWithByteSize(IRBuilder<>& B, Instruction* I,
                                           std::map<Value*, Value*>& valToVal) {
  AllocationType CallType = getCallType(I);
  int SizeArg = getSizeArg(I);

  switch (CallType) {
    case Malloc: {
      CallSite CS(I);
      if (valToVal.count(CS.getArgOperand(SizeArg)) > 0)
        return valToVal[CS.getArgOperand(SizeArg)];
      return CS.getArgOperand(SizeArg);
    }
    case Realloc: {
      CallSite CS(I);
      if (valToVal.count(CS.getArgOperand(1)) > 0)
        return valToVal[CS.getArgOperand(1)];
      return CS.getArgOperand(1);
    }
    case Calloc: {
      CallSite CS(I);
      Value* NumElements = valToVal.count(CS.getArgOperand(0)) > 0
                               ? valToVal[CS.getArgOperand(0)]
                               : CS.getArgOperand(0);
      Value* ElementSize = valToVal.count(CS.getArgOperand(1)) > 0
                               ? valToVal[CS.getArgOperand(1)]
                               : CS.getArgOperand(1);
      return B.CreateMul(NumElements, ElementSize);
    }
    case Alloca: {
      AllocaInst* AI = cast<AllocaInst>(I);
      Value* Size = B.getInt64(DL->getTypeAllocSize(AI->getAllocatedType()));
      Value* arraySize = valToVal.count(AI->getArraySize()) > 0
                             ? valToVal[AI->getArraySize()]
                             : AI->getArraySize();
      if (AI->isArrayAllocation()) Size = B.CreateMul(Size, arraySize);

      return Size;
    }
    case AllocaNone:
      return nullptr;
    default:
      return nullptr;
  }
  return nullptr; /* never reached */
}
bool MPAvailable::checkShouldBeWrapped(Function& F) {
  for (int i = 0; i < F.arg_size(); i++) {
    Value* arg = F.getArg(i);
    if (arg->getType()->isPointerTy()) {
      return true;
    }
  }
  if (F.getReturnType()->isPointerTy()) return true;
  return false;
}
void MPAvailable::findDoublePtrMalloc(Function& F) {
  bool isDoublePtrMalloc = false;
  for (Instruction& I : instructions(F)) {
    if (isMalloc(&I)) {
      CallInst* CI = dyn_cast<CallInst>(&I);
      if (CI->getNumUses() > 0) {
        for (Value* use : CI->users()) {
          if (BitCastInst* bci = dyn_cast<BitCastInst>(use)) {
            if (dyn_cast<PointerType>(bci->getType())
                    ->getElementType()
                    ->isPointerTy())
              isDoublePtrMalloc = true;
          }
        }
      }
      if (isDoublePtrMalloc) {
        IRBuilder<> irb(getInsertPointBefore(&I));
        Value* op = CI->getOperand(0);
        Value* newOp = irb.CreateMul(op, ConstantInt::get(op->getType(), 2));
        CI->setOperand(0, newOp);
      }
    }
  }
}

void MPAvailable::runOnStructInstrument(Module& M) {
  for (StructType* st : M.getIdentifiedStructTypes()) {
    if (st->getName().find("anon") != StringRef::npos) externStructs.insert(st);
  }
  for (Function& F : M) {
    if (F.isDeclaration()) {
      FunctionType* funcType = F.getFunctionType();
      for (Type* type : funcType->params()) {
        if (type->isPointerTy()) {
          PointerType* pt = dyn_cast<PointerType>(type);
          if (pt->getElementType()->isStructTy()) {
            StructType* st = dyn_cast<StructType>(pt->getElementType());
            externStructs.insert(st);
          }
        }
        if (type->isStructTy()) {
          StructType* st = dyn_cast<StructType>(type);
          externStructs.insert(st);
        }
      }
    }
  }
  bool changed = true;
  while (changed) {
    int before = externStructs.size();
    for (StructType* st : externStructs) {
      for (Type* type : st->elements()) {
        if (type->isPointerTy()) {
          PointerType* pt = dyn_cast<PointerType>(type);
          if (pt->getElementType()->isStructTy()) {
            StructType* st = dyn_cast<StructType>(pt->getElementType());
            externStructs.insert(st);
          }
        }
        if (type->isStructTy()) {
          StructType* addingST = dyn_cast<StructType>(type);
          externStructs.insert(addingST);
        }
      }
    }
    changed = before != externStructs.size();
  }
  errs() << "size: " << externStructs.size() << "\n";
  for (Type* type : externStructs) {
    typePrint(type, "inserting set ");
  }
}
bool MPAvailable::isExternStruct(Type* type) {
  if (type->isStructTy()) {
    StructType* st = dyn_cast<StructType>(type);
    if (externStructs.count(st) > 0) return true;
  }
  return false;
}

bool MPAvailable::fixParamAllocInst(Instruction& I,
                                    std::map<Value*, Value*>& valToVal,
                                    IRBuilder<>& irb, bool isNeededNewInst) {
  if (CallInst* ci = dyn_cast<CallInst>(&I)) {
    if (isMalloc(&I)) {
      for (User* use : ci->users()) {
        if (BitCastInst* bci = dyn_cast<BitCastInst>(use)) {
          if (dyn_cast<PointerType>(bci->getDestTy())
                  ->getPointerElementType()
                  ->isStructTy()) {
            instPrint(bci, "bci");
            StructType* st =
                dyn_cast<StructType>(dyn_cast<PointerType>(bci->getDestTy())
                                         ->getPointerElementType());

            if (strucTyToStructTy.count(st) > 0) {
              errs() << " New Struct!!\n";
              Value* op0 = ci->getOperand(0);
              Value* newParam;
              if (ConstantInt* cons = dyn_cast<ConstantInt>(op0)) {
                APInt intOp = cons->getValue();
                unsigned int arrayIntSize = this->DL->getTypeAllocSize(st);
                int index = intOp.getZExtValue() / arrayIntSize;
                unsigned int convertSize =
                    this->DL->getTypeAllocSize(strucTyToStructTy[st]);
                unsigned int newOp = convertSize * index;
                newParam = GETCONSTANTINT(
                    op0->getContext(),
                    I.getOperand(0)->getType()->getIntegerBitWidth(), newOp);
              } else {
                op0 = valToVal.count(op0) > 0 ? valToVal[op0] : op0;
                unsigned int arrayIntSize = this->DL->getTypeAllocSize(st);
                Value* div = GETCONSTANTINT(
                    op0->getContext(),
                    I.getOperand(0)->getType()->getIntegerBitWidth(),
                    arrayIntSize);
                unsigned int newTypeSize =
                    this->DL->getTypeAllocSize(strucTyToStructTy[st]);
                Value* mul = irb.CreateUDiv(op0, div);
                Value* newStSize = GETCONSTANTINT(
                    op0->getContext(),
                    I.getOperand(0)->getType()->getIntegerBitWidth(),
                    newTypeSize);
                newParam = irb.CreateMul(mul, newStSize);
              }
              if (isNeededNewInst) {
                std::vector<Value*> params;
                params.push_back(newParam);
                typePrint(ci->getCalledFunction()->getType(), "ci");
                Value* newCall =
                    irb.CreateCall(ci->getCalledFunction(), params);
                valToVal[ci] = newCall;
                return true;
              } else
                ci->setArgOperand(0, newParam);
            }
          } else if (dyn_cast<PointerType>(bci->getDestTy())
                         ->getPointerElementType()
                         ->isPointerTy()) {
            Value* op0 = ci->getOperand(0);
            op0 = valToVal.count(op0) > 0 ? valToVal[op0] : op0;
            Value* mul = GETCONSTANTINT(op0->getContext(), 64, 2);
            Value* newParam = irb.CreateMul(op0, mul);
            if (isNeededNewInst) {
              std::vector<Value*> params;
              params.push_back(newParam);
              Value* newCall = irb.CreateCall(ci->getCalledFunction(), params);
              valToVal[ci] = newCall;
              return true;
            } else {
              ci->setArgOperand(0, newParam);
            }
          }
        }
      }
    }
  }
  return false;
}

bool MPAvailable::fixGEPforStruct(GetElementPtrInst* gep,
                                  std::map<Value*, Value*>& valToVal,
                                  IRBuilder<>& irb, bool needReplace) {
  // 오직 struct 구조가 바뀌는 경우에 한해서만 하자
  // 카피가 필요하면 transformation 함수에서 해줄 것

  Value* pointer = gep->getPointerOperand();
  Type* pointerType = gep->getSourceElementType();
  Type* gepType = gep->getResultElementType();
  if (pointerType == gepType) return false;  //포인터, 배열 접근
  // typePrint(pointerType, "gep pointer type");
  if (pointerType->isStructTy()) {
    StructType* pointerSt = dyn_cast<StructType>(pointerType);
    if (strucTyToStructTy.count(pointerSt) > 0) {
      Value* newGEP;
      std::vector<Value*> plist;
      Value* newPtr = valToVal.count(pointer) > 0 ? valToVal[pointer] : pointer;

      if (isXMMTy(newPtr->getType())) {
        // unwrapping 해주면 됨
        Value* newInst = splatGEP(gep, valToVal, irb);
        valToVal[gep] = newInst;
        if (needReplace) willBeRemoveSet.insert(gep);
        return true;
      }
      // 그게 아닐 경우에 대해서만 하기 밑처럼 처리하면 됨
      for (auto i = gep->idx_begin(); i != gep->idx_end(); i++) {
        Value* val = *i;
        if (valToVal.count(val) > 0) {
          plist.push_back(valToVal[val]);
        } else {
          plist.push_back(val);
        }
      }
      if (gep->isInBounds()) {
        newGEP = irb.CreateInBoundsGEP(newPtr, plist, "fix");
      } else {
        newGEP = irb.CreateGEP(newPtr, plist);
      }
      valToVal[gep] = newGEP;
      // if (needReplace) willBeRemoveSet.insert(gep);
      return true;
    }
  }
  return false;
}

Value* MPAvailable::splatGEP(GetElementPtrInst* gep,
                             std::map<Value*, Value*>& valToVal,
                             IRBuilder<>& irb) {
  Value* offset = emitGEPOffset(irb, *DL, gep, valToVal);
  Value* basePointer = valToVal[gep->getPointerOperand()];

  Constant* nullVec = Constant::getNullValue(XMM);
  Value* tag = createOffsetMask(irb, offset);
  Value* v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
  Value* v1 = irb.CreateInsertElement(v0, offset, 1);

  Value* replaceInst = irb.CreateAdd(basePointer, v1, "SPLATGEP");
  return replaceInst;
  // valToVal[dyn_cast<Value>(gep)] = replaceInst;
}
Value* MPAvailable::splatGEP2(GetElementPtrInst* gep,
                              std::map<Value*, Value*>& valToVal,
                              IRBuilder<>& irb) {
  Value* offset = emitGEPOffset(irb, *DL, gep, valToVal);

  Constant* nullVec = Constant::getNullValue(XMM);
  Value* tag = createOffsetMask(irb, offset);
  Value* v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
  Value* v1 = irb.CreateInsertElement(v0, offset, 1);

  Value* replaceInst = irb.CreateAdd(gep->getPointerOperand(), v1, "SPLATGEP");
  return replaceInst;
  // valToVal[dyn_cast<Value>(gep)] = replaceInst;
}

void MPAvailable::verifyGlobalValue(Module& M) {
  errs() << "Verify Global Value \n";
  for (GlobalVariable& GV : M.getGlobalList()) {
    if (gToGV.count(&GV) > 0) {
      valuePrint(&GV, "original global");
      valuePrint(gToGV[&GV], "new global");
    }
  }
  exit(0);
}

FunctionType* MPAvailable::createFunctionType(FunctionType* ft) {
  std::vector<Type*> plist;
  for (unsigned int i = 0; i < ft->getNumParams(); i++) {
    Type* type = ft->getParamType(i);
    if (isFunctionPtrTy(type)) {
      FunctionType* elementFt = dyn_cast<FunctionType>(type);
      Type* newType = createFunctionType(elementFt);
      plist.push_back(newType);
    }
    // } else if (type->isPointerTy()) {
    //   plist.push_back(Type::getInt64Ty(ft->getContext()));
    //   plist.push_back(Type::getInt64Ty(ft->getContext()));
    // } else
    //   plist.push_back(type);
    else
      plist.push_back(type);
  }
  Type* returnType;
  if (ft->getReturnType()->isPointerTy())
    returnType = XMM;
  else
    returnType = ft->getReturnType();
  return FunctionType::get(returnType, plist, ft->isVarArg());
}
std::vector<Value*> MPAvailable::getCallArgs(CallInst* CI, FunctionType* ft,
                                             std::map<Value*, Value*>& valToVal,
                                             IRBuilder<>& irb) {
  std::vector<Value*> plist;
  Value* calledFunc = CI->getCalledOperand();
  typePrint(calledFunc->getType(), "calledFunc");

  for (unsigned int i = 0; i < CI->arg_size(); i++) {
    Type* argType = ft->getParamType(i);
    Value* arg = CI->getArgOperand(i);
    // 일단 타입별로
    //
    //
    if (isFunctionPtrTy(arg->getType())) {
      Value* newArg = valToVal.count(arg) ? valToVal[arg] : arg;
      valuePrint(newArg, "newArg");
      plist.push_back(newArg);
    } else if (arg->getType()->isPointerTy()) {
      if (valToVal.count(arg) > 0) {
        Value* newArg = valToVal[arg];
        if (isXMMTy(newArg->getType())) {
          Value* ptr = irb.CreateExtractElement(newArg, (uint64_t)1);
          Value* tag = irb.CreateExtractElement(newArg, (uint64_t)0);
          plist.push_back(tag);
          plist.push_back(ptr);
        } else {
          // constant null 채워서 주기
          Value* ptr = newArg->getType()->isPointerTy()
                           ? irb.CreatePtrToInt(newArg, irb.getInt64Ty())
                           : irb.CreateBitCast(newArg, irb.getInt64Ty());
          Value* tag = ConstantInt::get(irb.getInt64Ty(), 0);
          plist.push_back(tag);
          plist.push_back(ptr);
        }
      } else {
        errs() << "Error\n";
        exit(1);
        // Value* newArg;
        // if (isa<Instruction>(arg)) {
        //   Instruction* newInst = CI->clone();
        //   clone->getInstList().push_back(newInst);

        //   newArg = irb.CreatePtrToInt(newInst, irb.getInt64Ty());
        // } else
        //   newArg = irb.CreatePtrToInt(arg, irb.getInt64Ty());

        // Value* nullValue = Constant::getNullValue(irb.getInt64Ty());
        // plist.push_back(nullValue);
        // plist.push_back(newArg);
        // // 여기서는 포인터에 원래값
        // // 태그에는 널 넣기
      }
    } else {
      if (valToVal.count(arg) > 0) {
        plist.push_back(valToVal[arg]);
      } else {
        plist.push_back(arg);
        // 그냥 arg 넣어주기
        // 거의 왠만하면 constant 일듯
      }
    }
  }
  return plist;
}
void MPAvailable::valuePrintGenerate(Value* val, IRBuilder<>& irb) {
  static bool init = false;
  static GlobalVariable* gvar_ptr_abc;

  Module& M = *this->module;

  if (!init) {
    init = true;

    Constant* tempString =
        ConstantDataArray::getString(M.getContext(), "ADDRPRINT %p \n");

    Module& M = *this->module;
    gvar_ptr_abc = new GlobalVariable(
        /*Module=*/M,
        /*Type=*/tempString->getType(),
        /*isConstant=*/true,
        /*Linkage=*/GlobalValue::PrivateLinkage,
        /*Initializer=*/tempString,  // has initializer,
                                     // specified below
        /*Name=*/"print");
    gvar_ptr_abc->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
  }
  std::vector<Value*> cExprPlist;

  cExprPlist.push_back(ConstantInt::get(Type::getInt64Ty(M.getContext()), 0));
  cExprPlist.push_back(ConstantInt::get(Type::getInt64Ty(M.getContext()), 0));
  typePrint(gvar_ptr_abc->getType(), "type");
  valuePrint(gvar_ptr_abc, "gvar_ptr_abc");

  Value* arg = ConstantExpr::getInBoundsGetElementPtr(
      gvar_ptr_abc->getValueType(), gvar_ptr_abc, cExprPlist);
  std::vector<Value*> calleeList;
  calleeList.push_back(arg);
  calleeList.push_back(val);

  irb.CreateCall(printFunction, calleeList);
}
static RegisterPass<MPAvailable> MPAVAILABLE("mpav", "MPAvailable");