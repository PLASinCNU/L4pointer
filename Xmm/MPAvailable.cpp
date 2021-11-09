#include "MPAvailable.h"

#include <llvm/ADT/TinyPtrVector.h>
#include <llvm/Analysis/DependenceAnalysis.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ScalarEvolutionExpander.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/NoFolder.h>
#include <llvm/Transforms/Utils/Local.h>
#include <llvm/Transforms/Utils/LoopUtils.h>
#include <stdio.h>
#include <llvm/IR/LLVMContext.h>


#include <initializer_list>

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
  PM.add(new MPAvailable());
}
static RegisterStandardPasses RegisterMyPass(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerSkeletonPass);

void MPAvailable::getAnalysisUsage(AnalysisUsage& AU) const {
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<ScalarEvolutionWrapperPass>();
  AU.addRequired<DependenceAnalysisWrapperPass>();
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

  for (StructType* st : M.getIdentifiedStructTypes()) {
    std::vector<Type*> plist;
    for (Type* type : st->elements()) {
      if (type->isPointerTy()) {
        plist.push_back(XMM);
      } else
        plist.push_back(type);
    }
    StructType* newStructTy =
        StructType::create(plist, st->getName().str() + ".new.struct");
    strucTyToStructTy[st] = newStructTy;
  }
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

bool MPAvailable::runOnModule(Module& M) {
  DL = &M.getDataLayout();

  module = &M;

  createXmmStructTy(M);
  // replaceStructTy(M);
  // preprocessModule(M);
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
    createWrappingFunction(F);
  }
  for (auto& F : M) {
   createWrappingMain(F);
  }
  std::vector<Function*> workList(willBeDeletedFunctions.begin(),
                                  willBeDeletedFunctions.end());
  
  while (!workList.empty()) {
    Function* F = workList.front();
    if (F->users().empty()) {
      workList.erase(workList.begin());
      F->eraseFromParent();
    } else {
      // for(Value* use : F->users()) valuePrint(use, "F User");
      workList.erase(workList.begin());
      workList.push_back(F);
    }
  }
  errs() << "Deleting process finished!\n";
  
  // verifyModule(M);
  eraseRemoveInstruction();
  // M.dropAllReferences();
  // for (auto& F : M) {
  //   errs() << "Clearing ... " << F.getName() << "\n";
  //   // if (F.getName().str() == "Wrapping_globalReturnsTrue") continue;
  //   F.dropAllReferences();
  //   Constant* cons = dyn_cast<Constant>(&F);
  //   cons->removeDeadConstantUsers();
  //   delete &F;
  // }
  return false;
}

void MPAvailable::analyzeGEPforFunction(Function& F) {
  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E;) {
    inst_iterator vI = I;
    I++;
    if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(&*vI))
      splatGEP(&*vI);
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
          debugBCI(bci);
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
                          IRBuilder<>& irb) {
  // Input: malloc 류 함수의 리턴 값(i8*)
  // Output: array[2] (i64) 산술연산 instruction
  // Replace: Use는 bitcast 또는 StoreInst 들의 Value를 바꾸어 줌
  // base 태그 생성 테스트 끝
  // errs() << I << "\n";
  Value* ptr = dyn_cast<Value>(&I);  // maskMallocWrapper(irb, I);

  if (isStackValue(&I)) return;

  Value* Size = instrumentWithByteSize(irb, &I, *DL);

  Value* newSize;

  Value* allocaVar;
  BitCastInst* bci = nullptr;
  Instruction* origStore;
  if (bci = dyn_cast<BitCastInst>(I.getNextNode())) {
    allocaVar = bci->getNextNode()->getOperand(1);
    origStore = bci->getNextNode();
  } else {
    allocaVar = I.getNextNode()->getOperand(1);
    origStore = I.getNextNode();
  }
  //일단 태그 만들기

  Value* OvSz = createMask(irb, Size, module->getContext());
  Value* PtrInt = irb.CreatePtrToInt(ptr, irb.getInt64Ty());
  Value* emptyVec = Constant::getNullValue(XMM);

  Value* vec0 = irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
  Value* vec1 = irb.CreateInsertElement(vec0, PtrInt, 1);

  irb.CreateStore(vec1, allocaVar);
  // Value* mask = irb.CreateInsertElement(emptyVector, OvSz,
  // ConstantInt::get(IntegerType::get(I.getContext(), 32),0),
  // allocaVar->getName()+".MASK");

  // Value* indexList[2] = {ConstantInt::get(OvSz->getType(), 0),
  // ConstantInt::get(OvSz->getType(), 0)}; Value* mask =
  // irb.CreateInBoundsGEP(allocaVar, indexList, allocaVar->getName()+".MASK");
  // continueList.insert(dyn_cast<Instruction>(mask));
  // Value* indexList_[2] = {ConstantInt::get(OvSz->getType(), 0),
  // ConstantInt::get(OvSz->getType(), 1)}; Value* address =
  // irb.CreateInBoundsGEP(allocaVar, indexList_, allocaVar->getName()+".PTR");
  // continueList.insert(dyn_cast<Instruction>(address));
  // valuePrint(mask, "mask");

  // //irb.CreateInsertElement(emptyVector, PtrInt,
  // ConstantInt::get(IntegerType::get(I.getContext(), 32),1),
  // allocaVar->getName()+".POINTER");
  // typePrint(cast<PointerType>(mask->getType())->getElementType(), "mask
  // type"); typePrint(OvSz->getType(), "OvSz"); irb.CreateStore(OvSz, mask);
  // irb.CreateStore(PtrInt, address);

  origStore->eraseFromParent();
  if (bci) bci->eraseFromParent();
}

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
    if (valToVal.find(Val) != valToVal.end())
      Op = valToVal[Val];
    else {
      assert(isa<Constant>(Val) && "Val must be constant!");
      Op = Val;
    }
    uint64_t Size = DL.getTypeAllocSize(GTI.getIndexedType()) & PtrSizeMask;
    Value* Offset;
    if (Constant* OpC = dyn_cast<Constant>(Op)) {
      if (OpC->isZeroValue()) continue;

      // Handle a struct index, which adds its field offset to the pointer.
      if (StructType* STy = GTI.getStructTypeOrNull()) {
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

void MPAvailable::splatGEP(Instruction* I) {
  // 이거를 먼저 손봅시다....
  // offset을 미리 만들어놓고 저장하기
  // 타입 정보 반영
  //
  GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(I);
  IRBuilder<> irb(getInsertPointAfter(gep));

  Value* xmm_pointer;
  Value* xmm_offset;
  GetElementPtrInst* PreemptedGep = nullptr;

  if (!gep) return;
  if (instructionToL4.find(gep) == instructionToL4.end()) return;
  if (allocaGEPSet.find(dyn_cast<Value>(gep)) != allocaGEPSet.end())
    return;  //내가 만든 gep instruction

  // if (gep->getPointerOperand()->getType()->getContainedType(0) !=
  // XMM_POINTER) return ; XMM 포인터는 기존의 포인터 변수 대신에 내가 만든
  // 구조체로 할당되기 때문에 gep 이전의 load도 다시 해야 됨
  //

  // gep를 없애고 펼쳐놓자

  bool isPositive = hasNegativeOffset(gep);

  Value* base =
      gep->getPointerOperand()
          ->stripPointerCasts();  // base는 load 인스트럭션, 그리고 int128

  LoadInst* origLoad = dyn_cast<LoadInst>(base);  //추후에 이 LOAD는 바뀜

  Value* tag;
  uint64_t constOffset;

  std::vector<User*> Users(gep->user_begin(), gep->user_end());

  Value* Diff;
  Value* addOffset;
  ConstantInt* ConstOffset = nullptr;
  APInt ConstOffsetVal(64, 0);
  IntegerType* PtrIntTy = getPtrIntTy(gep->getContext());
  std::string Prefix = std::string(base->getName()) + "." + ".array.";

  // cast<Instruction>(irb.CreatePtrToInt(ptrToXMM[base], PtrIntTy, Prefix +
  // "int"));
  Value* PtrInt = irb.CreatePtrToInt(base, PtrIntTy);
  if (gep->accumulateConstantOffset(*DL, ConstOffsetVal))
    ConstOffset = irb.getInt(ConstOffsetVal);

  // const 일경우 -1. 양수, 2. 음수
  // const 아닐 경우 - 1. 양수, 음수
  //속도를 위해선 메모리 load나 레지스터 거쳐가는 것을 최대한 줄일것
  if (ConstOffset && isPositive) {
    // const 이면서 양수일 때,
    Diff = ConstOffset;
    addOffset = irb.CreateAdd(PtrInt, ConstOffset);
  } else if (isPositive) {
    // const 아니고 양수일 때,
    Diff = EmitGEPOffset(&irb, *DL, gep);
    addOffset = irb.CreateAdd(PtrInt, Diff);
  } else if (ConstOffset) {
    // const 인데, 음수임
    constOffset = -(ConstOffset->getSExtValue());
    addOffset = irb.CreateAdd(PtrInt, ConstOffset);
  } else {
    Diff = EmitGEPOffset(&irb, *DL, gep);
    addOffset = irb.CreateAdd(PtrInt, Diff);
  }

  // tag를 만들고 나서 보수하는거니까 tag하고 나서 확인하고 해도 되지

  Value* result = irb.CreateIntToPtr(addOffset, gep->getType());
  gep->replaceAllUsesWith(result);

  // continueList.insert(dyn_cast<Instruction>(result));
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
  valuePrint(i, "suboradd");
  if (isXMMTy(i->getOperand(0)->getType())) {
    Value* op1 = i->getOperand(1);
    Value* nullVector = Constant::getNullValue(XMM);
    valuePrint(op1, "op1 print");
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
      valuePrint(si->getValueOperand(), "Store Value");
      valuePrint(si->getPointerOperand(), "Store Pointer");
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
  for (Instruction* inst : willBeRemoveSet) inst->eraseFromParent();
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
      resultPtr, Type::getInt8PtrTy(irb.getContext()), prefix + "_ptr");

  Value* res = irb.CreateBitCast(ptr, origType, prefix + ".unwrap");
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
  for (Function& F : M) {
    if (F.isDeclaration()) continue;
    errs() << F.getName() << "\n";
    F.getFunctionType()->print(errs());
    errs() << "\n";
    for (Instruction& I : instructions(F)) {
      I.print(errs());
      errs() << "\n";
    }
  }
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
        valuePrint(CI->getArgOperand(i), " test");
        ArrayRef<Value*> array = args;
        Type* fType = calledFuncType->getParamType(i);
        Type* aType = array[i]->getType();
        typePrint(fType, "FType");
        typePrint(aType, "aType");
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
  if (F.getName() == "main") return;
  // if (isa<Constant>(&F)) return;
  bool mustWrapped = false;

  std::map<Value*, Value*> valToVal;
  std::map<StringRef, int> argToArg;
  std::map<BasicBlock*, BasicBlock*> basicToBasic;
  std::map<Value*, Type*> valToType;

  Function* newFunc = funcToFunc[&F];
  int i = 0;
  std::vector<Type*> plist;
  for (Argument& arg : F.args()) {
    Value* vArg = dyn_cast<Value>(&arg);
    if (arg.getType()->isPointerTy()) {
      plist.push_back(Type::getInt64Ty(F.getContext()));
      plist.push_back(Type::getInt64Ty(F.getContext()));
      argToArg[vArg->getName()] = i;
      i++;
    } else {
      plist.push_back(arg.getType());
      argToArg.insert(std::pair<StringRef, int>(vArg->getName(), i));
    }
    i++;
  }

  for (BasicBlock& BB : F.getBasicBlockList()) {
    BasicBlock* clone =
        BasicBlock::Create(newFunc->getContext(), newFunc->getName(), newFunc);
    valToVal[&BB] = clone;
    basicToBasic[&BB] = clone;
  }
  for (BasicBlock& BB : F.getBasicBlockList()) {
    cloneBB(newFunc, &BB, argToArg, valToVal);
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
        if (arg->getType()->isPointerTy()) {
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
          // if (Type* Ty = Attrs.getAttribute(i, TypedAttr).getValueAsType()) {
          // Attrs = Attrs.replaceAttributeType(CI->getContext(), i, TypedAttr,
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
                                 std::map<Value*, Value*>& valToVal) {
  BasicBlock* clone = dyn_cast<BasicBlock>(valToVal[orig]);

  IRBuilder<> irb(clone);
  for (Instruction& I : orig->getInstList()) {
    // clone->getInstList().push_back(newInst);

    // Reset the insert point of IRB
    switch (I.getOpcode()) {
      case Instruction::Alloca: {
        // PASS
        AllocaInst* allocaInst = dyn_cast<AllocaInst>(&I);
        if (allocaInst->getAllocatedType()->isPointerTy()) {
          Value* replace = irb.CreateAlloca(XMM, nullptr, I.getName());

          // AllocaInst* newAI = dyn_cast<AllocaInst>(newInst);
          // newAI->setAllocatedType(XMM);
          // newAI->setAlignment(Align(16));
          valToVal[dyn_cast<Value>(&I)] = replace;

          // newInst->eraseFromParent();
        } else if (allocaInst->getAllocatedType()->isStructTy()) {
          StructType* allocaSt =
              dyn_cast<StructType>(allocaInst->getAllocatedType());

          if (strucTyToStructTy.count(allocaSt) > 0) {
            StructType* newType = strucTyToStructTy[allocaSt];
            IRBuilder<> irb(&I);
            Value* newVal =
                irb.CreateAlloca(newType->getPointerTo(), nullptr,
                                 allocaInst->getName() + ".xmm.struct");
            valToVal[dyn_cast<Value>(&I)] = newVal;
          }
        } else {
          Instruction* newInst = I.clone();
          valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
          clone->getInstList().push_back(newInst);
        }
        break;
      }
      case Instruction::Store: {
        Instruction* beforeBefore =
            getInsertPointBefore(getInsertPointBefore(&I));
        Value* v0 = I.getOperand(0);            // value
        Value* v1 = valToVal[I.getOperand(1)];  // pointer
        if (argToArg.count(v0->getName())) {
          // Argument를 저장하는 과정
          // Argument 저장 통과
          AllocaInst* newAI = dyn_cast<AllocaInst>(I.getOperand(1));
          int index = argToArg[v0->getName()];
          if (newAI->getAllocatedType()->isPointerTy()) {
            Value* ptr = cloneFunc->getArg(index);

            Value* tag = cloneFunc->getArg(index + 1);
            Value* nullL4 = Constant::getNullValue(XMM);
            Value* tagVec = irb.CreateInsertElement(nullL4, tag, (uint64_t)0);
            Value* ptrToInt =
                irb.CreatePtrToInt(ptr, Type::getInt64Ty(ptr->getContext()));
            Value* L4 = irb.CreateInsertElement(tagVec, ptrToInt, 1);

            Instruction* inst = dyn_cast<Instruction>(v1);

            irb.CreateStore(L4, v1);
          } else {
            int index = argToArg[v0->getName()];
            Value* val = cloneFunc->getArg(index);
            irb.CreateStore(val, v1);
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

          if (isXMMTy(newPointer->getType())) {
            // 통과
            instPrint(&I, "I");
            valuePrint(newPointer, "newPointer");
            Value* clearTag = ununTag(newPointer, pointer->getType(), irb);
            if(isXMMTy(newValue->getType())) {
              Value* clearVal = ununTag(newValue, value->getType(), irb);
              irb.CreateStore(clearVal, clearTag);
            } else irb.CreateStore(newValue, clearTag);
          } else {
            // Pointer 가 XMM TYPE 이 아님 근데 왜 코드가 이러지?

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
                    irb.CreateInsertElement(vec1, nullValue, uint64_t(1));
                irb.CreateStore(vec2, newPointer);
              }
            } else {
              irb.CreateStore(newValue, newPointer);
            }
          }
        } else {
          // 글로벌 변수
          // value is constant
          StoreInst* si = dyn_cast<StoreInst>(&I);
          Value* ptr = si->getPointerOperand();
          if (GlobalValue* gv = dyn_cast_or_null<GlobalValue>(ptr)) {
            Value* value = si->getValueOperand();
            Value* newValue = valToVal.count(value) ? valToVal[value] : value;
            irb.CreateStore(newValue, ptr);
          } else {
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
            Type* type = valueToType[origPointer];
            Value* clearTagPointer = ununTag(
                pointer, origPointer->getType(), irb,
                origPointer->hasName() ? origPointer->getName().str() : "");
            Value* replaceInst = irb.CreateLoad(
                clearTagPointer, origPointer->hasName()
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
            errs() << "this instruction has problem!\n";
            instPrint(&I, "problem");
            instPrint(getInsertPointBefore(&I), "before");
          }
        }
        break;
      }
      case Instruction::GetElementPtr: {
        // 구조체, 배열, 포인터에 대해서 모두 생각해야 함
        // PASS

        GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(&I);
        Value* base = gep->getPointerOperand();
        Value* realBase = gep->getPointerOperand();

        if (valToVal.count(base) > 0) {
          Value* newBase = valToVal[base];

          if (base->getType()->getPointerElementType()->isStructTy()) {
            //구조체일 때
            if (gep->getType() != base->getType()) {
              // load 까지 해놔야 함
              // 왜냐? gep struct 면 return 이 멤버임
              // 그럼 load 한 상태에서 gep를 만들면 되겠네?
              // 우와 나 천재냐?
              //
              StructType* newSt =
                  dyn_cast<StructType>(strucTyToStructTy[dyn_cast<StructType>(
                      base->getType()->getPointerElementType())]);

              Value* newGepBase =
                  ununTag(newBase, newSt->getPointerTo(), irb, "unwrap.struct");

              Value* newGEP;
              if (gep->isInBounds()) {
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

                newGEP = irb.CreateInBoundsGEP(newGepBase, plist);
                valToVal[dyn_cast<Value>(gep)] = newGEP;

              } else {
                // 만약 같은 타입이라면 load할 필요가 없겠찌?
              }
            }
          } else if (base->getType()->getPointerElementType()->isArrayTy()) {
            if (gep->isInBounds()) {
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

              Value* newGEP = irb.CreateInBoundsGEP(newBase, plist);
              valToVal[dyn_cast<Value>(gep)] = newGEP;

            } else {
              // 만약 같은 타입이라면 load할 필요가 없겠찌?
            }
          } else if (isXMMTy(newBase->getType())) {
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
              Value* newGEP = irb.CreateInBoundsGEP(newBase, plist);
              valToVal[dyn_cast<Value>(&I)] = newGEP;
            } else {
              Value* newGEP = irb.CreateGEP(newBase, plist);
              valToVal[dyn_cast<Value>(&I)] = newGEP;
            }
          }
          break;
        } else {
          // break 넣지 않고 default block에서 처리
          errs() << "this instruction has problem!\n";
          instPrint(&I, "problem");
        }
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

          cloneI = I.clone();
          clone->getInstList().push_back(cloneI);
          CI = dyn_cast<CallInst>(cloneI);

          ConstantExpr* cExpr = dyn_cast<ConstantExpr>(CI->getCalledOperand());

          Constant* newCons = cloneConstantExpr(cExpr);
          CI->setCalledOperand(newCons);
          Value* calleeVal = CI->getCalledOperand();
          // if (isa<Instruction>(calleeVal))
          //   errs() << "Test ConstantExpr is Instruction\n";
          // if (checks.count(cExpr) > 0) {
          //   errs() << "내가 생각한 것이 맞음 ㅇㅇ\n";
          //   errs() << cExpr << " : check!!!\n";
          // }
          // errs() << "\n";
          for (int i = 0; i < cExpr->getNumOperands(); i++) {
            Value* calleeFunc = cExpr->getOperand(i);
            if (Function* func = dyn_cast_or_null<Function>(calleeFunc)) {
              if (funcToFunc.count(func) > 0) {
                Function* newFunc = funcToFunc[func];
                cExpr->setOperand(i, newFunc);
                checks.insert(cExpr);
              }
            }
          }

          IRBuilder<> tempIRB(cloneI);

          for (unsigned int i = 0; i < CI->getNumArgOperands(); i++) {
            Value* arg = CI->getArgOperand(i);
            if (valToVal.count(arg) > 0) {
              Value* newArg = valToVal[arg];
              if (isXMMTy(newArg->getType())) {
                Value* newXMM = ununTag(newArg, arg->getType(), tempIRB);
                CI->setArgOperand(i, newXMM);
              } else
                CI->setArgOperand(i, newArg);
            }
          }
          valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(cloneI);
          break;
        }
        if (callee->isDeclaration()) {
          // 포인터들 다 언랩핑하기
          // 여기서는 오퍼랜드만 교체하기
          cloneI = I.clone();
          clone->getInstList().push_back(cloneI);

          CI = dyn_cast<CallInst>(cloneI);
          IRBuilder<> tempIRB(cloneI);
          for (unsigned int i = 0; i < CI->getNumArgOperands(); i++) {
            Value* arg = CI->getArgOperand(i);

            if (valToVal.count(arg) > 0) {
              Value* newArg = valToVal[arg];
              if (isXMMTy(newArg->getType())) {
                Value* newXMM = ununTag(newArg, arg->getType(), tempIRB);
                CI->setArgOperand(i, newXMM);
              } else
                CI->setArgOperand(i, newArg);
            }
          }
          valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(cloneI);
          // malloc 때문에 break; 안함
        }
        if (isAllocation(&I)) {
          Value* ptr = dyn_cast<Value>(cloneI);  // maskMallocWrapper(irb, I);

          if (isStackValue(&I)) break;

          Value* Size = instrumentWithByteSize(irb, cloneI, *DL);
          Instruction* next = I.getNextNode();
          if (BitCastInst* bci = dyn_cast_or_null<BitCastInst>(next)) {
            Type* destTy = bci->getDestTy();
            if (destTy->isStructTy()) {
              StructType* st = dyn_cast<StructType>(destTy);
              if (strucTyToStructTy.count(st) > 0) {
                IRBuilder<> tempIRB(cloneI);
                StructType* newTy = strucTyToStructTy[st];
                uint64_t typeSize = DL->getTypeAllocSize(st);
                Constant* typeSizeCons =
                    ConstantInt::get(irb.getInt64Ty(), typeSize);
                Value* div = tempIRB.CreateUDiv(Size, typeSizeCons);

                uint64_t newTypeSize = DL->getTypeAllocSize(newTy);
                Constant* newTypeSizeCons =
                    ConstantInt::get(irb.getInt64Ty(), newTypeSize);
                Value* newSize = tempIRB.CreateMul(div, newTypeSizeCons);
                CallInst* tempCI = dyn_cast<CallInst>(cloneI);
                tempCI->setArgOperand(0, newSize);
                Size = newSize;
              }
            }
          }

          Value* allocaVar;
          BitCastInst* bci = nullptr;
          Instruction* origStore;

          //일단 태그 만들기

          Value* OvSz = createMask(irb, Size, module->getContext());
          Value* PtrInt = irb.CreatePtrToInt(ptr, irb.getInt64Ty());
          Value* emptyVec = Constant::getNullValue(XMM);

          Value* vec0 = irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
          Value* vec1 = irb.CreateInsertElement(vec0, PtrInt, 1);
          valToVal[dyn_cast<Value>(&I)] = vec1;
          break;
        } else if (funcToFunc.count(callee) > 0) {
          // 함수가 대체되는 경우
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
                if (isXMMTy(newArg->getType())) {
                  Value* ptr = irb.CreateExtractElement(newArg, (uint64_t)1);
                  Value* tag = irb.CreateExtractElement(newArg, (uint64_t)0);
                  plist.push_back(ptr);
                  plist.push_back(tag);
                } else {
                  // constant null 채워서 주기
                  Value* ptr =
                      newArg->getType()->isPointerTy()
                          ? irb.CreatePtrToInt(newArg, irb.getInt64Ty())
                          : irb.CreateBitCast(newArg, irb.getInt64Ty());
                  Value* tag = ConstantInt::get(irb.getInt64Ty(), 0);
                  plist.push_back(ptr);
                  plist.push_back(tag);
                }
              } else {
                Value* newArg;
                if (isa<Instruction>(arg)) {
                  Instruction* newInst = I.clone();
                  clone->getInstList().push_back(newInst);
                  newArg = irb.CreatePtrToInt(newInst, irb.getInt64Ty());
                } else
                  newArg = irb.CreatePtrToInt(arg, irb.getInt64Ty());

                plist.push_back(newArg);
                Value* nullValue = Constant::getNullValue(irb.getInt64Ty());
                plist.push_back(nullValue);
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
        }
        break;
      }
      case Instruction::ICmp: {
        Instruction* newInst = I.clone();
        newInst->setName(I.getName());
        ICmpInst* iCmp = dyn_cast<ICmpInst>(&I);
        for (int i = 0; i < I.getNumOperands(); i++) {
          Value* op = I.getOperand(i);
          if (valToVal.count(op) > 0) {
            Value* newOp = valToVal[op];
            if (isXMMTy(newOp->getType())) {
              // it need only ptr in this instruction;
              // 포인터가 null 인지 아닌지 확인하기도 해서 그럼
              // 개선할 가능성 있을듯
              Value* replaceOp =
                  ununTag(newOp, I.getOperand(0)->getType(), irb);
              newInst->setOperand(i, replaceOp);
            } else {
              newInst->setOperand(i, newOp);
            }
          }
        }
        clone->getInstList().push_back(newInst);
        valToVal[dyn_cast<Value>(&I)] = newInst;

        break;
      }
      case Instruction::BitCast:
        // If it is for malloc instruction, it should be deleted.
        // L4 pointer don't need bitcast instruction.
        // 그냥 배열일때 필요함, 하아 이걸 어떻게 고치나...
        if (valToVal.count(I.getOperand(0)) > 0) {
          if (isAllocation(getInsertPointBefore(&I))){ 
            valToVal[dyn_cast<Value>(&I)] = valToVal[I.getOperand(0)];
            break;
          }

          Value* op = valToVal[I.getOperand(0)];
          if (isXMMTy(op->getType())) {
            Value* newOp = ununTag(op, I.getOperand(0)->getType(), irb);
            Instruction* newInst = I.clone();
            clone->getInstList().push_back(newInst);
            newInst->setOperand(0, newOp);
            valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
          } else {
            Instruction* newInst = I.clone();
            newInst->setName(I.getName());
            newInst->setOperand(0, op);
            clone->getInstList().push_back(newInst);
            valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
          }
          break;
        } else {
        }
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
      default:
        Instruction* newInst = I.clone();
        newInst->setName(I.getName());
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
  if (F.getName() == "main") return;
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
    if (arg.getType()->isPointerTy()) {
      plist.push_back(Type::getInt64Ty(F.getContext()));
      plist.push_back(Type::getInt64Ty(F.getContext()));
      i++;
    } else {
      plist.push_back(arg.getType());
    }
    i++;
  }

  FunctionType* newFT =
      FunctionType::get(F.getReturnType(), plist, F.isVarArg());
  newFunc = Function::Create(newFT, F.getLinkage(), "Wrapping_" + F.getName());

  std::vector<AttributeSet> argAttrVec;
  Module* m = F.getParent();

  m->getFunctionList().insert(F.getIterator(), newFunc);
  // m->getFunctionList().insert(Module::iterator(F), newFunc);

  newFunc->copyAttributesFrom(&F);
  AttributeList newAttrList = newFunc->getAttributes();

  for (int i = 0; i < F.arg_size(); i++) {
    newAttrList = newAttrList.removeParamAttributes(F.getContext(), i);
  }

  const AttrBuilder newAttrBuilder;

  for (int i = 0; i < newFunc->arg_size(); i++)
    newAttrList = newAttrList.addParamAttributes(newFunc->getContext(), i,
                                                 newAttrBuilder);
  const AttributeList resultAttrList = newAttrList;

  newFunc->setAttributes(resultAttrList);

  funcToFunc[&F] = newFunc;
  wrappingFunctions.insert(newFunc);
  willBeDeletedFunctions.insert(&F);

  // replaceFunction(newFunc, &F);
  // F.eraseFromParent();
}

void MPAvailable::createWrappingMain(Function& F) {
  // This function wrap only main function or init function
  if (F.getName().find("main") == std::string::npos) return;

  // 여기서 해야할건 기존에 했던거 같은데
  // 다만 메인의 인자를 어떻게 받을것인가 고민하기
  // 메인 인자는 포인터만 받고 tag에는 걍 null value 넣기
  // 기존에 했던것을 clone 식으로 바꾸자
  // 그게 더 안정적인듯
  //
  // cloneBB 와 다른 점, 원래 있떤 함수를 고치는 것이라
  // 기존의 인스트럭션이 보존이 됨

  std::map<Value*, Value*> valToVal;
  DenseSet<Instruction*> willBeDeletedInsts;
  DenseSet<Instruction*> continueList;

  for (Instruction& I : instructions(F)) {
    if (continueList.count(&I) > 0) continue;
    switch (I.getOpcode()) {
      case Instruction::Alloca: {
        // 통과
        AllocaInst* alloca = dyn_cast<AllocaInst>(&I);
        if (alloca->getAllocatedType()->isPointerTy()) {
          if (alloca->getName().find(".addr") != std::string::npos) {
            // It is function argument variable, so don't change xmm type
            break;
          }
          IRBuilder<> irb(&I);
          Value* newVal =
              irb.CreateAlloca(XMM, nullptr, alloca->getName() + ".xmm");
          valToVal[dyn_cast<Value>(&I)] = newVal;
          willBeDeletedInsts.insert(&I);
        } else if (alloca->getAllocatedType()->isStructTy()) {
          StructType* allocaSt =
              dyn_cast<StructType>(alloca->getAllocatedType());

          if (strucTyToStructTy.count(allocaSt) > 0) {
            StructType* newType = strucTyToStructTy[allocaSt];
            IRBuilder<> irb(&I);
            Value* newVal = irb.CreateAlloca(newType->getPointerTo(), nullptr,
                                             alloca->getName() + ".xmm.struct");
            valToVal[dyn_cast<Value>(&I)] = newVal;
            willBeDeletedInsts.insert(&I);
          }
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
          if (isXMMTy(newPointer->getType())) {
            Value* unwrapPtr = ununTag(newPointer, origPointer->getType(), irb);
            irb.CreateStore(val, unwrapPtr);
            willBeDeletedInsts.insert(&I);
          }
          if (AllocaInst* ai = dyn_cast<AllocaInst>(newPointer)) {
            if (isXMMTy(ai->getAllocatedType())) {
              if (isXMMTy(val->getType())) {
                irb.CreateStore(val, newPointer);
                willBeDeletedInsts.insert(&I);
              } else {
                Value* nullVec = Constant::getNullValue(XMM);
                Value* replaceVal;
                if (val->getType()->isPointerTy())
                  replaceVal = irb.CreatePtrToInt(val, irb.getInt64Ty());
                else if (isXMMTy(val->getType()))
                  replaceVal = val;
                Value* vecPtr = irb.CreateInsertElement(nullVec, replaceVal, 1);
                irb.CreateStore(vecPtr, newPointer);
                willBeDeletedInsts.insert(&I);
              }
            }
          }
        }
        break;
      }
      case Instruction::Load: {
        Value* ptr = I.getOperand(0);
        if (valToVal.count(ptr) > 0) {
          IRBuilder<> irb(&I);
          Value* newPtr = valToVal[ptr];
          if (isXMMTy(newPtr->getType())) {
            Value* unwrapPtr = ununTag(newPtr, ptr->getType(), irb);
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
          IRBuilder<> irb(CI);
          for (unsigned int i = 0; i < CI->getNumArgOperands(); i++) {
            Value* arg = CI->getArgOperand(i);
            if (valToVal.count(arg) > 0) {
              Value* newArg = valToVal[arg];
              if (isXMMTy(newArg->getType())) {
                Value* newXMM = ununTag(newArg, arg->getType(), irb);
                CI->setArgOperand(i, newXMM);
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
              } else
                CI->setArgOperand(i, newArg);
            }
          }
        }

        if (isAllocation(&I)) {
          IRBuilder<> irb(getInsertPointAfter(&I));

          Value* ptr = dyn_cast<Value>(&I);  // maskMallocWrapper(irb, I);
          Value* Size = instrumentWithByteSize(irb, &I, *DL);
          //역계산하자

          Instruction* next = I.getNextNode();
          if (BitCastInst* bci = dyn_cast_or_null<BitCastInst>(next)) {
            Type* destTy = bci->getDestTy();
            if (destTy->isStructTy()) {
              StructType* st = dyn_cast<StructType>(destTy);
              if (strucTyToStructTy.count(st) > 0) {
                StructType* newTy = strucTyToStructTy[st];
                uint64_t typeSize = DL->getTypeAllocSize(st);
                Constant* typeSizeCons =
                    ConstantInt::get(irb.getInt64Ty(), typeSize);
                Value* div = irb.CreateUDiv(Size, typeSizeCons);

                uint64_t newTypeSize = DL->getTypeAllocSize(newTy);
                Constant* newTypeSizeCons =
                    ConstantInt::get(irb.getInt64Ty(), newTypeSize);
                Value* newSize = irb.CreateMul(div, newTypeSizeCons);

                CI->setArgOperand(0, newSize);
                Size = newSize;
              }
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
                if (isXMMTy(newArg->getType())) {
                  Value* ptr = irb.CreateExtractElement(newArg, (uint64_t)1);
                  Value* tag = irb.CreateExtractElement(newArg, (uint64_t)0);
                  plist.push_back(ptr);
                  plist.push_back(tag);
                } else {
                  Value* ptr =
                      newArg->getType()->isPointerTy()
                          ? irb.CreatePtrToInt(newArg, irb.getInt64Ty())
                          : irb.CreateBitCast(newArg, irb.getInt64Ty());
                  Value* tag = ConstantInt::get(irb.getInt64Ty(), 0);
                  plist.push_back(ptr);
                  plist.push_back(tag);
                }
              } else {
                Value* newArg = irb.CreatePtrToInt(arg, irb.getInt64Ty());
                plist.push_back(newArg);
                // if
                Value* nullValue = Constant::getNullValue(irb.getInt64Ty());
                plist.push_back(nullValue);
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
        }
        break;
      }
      case Instruction::BitCast: {
        // don't need bitcast.
        if (valToVal.count(I.getOperand(0)) > 0) {
          Value* op = valToVal[I.getOperand(0)];
          valToVal[dyn_cast<Value>(&I)] = op;
          willBeDeletedInsts.insert(&I);
          break;
        }
        break;
      }
      case Instruction::GetElementPtr: {
        // 구조체, 배열, 포인터에 해당하는 3가지를 구현할 것
        //
        //
        IRBuilder<> irb(getInsertPointAfter(&I));
        GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(&I);
        Value* base = gep->getPointerOperand();
        if (valToVal.count(base) > 0) {
          Value* newBase = valToVal[base];
          if (base->getType()->getPointerElementType()->isStructTy()) {
            StructType* newSt =
                dyn_cast<StructType>(strucTyToStructTy[dyn_cast<StructType>(
                    base->getType()->getPointerElementType())]);

            Value* newGepBase =
                ununTag(newBase, newSt->getPointerTo(), irb, "unwrap.struct");

            Value* newGEP;
            if (gep->isInBounds()) {
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

              newGEP = irb.CreateInBoundsGEP(newGepBase, plist);
              valToVal[dyn_cast<Value>(gep)] = newGEP;
            }
          } else if (base->getType()->getPointerElementType()->isArrayTy()) {
            if (gep->isInBounds()) {
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

              Value* newGEP = irb.CreateInBoundsGEP(newBase, plist);
              valToVal[dyn_cast<Value>(gep)] = newGEP;

            } else {
              // 만약 같은 타입이라면 load할 필요가 없겠찌?
            }
          } else if (isXMMTy(newBase->getType())) {
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
          } else if (newBase->getType()
                         ->getPointerElementType()
                         ->isStructTy()) {
            if (gep->isInBounds()) {
              std::vector<Value*> plist(gep->idx_begin(), gep->idx_end());
              Value* newGEP = irb.CreateInBoundsGEP(newBase, plist);
              valToVal[dyn_cast<Value>(gep)] = newGEP;
              willBeDeletedInsts.insert(&I);
            }
          }
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
                  ununTag(newOp, I.getOperand(0)->getType(), irb);
              I.setOperand(i, replaceOp);
            } else {
              I.setOperand(i, newOp);
            }
          }
        }
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
  std::vector<Instruction*> workList(willBeDeletedInsts.begin(),
                                     willBeDeletedInsts.end());
  while (!workList.empty()) {
    Instruction* inst = workList.front();

    if (inst->users().empty()) {
      workList.erase(workList.begin());
      inst->eraseFromParent();
    } else {
      // instPrint(inst, " use inst");
      // for(Value* use: inst->users()){
      //   valuePrint(use, "using inst ");
      // }
      workList.erase(workList.begin());
      workList.push_back(inst);
    }
  }
}
Value* MPAvailable::createOffsetMask(IRBuilder<>& irb, Value* offset) {
  Value* over = irb.CreateShl(offset, 32);
  Value* result = irb.CreateOr(over, offset);
  return result;
}

// void MPAvailable::replaceStructTy(Module& M) {
//   for (Function& F : M) {
//     replaceStructTyInFunction(F);
//   }
// }
// void MPAvailable::replaceStructTyInFunction(Function& F) {
//   // gep만 펼치기
//   for (Instruction& I : instructions(F)) {
//     if (I.getOpcode() == Instruction::GetElementPtr) {
//       IRBuilder<> irb(&I);
//       GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(&I);
//       gep_type_iterator GTI = gep_type_begin(gep);
//       Value* base = gep->getPointerOperand()->stripPointerCasts();
//       instPrint(gep, "original gep: ");
//       for (User::op_iterator i = gep->op_begin() + 1, e = gep->op_end(); i
//       != e;
//            ++i, ++GTI) {
//         Value* Op = *i;

//         base = irb.CreateGEP(GTI.getIndexedType(), base, Op);
//         valuePrint(base, "split gep ");
//       }
//       if(base != gep->getPointerOperand()->stripPointerCasts()) {
//         typePrint(gep->getType(), "orig gep type");
//         typePrint(base->getType(), "replacing type");
//         gep->replaceAllUsesWith(base);
//         gep->eraseFromParent();
//       }
//     }
//   }
// }

static Constant* cloneConstantExpr(ConstantExpr* cExpr) {
  switch (cExpr->getOpcode()) {
    case Instruction::BitCast:

      return ConstantExpr::getBitCast(cExpr->getOperand(0), cExpr->getType());
    default:
      return cExpr;
  }
}

static RegisterPass<MPAvailable> MPAVAILABLE("mpav", "MPAvailable");