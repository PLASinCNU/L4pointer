#include "MPAvailable.h"

#include <llvm/ADT/TinyPtrVector.h>
#include <llvm/Analysis/DependenceAnalysis.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/Utils/Local.h>
#include <llvm/IR/Attributes.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/NoFolder.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/Casting.h>
#include <llvm/Transforms/Utils/Local.h>
#include <llvm/Transforms/Utils/LoopUtils.h>
#include <stdio.h>

#include <fstream>
#include <initializer_list>
#include <iostream>

#include "AddressSpace.h"
#include "util.h"
// #include "llvm-11/llvm/"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

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
  const char *X##_desc = Y;

#define STATISTICS_DUMP(X) errs() << "    " << X << " : " << X##_desc << "\n";

#endif

STATISTIC(NEpsilon, "Number of Epsilon");
STATISTIC(VALUE_NOT_L4, "Number of Not L4 Value ");

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerSkeletonPass(const PassManagerBuilder &,
                                 legacy::PassManagerBase &PM)
{
  PM.add(new DominatorTreeWrapperPass());
  PM.add(new LoopInfoWrapperPass());
  PM.add(new ScalarEvolutionWrapperPass());
  PM.add(new DependenceAnalysisWrapperPass());
  // PM.add(createVerifierPass());
  PM.add(new MPAvailable());
}
static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_EnabledOnOptLevel0,
                   registerSkeletonPass);

void MPAvailable::getAnalysisUsage(AnalysisUsage &AU) const
{
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

void MPAvailable::createXmmStructTy(Module &M)
{
  // std::list<Type> xmm_elements = {Type::getInt64Ty(M.getContext()),
  // Type::getInt64Ty(M.getContext())};
  ArrayRef<Type *> xmm_element_types(
      {Type::getInt64Ty(M.getContext()), Type::getInt64Ty(M.getContext())});
  XMM = FixedVectorType::get(Type::getInt64Ty(M.getContext()), 2);
  XMM_POINTER = XMM->getPointerTo();
  constantNullXMM = Constant::getNullValue(XMM);
}

StructType *MPAvailable::createStructureType(StructType *st)
{
  if (st->hasName() && isExternalStruct(st->getName().str()))
  {
    return st;
  }
  if (isExternStruct(st))
    return st;
  if (strucTyToStructTy.count(st) > 0)
  {
    StructType *newSt = strucTyToStructTy[st];
    std::vector<Type *> types;
    for (Type *type : newSt->elements())
    {
      if (type->isStructTy())
      {
        StructType *stElement = dyn_cast<StructType>(type);
        if (strucTyToStructTy.count(stElement) > 0)
        {
          StructType *newStElement = strucTyToStructTy[stElement];
          types.push_back(newStElement);
        }
        else
          types.push_back(type);
      }
      else if (isFunctionPtrTy(type))
      {
        FunctionType *ft = dyn_cast<FunctionType>(
            dyn_cast<PointerType>(type)->getPointerElementType());
        FunctionType *newFt = createFunctionType(ft);
        types.push_back(newFt->getPointerTo());
        // types.push_back(type);
      }
      else if (type->isPointerTy())
      {
        types.push_back(XMM);
      }
      else if (type->isArrayTy())
      {
        ArrayType *aType = dyn_cast<ArrayType>(type);
        if (aType->getArrayElementType()->isPointerTy())
        {
          Type *newArrayType =
              ArrayType::get(XMM, aType->getArrayNumElements());
          types.push_back(newArrayType);
        }
        else
        {
          types.push_back(type);
        }
      }
      else
      {
        types.push_back(type);
      }
    }
    StructType *newStructTy = StructType::create(types, newSt->getName());

    strucTyToStructTy[st] = newStructTy;
    return newStructTy;
  }
  std::vector<Type *> plist;
  bool recursive = false;
  bool isNeededTransform = false;
  for (Type *type : st->elements())
  {
    if (type->isPointerTy())
      isNeededTransform = true;
    if (type->isArrayTy())
    {
      if (ArrayType *at = dyn_cast<ArrayType>(type))
      {
        if (at->getArrayElementType()->isPointerTy())
          isNeededTransform = true;
      }
    }
    if (type->isStructTy())
    {
      if (!isExternStruct(type))
        isNeededTransform = true;
    }
  }

  if (!isNeededTransform)
    return st;
  bool isLater = false;
  for (Type *type : st->elements())
  {
    if (isFunctionPtrTy(type))
    {
      plist.push_back(type);
    }
    else if (type->isPointerTy())
    {
      PointerType *pt = dyn_cast<PointerType>(type);

      // it is linked list, maybe it is not spatial memory pointer.
      plist.push_back(XMM);
    }
    else if (type->isStructTy())
    {
      if (type == st)
      {
        plist.push_back(st);
        recursive = true;
      }
      else if (strucTyToStructTy.count(dyn_cast<StructType>(type)) == 0)
      {
        Type *newType = createStructureType(dyn_cast<StructType>(type));
        plist.push_back(newType);
        isLater = true;
      }
      else
        plist.push_back(type);
    }
    else
      plist.push_back(type);
  }
  std::string newStName = st->isLiteral() ? "" : st->getName().str();
  StructType *newStructTy =
      StructType::create(plist, newStName + ".new.struct");
  strucTyToStructTy[st] = newStructTy;
  // typePrint(newStructTy, "new struct");
  transStructs.insert(newStructTy);
  return newStructTy;
}

void MPAvailable::createGlobalValue()
{
  Module &M = *this->module;
  std::set<GlobalVariable *> addingGVs;
  for (GlobalVariable &GV : M.getGlobalList())
  {
    if (GV.getType()->isFunctionTy())
      continue;
    if (GV.isConstant())
    {

      continue;
    }
    if (addingGVs.count(&GV) > 0)
      continue;
    if (!GV.hasInitializer())
      continue;
    // GV.print(errs());
    // errs() << "\n";

    if (isFunctionPtrTy(GV.getType()))
    {
    }
    if (GV.isDSOLocal() || GV.hasInternalLinkage())
    {
      // GV.print(errs());
      // errs() << "\n";

      if (GV.getValueType()->isArrayTy())
      {
        ArrayType *aType = dyn_cast<ArrayType>(GV.getValueType());
        if (aType->getArrayElementType()->isPointerTy() && !isFunctionPtrTy(aType->getArrayElementType()))
        {
          removeGlobals.push_back(&GV);

          ArrayType *newAtype = ArrayType::get(XMM, aType->getArrayNumElements());
          GlobalVariable *gvar_ptr_array = new GlobalVariable(
              /*Module=*/M,
              /*Type=*/newAtype,
              /*isConstant=*/false,
              /*Linkage=*/GlobalValue::InternalLinkage,
              /*Initializer=*/0, // has initializer, specified
                                 // below
              /*Name=*/GV.getName() + "_NEW");
          gvar_ptr_array->copyAttributesFrom(&GV);
          ConstantAggregateZero *caz = ConstantAggregateZero::get(newAtype);
          gvar_ptr_array->setInitializer(caz);
          unsigned int typeSize = DL->getTypeAllocSize(newAtype);
          // Constant *size = ConstantInt::getIntegerValue(Type::getInt64Ty(aType->getContext()), APInt(64, typeSize * 2));
          Constant *Ovsz = createConstantMask(typeSize, aType->getContext());

          Constant *emptyVec = Constant::getNullValue(XMM);
          Constant *PtrInt = ConstantExpr::getPtrToInt(gvar_ptr_array, IntegerType::getInt64Ty(XMM->getContext()));
          Constant *vec0 = ConstantExpr::getInsertElement(emptyVec, Ovsz, ConstantInt::get(Ovsz->getType(), 0));
          Constant *vec1 = ConstantExpr::getInsertElement(vec0, PtrInt, ConstantInt::get(Ovsz->getType(), 1));
          GlobalVariable *gvar_ptr_abc = new GlobalVariable(
              /*Module=*/M,
              /*Type=*/XMM,
              /*isConstant=*/false,
              /*Linkage=*/GlobalValue::InternalLinkage,
              /*Initializer=*/vec1, // has initializer, specified
                                    // below
              /*Name=*/GV.getName() + "_XMM");
          gvar_ptr_abc->setAlignment(MaybeAlign(16));
          addingGVs.insert(gvar_ptr_array);

          gToGV[&GV] = gvar_ptr_abc;
          arrOfGlobalVal[&GV] = gvar_ptr_abc;
          addingGVs.insert(gvar_ptr_abc);

          continue;
        }
        else
        {
          // typePrint(aType->getArrayElementType(), "array type");
          ArrayType *newAtype;
          GlobalVariable *gvar_ptr_array;
          if (aType->getArrayElementType()->isStructTy())
          {
            Type *newElementType = aType->getArrayElementType();
            if (strucTyToStructTy.count(dyn_cast<StructType>(aType->getArrayElementType())) > 0)
              newElementType = this->strucTyToStructTy[dyn_cast<StructType>(aType->getArrayElementType())];

            newAtype = ArrayType::get(newElementType, aType->getArrayNumElements());
            gvar_ptr_array = new GlobalVariable(
                /*Module=*/M,
                /*Type=*/newAtype,
                /*isConstant=*/false,
                /*Linkage=*/GlobalValue::InternalLinkage,
                /*Initializer=*/0, // has initializer, specified
                                   // below
                /*Name=*/GV.getName() + "_NEW");
            removeGlobals.push_back(&GV);
            ConstantAggregateZero *caz = ConstantAggregateZero::get(newAtype);
            gvar_ptr_array->setAlignment(MaybeAlign(16));
            gvar_ptr_array->setInitializer(caz);
          }
          else if (isFunctionPtrTy(aType->getArrayElementType()))
          {
            Constant *init = GV.getInitializer();
            // 어레이 엘리먼트가 포인터임
            removeGlobals.push_back(&GV);
            PointerType *pt = dyn_cast<PointerType>(aType->getArrayElementType());
            FunctionType *ft = dyn_cast<FunctionType>(pt->getElementType());
            FunctionType *newFt = createFunctionType(ft);

            // ConstantAggregate* ca = dyn_cast<ConstantAggregate>(init);
            ConstantArray *ca = dyn_cast<ConstantArray>(init);
            std::vector<Constant *> plist;
            Function *newFunc;
            for (unsigned int i = 0; i < ca->getNumOperands(); i++)
            {
              Value *op = ca->getOperand(i);
              Function *func = dyn_cast<Function>(op);

              newFunc = funcToFunc[func];
              Constant *cons = dyn_cast<Constant>(newFunc);
              plist.push_back(cons);
              errs() << newFunc->getName() << "\n";
              // ConstantArray::get(newAtype, plist);
            }

            newAtype = ArrayType::get(newFunc->getFunctionType()->getPointerTo(), aType->getArrayNumElements());
            Constant *newInit = ConstantArray::get(newAtype, plist);
            gvar_ptr_array = new GlobalVariable(
                /*Module=*/M,
                /*Type=*/newAtype,
                /*isConstant=*/false,
                /*Linkage=*/GlobalValue::InternalLinkage,
                /*Initializer=*/0, // has initializer, specified
                                   // below
                /*Name=*/GV.getName() + "_FUNCTIONPTR");
            gvar_ptr_array->setInitializer(newInit);
          }
          else
          {
            gvar_ptr_array = &GV;
            newAtype = aType;
          }

          addingGVs.insert(gvar_ptr_array);
          unsigned int typeSize = DL->getTypeAllocSize(newAtype);
          // Constant *size = ConstantInt::getIntegerValue(Type::getInt64Ty(aType->getContext()), APInt(64, typeSize));
          Constant *Ovsz = createConstantMask(typeSize, aType->getContext());
          Constant *emptyVec = Constant::getNullValue(XMM);
          Constant *PtrInt = ConstantExpr::getPtrToInt(gvar_ptr_array, IntegerType::getInt64Ty(XMM->getContext()));
          Constant *vec0 = ConstantExpr::getInsertElement(emptyVec, Ovsz, ConstantInt::get(Ovsz->getType(), 0));
          Constant *vec1 = ConstantExpr::getInsertElement(vec0, PtrInt, ConstantInt::get(Ovsz->getType(), 1));
          GlobalVariable *gvar_ptr_abc = new GlobalVariable(
              /*Module=*/M,
              /*Type=*/XMM,
              /*isConstant=*/false,
              /*Linkage=*/GlobalValue::InternalLinkage,
              /*Initializer=*/vec1, // has initializer, specified
                                    // below
              /*Name=*/GV.getName() + "_XMM");
          gvar_ptr_abc->setAlignment(MaybeAlign(16));
          gToGV[&GV] = gvar_ptr_abc;
          addingGVs.insert(gvar_ptr_abc);
          arrOfGlobalVal[&GV] = gvar_ptr_abc;
          continue;
        }
      }
      if (GV.getValueType()->isPointerTy())
      {
        if (Constant *initCons = GV.getInitializer())
        {
          if (initCons->isNullValue())
          {
            GlobalVariable *gvar_ptr_abc = new GlobalVariable(
                /*Module=*/M,
                /*Type=*/XMM,
                /*isConstant=*/false,
                /*Linkage=*/GlobalValue::InternalLinkage,
                /*Initializer=*/constantNullXMM, // has initializer, specified
                                                 // below
                /*Name=*/GV.getName() + "_XMM");
            gToGV[&GV] = gvar_ptr_abc;
          }
          else
          {
          }
        }
        else
        {
          GlobalVariable *gvar_ptr_abc = new GlobalVariable(
              /*Module=*/M,
              /*Type=*/XMM,
              /*isConstant=*/false,
              /*Linkage=*/GlobalValue::InternalLinkage,
              /*Initializer=*/0, // has initializer, specified below
              /*Name=*/GV.getName() + "_XMM");
          gvar_ptr_abc->copyAttributesFrom(&GV);
          gToGV[&GV] = gvar_ptr_abc;
          addingGVs.insert(gvar_ptr_abc);
        }
        continue;
      }
      if (Constant *initCons = GV.getInitializer())
      {
        Constant *nullXMM = Constant::getNullValue(XMM);
        // valuePrint(initCons, "initCons");
        if (dyn_cast<PointerType>(initCons->getType())
                ? dyn_cast<PointerType>(initCons->getType())
                      ->getElementType()
                      ->isArrayTy()
                : false)
        {
          // 포인터인데 초기화가 되어있을 경우
          // 아마도 데드코드
          Constant *addr = ConstantExpr::getBitCast(
              initCons, IntegerType::getInt64Ty(M.getContext()));
          unsigned int arrayIntSize = this->DL->getTypeAllocSize(
              dyn_cast<PointerType>(initCons->getType())->getElementType());
          Value *size = ConstantInt::get(
              IntegerType::getInt64Ty(M.getContext()), arrayIntSize);
          Constant *mask = createConstantMask(size, M.getContext());
          Constant *zero = ConstantInt::get(Type::getInt8Ty(M.getContext()), 0);
          Constant *one = ConstantInt::get(Type::getInt8Ty(M.getContext()), 1);
          Constant *vec1 = ConstantExpr::getInsertElement(nullXMM, mask, zero);
          Constant *vec2 = ConstantExpr::getInsertElement(vec1, addr, one);
          GlobalVariable *gvar_ptr_abc = new GlobalVariable(
              /*Module=*/M,
              /*Type=*/XMM,
              /*isConstant=*/false,
              /*Linkage=*/GlobalValue::InternalLinkage,
              /*Initializer=*/vec2, // has initializer, specified below
              /*Name=*/GV.getName() + "_XMM");
          gToGV[&GV] = gvar_ptr_abc;
          addingGVs.insert(gvar_ptr_abc);
        }
        else if (GV.getType()->isPointerTy())
        {
          if (Constant *initCons = GV.getInitializer())
          {
          }
          else
          {
            GlobalVariable *gvar_ptr_abc = new GlobalVariable(
                /*Module=*/M,
                /*Type=*/XMM,
                /*isConstant=*/false,
                /*Linkage=*/GlobalValue::InternalLinkage,
                /*Initializer=*/0, // has initializer, specified below
                /*Name=*/GV.getName() + "_XMM");
            gToGV[&GV] = gvar_ptr_abc;
            addingGVs.insert(gvar_ptr_abc);
          }
        }
      }
    }
  }
}
bool MPAvailable::runOnModule(Module &M)
{
  removeConstantExpr(M);
  // verifyModule(M);
  DL = &M.getDataLayout();
  errs() << "Run On Module\n";
  module = &M;

  runOnStructInstrument(M);
  createXmmStructTy(M);
  replaceStructTy(M);
  checkConstValue(M);
  makeConstAliasList();

  for (auto &F : M)
  {
    if (!F.hasName())
    {
      errs() << "F has no name \n";
      continue;
    }
    if (F.isDeclaration())
      continue;
    declareWrappingFunction(F);
  }

  createGlobalValue();

  printFunction = M.getOrInsertFunction(
      "printf",
      FunctionType::get(IntegerType::getInt32Ty(M.getContext()),
                        PointerType::get(Type::getInt8Ty(M.getContext()), 0),
                        true /* this is var arg func type*/));
  //  verifyGlobalValue(M);
  // preprocessModule(M);

  /*  debug codes
      for (StructType *st : M.getIdentifiedStructTypes()) {
      if (st->isOpaque())
        continue;
      if (isExternStruct(st))
        continue;
      if (st->isPacked())
        errs() << "is Pack : ";
      if (strucTyToStructTy.count(st) > 0) {
        typePrint(st, "original");
        typePrint(strucTyToStructTy[st], "transform");
      }
    } */

  for (auto &F : M)
  {
    if (!F.hasName())
    {
      errs() << "F has no name \n";
      continue;
    }
    if (wrappingFunctions.count(&F) > 0)
      continue;
    if (!(&F))
      continue;
    if (F.isDeclaration())
      continue;

    errs() << F.getName() << "\n";
    createWrappingFunction(F);
  }
  // for (auto& F : M) {
  //   if (!(&F)) continue;
  //   if (F.isDeclaration()) continue;

  //   // createWrappingMain(F);
  // }
  std::vector<Function *> workList(willBeDeletedFunctions.begin(),
                                   willBeDeletedFunctions.end());

  int count = 0;
  int beforeSize = workList.size();
  verifyModule(M);

  removeGlobalValue(M);

  while (!workList.empty())
  {
    Function *F = workList.front();
    if (usedFunctions.count(F) > 0)
    {
      workList.erase(workList.begin());
      continue;
    }
    if (F->users().empty())
    {
      workList.erase(workList.begin());
      // deleteFunctionInst(*F);
      deleteFunction(F);
      F->dropDroppableUses();
      F->eraseFromParent();
    }
    else
    {
      if (F->doesNotRecurse())
      {
        workList.erase(workList.begin());
        workList.push_back(F);
      }
      else
      {
        workList.erase(workList.begin());
        workList.push_back(F);
        deleteFunction(F);
      }
    }
    if (workList.size() == beforeSize)
    {
      count++;
    }
    else
      count = 0;
    if (count > 1000)
    {
      errs() << "무한루프\n";
      break;
    }
    beforeSize = workList.size();
  }
  for (Function *F : workList)
  {
    errs() << "안지워지는 함수 : " << F->getName() << "\n";
    traceUses(F);
  }
  errs() << "Deleting process finished!\n";

  eraseRemoveInstruction();
  verifyModule(M);
  // verifyGlobalValue(M);
  errs() << "VerifyModule ! \n";
  return true;
}

void MPAvailable::analyzeGEPforFunction(Function &F)
{
  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E;)
  {
    inst_iterator vI = I;
    I++;
  }
}
void MPAvailable::allocation(Module &M)
{
  for (Function &F : M)
  {
    allocOnFunction(F);
  }
}

void MPAvailable::allocOnFunction(Function &F)
{
  // SRA = &getAnalysis<SymbolicRangeAnalysis>(F);
  // ScalarEvolution *SE = &getAnalysis<ScalarEvolutionWrapperPass>(F).getSE();
  for (Instruction &I : instructions(F))
  {
    if (isAllocation(&I))
      allocEpsilon(I, SE);

    if (isa<CallInst>(I) || isa<InvokeInst>(I))
    {

      Function *F = dyn_cast<CallBase>(&I)->getCalledFunction();
      if (F && F->isDeclaration())
        continue;
    }
  }
}

void MPAvailable::allocEpsilon(Instruction &I, ScalarEvolution *SE)
{
  if (isa<BitCastInst>(I.getNextNode()))
  {
    IRBuilder<> irb(getInsertPointAfter(I.getNextNode()));
    l4Alloc(I, SE, irb);
  }
  else
  {
    IRBuilder<> irb(getInsertPointAfter(&I));
    l4Alloc(I, SE, irb);
  }
}

void MPAvailable::l4Alloc(Instruction &I, ScalarEvolution *SE,
                          IRBuilder<> &irb) {}

Constant *MPAvailable::getNullPtr(PointerType *Ty)
{
  IntegerType *IntTy = IntegerType::get(Ty->getContext(), 64);
  ConstantInt *IntVal = ConstantInt::get(IntTy, BOUND_MASK_HIGH);
  return ConstantExpr::getIntToPtr(IntVal, Ty);
}

Value *MPAvailable::createOffset(Value *index, Type *type, IRBuilder<> &irb)
{
  uint64_t typeSize = DL->getTypeAllocSize(type->getPointerElementType());
  ConstantInt *typeSizeToValue =
      ConstantInt::get(IntegerType::get(irb.getContext(), 64), typeSize);
  Value *offset = irb.CreateMul(index, typeSizeToValue, "offset");
  return offset;
}
Value *MPAvailable::emitGEPOffset2(IRBuilder<> &irb, const DataLayout &DL,
                                   User *GEP,
                                   std::map<Value *, Value *> &valToVal)
{
  GEPOperator *GEPOp = cast<GEPOperator>(GEP);
  Type *IntIdxTy = DL.getIndexType(GEP->getType());
  Value *Result = nullptr;

  // If the GEP is inbounds, we know that none of the addressing operations will
  // overflow in a signed sense.
  bool isInBounds = GEPOp->isInBounds();

  // Build a mask for high order bits.

  gep_type_iterator GTI = gep_type_begin(GEP);
  for (User::op_iterator i = GEP->op_begin() + 1, e = GEP->op_end(); i != e;
       ++i, ++GTI)
  {
    Value *Op;
    Value *Val = *i;
    if (valToVal.count(Val) > 0)
      Op = valToVal[Val];
    else
    {
      // assert(isa<Constant>(Val) && "Val must be constant!");
      Op = Val;
    }
    uint64_t Size = DL.getTypeAllocSize(GTI.getIndexedType());
    Value *Offset;
    if (Constant *OpC = dyn_cast<Constant>(Op))
    {
      if (OpC->isZeroValue())
        continue;

      // Handle a struct index, which adds its field offset to the pointer.
      if (StructType *STy = GTI.getStructTypeOrNull())
      {
        if (strucTyToStructTy.count(STy) > 0)
          STy = strucTyToStructTy[STy];
        uint64_t OpValue = OpC->getUniqueInteger().getZExtValue();
        Size = DL.getStructLayout(STy)->getElementOffset(OpValue);
        if (!Size)
          continue;

        Offset = ConstantInt::get(IntIdxTy, Size);
      }
      else
      {
        // Splat the constant if needed.
        if (IntIdxTy->isVectorTy() && !OpC->getType()->isVectorTy())
          OpC = ConstantVector::getSplat(
              cast<VectorType>(IntIdxTy)->getElementCount(), OpC);

        Constant *Scale = ConstantInt::get(IntIdxTy, Size);
        Constant *OC =
            ConstantExpr::getIntegerCast(OpC, IntIdxTy, true /*SExt*/);
        Offset =
            ConstantExpr::getMul(OC, Scale, false /*NUW*/, isInBounds /*NSW*/);
      }
    }
    else
    {
      // Splat the index if needed.
      if (IntIdxTy->isVectorTy() && !Op->getType()->isVectorTy())
        Op = irb.CreateVectorSplat(
            cast<FixedVectorType>(IntIdxTy)->getNumElements(), Op);

      // Convert to correct type.
      if (Op->getType() != IntIdxTy)
        Op = irb.CreateIntCast(Op, IntIdxTy, true, Op->getName().str() + ".c");
      if (Size != 1)
      {
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
Value *MPAvailable::emitGEPOffset(IRBuilder<> &irb, const DataLayout &DL,
                                  User *GEP,
                                  std::map<Value *, Value *> &valToVal)
{
  GEPOperator *GEPOp = cast<GEPOperator>(GEP);
  Type *IntIdxTy = DL.getIndexType(GEP->getType());
  Value *Result = nullptr;

  // If the GEP is inbounds, we know that none of the addressing operations will
  // overflow in a signed sense.
  bool isInBounds = GEPOp->isInBounds();

  // Build a mask for high order bits.

  gep_type_iterator GTI = gep_type_begin(GEP);
  for (User::op_iterator i = GEP->op_begin() + 1, e = GEP->op_end(); i != e;
       ++i, ++GTI)
  {
    Value *Op;
    Value *Val = *i;
    if (valToVal.count(Val) > 0)
      Op = valToVal[Val];
    else
    {
      // assert(isa<Constant>(Val) && "Val must be constant!");
      Op = Val;
    }
    uint64_t Size = DL.getTypeAllocSize(GTI.getIndexedType());
    Value *Offset;
    if (Constant *OpC = dyn_cast<Constant>(Op))
    {
      if (OpC->isZeroValue())
        continue;

      // Handle a struct index, which adds its field offset to the pointer.
      if (StructType *STy = GTI.getStructTypeOrNull())
      {
        if (strucTyToStructTy.count(STy) > 0)
          STy = strucTyToStructTy[STy];
        uint64_t OpValue = OpC->getUniqueInteger().getZExtValue();
        Size = DL.getStructLayout(STy)->getElementOffset(OpValue);
        if (!Size)
          continue;

        Offset = ConstantInt::get(IntIdxTy, Size);
      }
      else
      {
        // Splat the constant if needed.
        if (IntIdxTy->isVectorTy() && !OpC->getType()->isVectorTy())
          OpC = ConstantVector::getSplat(
              cast<VectorType>(IntIdxTy)->getElementCount(), OpC);

        Constant *Scale = ConstantInt::get(IntIdxTy, Size);
        Constant *OC =
            ConstantExpr::getIntegerCast(OpC, IntIdxTy, true /*SExt*/);
        Offset =
            ConstantExpr::getMul(OC, Scale, false /*NUW*/, isInBounds /*NSW*/);
      }
    }
    else
    {
      // Splat the index if needed.
      if (IntIdxTy->isVectorTy() && !Op->getType()->isVectorTy())
        Op = irb.CreateVectorSplat(
            cast<FixedVectorType>(IntIdxTy)->getNumElements(), Op);

      // Convert to correct type.
      if (Op->getType() != IntIdxTy)
        Op = irb.CreateIntCast(Op, IntIdxTy, true, Op->getName().str() + ".c");
      if (Size != 1)
      {
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

void MPAvailable::handleGEP(GetElementPtrInst *gep)
{
  IRBuilder<> irb(getInsertPointAfter(gep));

  Value *xmm_pointer;
  Value *xmm_offset;
  GetElementPtrInst *PreemptedGep = nullptr;

  if (!gep)
    return;

  if (instructionToL4.find(dyn_cast<Instruction>(gep)) == instructionToL4.end())
    return;

  // if (gep->getPointerOperand()->getType()->getContainedType(0) !=
  // XMM_POINTER) return ; XMM 포인터는 기존의 포인터 변수 대신에 내가 만든
  // 구조체로 할당되기 때문에 gep 이전의 load도 다시 해야 됨

  bool isPositive = gepToPositive[gep];

  Value *base =
      gep->getPointerOperand()
          ->stripPointerCasts(); // base는 load 인스트럭션, 그리고 int128

  if (!isXMMTy(base->getType()))
    return;
  LoadInst *origLoad = dyn_cast<LoadInst>(base);
  Type *type = valueToType[base];
  // willBeRemoveSet.insert(origLoad);

  Value *tag;
  uint64_t constOffset;

  std::string Prefix = std::string(base->getName()) + "." + ".array.";
  // cast<Instruction>(irb.CreatePtrToInt(ptrToXMM[base], PtrIntTy, Prefix +
  // "int"));

  // const 일경우 -1. 양수, 2. 음수
  // const 아닐 경우 - 1. 양수, 음수

  // 속도를 위해선 메모리 load나 레지스터 거쳐가는 것을 최대한 줄일것

  // 오프셋 만드는 건 보류
  // 이거를 내가 직접 만들어보자...
  Value *Offset = EmitGEPOffset(&irb, *DL, gep);

  Value *replacePointer = nullptr;
  Value *emptyVec = Constant::getNullValue(XMM);

  // 어차피 vector 계산이니까
  // 양수, 음수 계산 따로 할 필요가 없음
  // 그럼 constoffset이냐 아니냐로만 구분하고

  // IRBuilder<> irbOffset(getInsertPointAfter(dyn_cast<Instruction>(Offset)));
  Value *element1 = irb.CreateInsertElement(emptyVec, Offset, (uint64_t)0);
  Value *element2 = irb.CreateInsertElement(element1, Offset, 1);
  replacePointer =
      irb.CreateAdd(base, element2, gep->getName() + ".TYPEPTR.sub");

  // irb.CreateInsertElement(emptyVec, , 0);
  // 일단 L4포인터로 생성이 안되고 있음
  // 이것먼저 되게 고쳐야함

  // tag를 만들고 나서 보수하는거니까 tag하고 나서 확인하고 해도 되지

  // 이거를 고쳐야 함
  //  continueList.insert(dyn_cast<Instruction>(P));

  // replacePointer is v2i64
  replaceAll(gep, replacePointer);
  gep->eraseFromParent();
}

void MPAvailable::handlePtrToInt(PtrToIntInst *pti)
{
  Value *op = pti->getPointerOperand();
  if (isXMMTy(op->getType()))
  {
    replaceAll(pti, op);
    pti->eraseFromParent();
  }
}

void MPAvailable::handleIntToPtr(IntToPtrInst *itp)
{
  Value *op = itp->getOperand(0);

  if (isXMMTy(op->getType()))
  {
    replaceAll(itp, op);
    itp->eraseFromParent();
  }
}

void MPAvailable::handleIcmp(ICmpInst *iCmpI)
{
  // null 인지 아닌지 확인해야해서 복구해야 됨
  // 즉 load나 스토어처럼 동작
  IRBuilder<> irb(iCmpI);
  Value *xmmPointer;
  Value *iCmpValue;
  if (isXMMTy(iCmpI->getOperand(0)->getType()))
  {
    xmmPointer = iCmpI->getOperand(0);
    iCmpValue = iCmpI->getOperand(1);
    Value *unWrapValue = ununTag(xmmPointer, iCmpValue->getType(), irb);
    iCmpI->setOperand(0, unWrapValue);
  }
  else if (isXMMTy(iCmpI->getOperand(1)->getType()))
  {
    xmmPointer = iCmpI->getOperand(1);
    iCmpValue = iCmpI->getOperand(0);
    Value *unWrapValue = ununTag(xmmPointer, iCmpValue->getType(), irb);
    iCmpI->setOperand(1, unWrapValue);
  }
  else
    return;
}
void MPAvailable::handleSubOrAdd(Instruction *i)
{
  IRBuilder<> irb(i);
  Value *replacer;
  if (isXMMTy(i->getOperand(0)->getType()))
  {
    Value *op1 = i->getOperand(1);
    Value *nullVector = Constant::getNullValue(XMM);
    Value *vec0 = irb.CreateInsertElement(nullVector, op1, (uint64_t)0);
    Value *vec1 = irb.CreateInsertElement(vec0, op1, 1);

    if (i->getOpcode() == Instruction::Add)
      replacer = irb.CreateAdd(i->getOperand(0), vec1);
    else
      replacer = irb.CreateSub(i->getOperand(0), vec1);
  }
  else if (isXMMTy(i->getOperand(1)->getType()))
  {
    Value *op0 = i->getOperand(0);
    Value *nullVector = Constant::getNullValue(XMM);
    Value *vec0 = irb.CreateInsertElement(nullVector, op0, (uint64_t)0);
    Value *vec1 = irb.CreateInsertElement(vec0, op0, 1);

    if (i->getOpcode() == Instruction::Add)
      replacer = irb.CreateAdd(i->getOperand(1), vec1);
    else
      replacer = irb.CreateSub(i->getOperand(1), vec1);
  }
  replaceAll(i, replacer);
  i->eraseFromParent();
}

bool MPAvailable::hasNegativeOffset(GetElementPtrInst *gep)
{
  // 먼저 gep에 대해서 분석을 해놓자

  APInt ConstOffset(64, 0);
  if (gep->accumulateConstantOffset(*DL, ConstOffset))
    return ConstOffset.isNegative();

  // For synamid offsets, look for the pattern "gep %base, (sub 0, %idx)"
  // XXX this is best-effort and may not catch all cases
  for (int i = 1, l = gep->getNumOperands(); i < l; i++)
  {
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

void MPAvailable::handleStore(StoreInst *si)
{
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

  Value *addr = si->getOperand(1);

  IRBuilder<> irb(getInsertPointAfter(si));

  if (isa<AllocaInst>(addr))
  {
    IRBuilder<> irbefore(getInsertPointBefore(si));
    if (isXMMTy(dyn_cast<AllocaInst>(addr)->getAllocatedType()))
    {
      if (isXMMTy(si->getValueOperand()->getType()))
        irb.CreateStore(si->getValueOperand(), si->getPointerOperand());
      else
      {
        // 이건 일종의 에러 핸들링 케이스..? 이런 경우가 많으면 안좋음
        // 카운트 체크 하게 바꿀 것
        VALUE_NOT_L4++;
        Value *nullVector = Constant::getNullValue(XMM);
        Value *valueVector;
        if (si->getValueOperand()->getType()->isIntegerTy())
        {
          if (!si->getValueOperand()->getType()->isIntegerTy(64))
          {
            Value *bitCast = irb.CreateBitCast(
                si->getValueOperand(), Type::getInt64Ty(si->getContext()));
            valueVector =
                irb.CreateInsertValue(nullVector, si->getValueOperand(), 1);
          }
          else
            valueVector =
                irb.CreateInsertElement(nullVector, si->getValueOperand(), 1);
        }
        else if (si->getValueOperand()->getType()->isPointerTy())
        {
          Value *ptrToInt = irb.CreatePtrToInt(
              si->getValueOperand(), Type::getInt64Ty(si->getContext()));
          Value *bitCast =
              irb.CreateBitCast(ptrToInt, Type::getInt64Ty(si->getContext()));
          typePrint(nullVector->getType(), "nullvector");
          typePrint(bitCast->getType(), "bitCast");
          valueVector =
              irb.CreateInsertElement(nullVector, bitCast, (uint64_t)1);
        }
        irb.CreateStore(valueVector, si->getPointerOperand());
      }
      // 여기에 타입이 퍼져나가는 것을 놓자

      si->eraseFromParent();
    }
  }
  else if (isXMMTy(addr->getType()))
  {
    Type *valueType = si->getValueOperand()->getType();
    Type *toPointer = valueType->getPointerTo();
    Value *clearTagPointer = ununTag(addr, toPointer, irb, "store");
    Value *replaceInst = irb.CreateStore(si->getOperand(0), clearTagPointer);
    si->eraseFromParent();
    // instPrint(dyn_cast<Instruction>(replaceInst), "i128llvm");
    // continueList.insert(dyn_cast<Instruction>(replaceInst));
  }
  return;
}

void MPAvailable::handleLoad(LoadInst *li)
{
  //  %0 = load i8*, i8** %ptr, align 8

  // 오퍼랜드가 GEP인지 아니면 AllocaInst 인지 확인해야함
  //  GEP->LOAD
  //  AllocaInst->LOAD
  //  LOAD->LOAD

  // i128 -> 18*
  // v2i64의 LOAD로 바꾸기

  // 먼저 포인터로 타입변환
  //  load
  Type *origType = li->getType();
  Value *liOp = li->getPointerOperand();

  IRBuilder<> irb(getInsertPointAfter(li));

  if (isa<AllocaInst>(liOp))
  {
    AllocaInst *ai = dyn_cast<AllocaInst>(liOp);
    if (!isXMMTy(ai->getAllocatedType()))
      return;
    // type 비교 equal은 없는거 같음 없으면 내가 구현 ㅇㅋ?
    // array[2] :i64 를 i128로 load 하기

    // 새로운 load 생성

    LoadInst *newLoad =
        irb.CreateLoad(XMM, liOp, liOp->getName() + ".TYPEPTRLOAD");
    continueList.insert(cast<Instruction>(newLoad));
    xmmLoadSet.insert(dyn_cast<Value>(newLoad));
    replaceAll(li, newLoad);
    valueToType[newLoad] = xmmToType[ai];
    li->eraseFromParent();
  }
  else if (isXMMTy(liOp->getType()))
  {
    // 태그 클리어 및 로드하는 인스트럭션으로 바꿔주기
    // 타입 확인도 할것
    Type *type = valueToType[liOp];
    Value *clearTagPointer =
        ununTag(liOp, origType->getPointerTo(), irb, liOp->getName().str());
    Value *replaceInst =
        irb.CreateLoad(clearTagPointer, liOp->getName() + "clear.bit");
    continueList.insert(dyn_cast<Instruction>(replaceInst));
    li->replaceAllUsesWith(replaceInst);
    li->eraseFromParent();
  }
}

bool MPAvailable::isInnerTagPossible(Value *size)
{
  if (ConstantInt *intSize = dyn_cast<ConstantInt>(size))
  {
    int realSize = intSize->getSExtValue();
    if (realSize <= 128)
      return true;
    else
      return false;
  }
  else
  {
    // SRA->
    const SCEV *sc = SE->getSCEV(size);
    if (sc->isAllOnesValue())
    {
      ConstantRange cr = SE->getUnsignedRange(sc);
      if (cr.isEmptySet())
        return false;
      APInt ai = cr.getUnsignedMax();
      int64_t intSize = ai.getSExtValue();
      if (intSize > 128)
        return false; // if(>128) return false;
      else
        return true;
    }
    else
      return false;
  }
  return false;
}

void MPAvailable::initFunction(Module &M)
{
  Type *PtrIntTy = getPtrIntTy(M.getContext());
  AddWithOverflowFunc =
      Intrinsic::getDeclaration(&M, Intrinsic::uadd_with_overflow, PtrIntTy);
}

void MPAvailable::eraseRemoveInstruction()
{
  for (Instruction *inst : willBeRemoveSet)
  {
    instPrint(inst, "erase");
    inst->eraseFromParent();
  }
}

Value *MPAvailable::clearTag_2(Value *xmmPtr, IRBuilder<> &irb,
                               std::string prefix)
{
  // xmmPtr 은 XMMP 구조체
  // 먼저, tag 갖고 오기 tag 가공해야됨 그 이유는 상위 17bit으로 몰아주기 위해서
  // 그 다음 메모리 주소 bitcast 하기
  // and 연산해서 바꿔주기

  // Load를 두개를 만들자
  // 하나는 128로 load 하는 것
  // 하나는 각각 64bit으로 load 하는 것
  Value *xmmPtr_ = cast<LoadInst>(xmmPtr)->getOperand(0);
  Value *indexListTag[2] = {
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       0),
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       0)};
  Value *XmmTag =
      irb.CreateInBoundsGEP(xmmPtr, indexListTag, xmmPtr->getName() + ".tag");

  Value *indexListOffset[2] = {
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       0),
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       1)};
  Value *xmmOffset =
      irb.CreateInBoundsGEP(xmmPtr, indexListOffset, prefix + ".offset");

  Value *XmmTagLoad = irb.CreateLoad(XmmTag);
  Value *XmmOffsetLoad = irb.CreateLoad(xmmOffset);

  Value *xmmTagAnd = irb.CreateAnd(
      XmmTagLoad, 0x8000000080000000,
      prefix + ".tag.and"); // 여기서 이미 태그를 제외한 메타데이터 클리어가 됨
  Value *xmmTagOverShl = irb.CreateShl(xmmTagAnd, 31, prefix + ".tag.over.shl");
  Value *xmmTagAssemble =
      irb.CreateOr(xmmTagAnd, xmmTagOverShl, prefix + "tag.assemble");
  Value *xmmTagResult =
      irb.CreateAnd(xmmTagAssemble, 0xC000000000000000, prefix + ".result");

  Value *clearPointer =
      irb.CreateOr(xmmTagResult, XmmOffsetLoad, prefix + ".clear");
  Value *result =
      irb.CreateBitCast(clearPointer, xmmToType[dyn_cast<AllocaInst>(xmmPtr)],
                        prefix + ".unwrap");

  return result;
}

Value *MPAvailable::unTag(Value *xmmPtr, IRBuilder<> &irb, std::string prefix)
{
  Value *xmmPtr_ = cast<LoadInst>(xmmPtr)->getOperand(0);
  Value *indexListTag[2] = {
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       0),
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       0)};
  Value *XmmTag =
      irb.CreateInBoundsGEP(xmmPtr, indexListTag, xmmPtr->getName() + ".tag");

  Value *indexListOffset[2] = {
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       0),
      ConstantInt::get(cast<PointerType>(xmmPtr->getType())->getElementType(),
                       1)};
  Value *xmmOffset =
      irb.CreateInBoundsGEP(xmmPtr, indexListOffset, prefix + ".offset");

  Value *XmmTagLoad = irb.CreateLoad(XmmTag);
  Value *XmmOffsetLoad = irb.CreateLoad(xmmOffset);

  Value *xmmTagAnd = irb.CreateAnd(
      XmmTagLoad, 0x8000000080000000,
      prefix + ".tag.and"); // 여기서 이미 태그를 제외한 메타데이터 클리어가 됨
  Value *xmmTagOverShl = irb.CreateShl(xmmTagAnd, 31, prefix + ".tag.over.shl");
  Value *xmmTagAssemble =
      irb.CreateOr(xmmTagAnd, xmmTagOverShl, prefix + "tag.assemble");
  Value *xmmTagResult =
      irb.CreateAnd(xmmTagAssemble, 0xC000000000000000, prefix + ".result");

  Value *clearPointer =
      irb.CreateOr(xmmTagResult, XmmOffsetLoad, prefix + ".clear");
  Value *result =
      irb.CreateIntToPtr(clearPointer, xmmToType[dyn_cast<AllocaInst>(xmmPtr)],
                         prefix + ".unwrap");

  return result;
}

Value *MPAvailable::ununTag(Value *xmmPtr, Type *origType, IRBuilder<> &irb,
                            std::string prefix)
{
  // i128 -> i64 -> i64* -> T* (T is original Type)
  // Trunc instruction 이용
  // oritType must be Pointer
  assert(isXMMTy(xmmPtr->getType()) && "origType must be XMMTy.");
  APInt oneAPInt(64, 1);
  ConstantInt::get(irb.getInt64Ty(), 1);
  Constant *one = ConstantInt::get(irb.getInt64Ty(), 1);

  Value *lowerSignal = irb.CreateShl(one, 63);
  Value *upperSignal = irb.CreateShl(one, 31);

  Value *signal = irb.CreateOr(lowerSignal, upperSignal);

  Value *tag =
      irb.CreateExtractElement(xmmPtr, (uint64_t)0, prefix + ".tag.extract");

  Value *pointer = irb.CreateExtractElement(xmmPtr, 1, prefix + ".ptr");

  Value *removeTag = irb.CreateAnd(signal, tag);
  Constant *cons = dyn_cast<Constant>(removeTag);

  Value *lower = irb.CreateAnd(removeTag, lowerSignal);
  Value *upper = irb.CreateShl(removeTag, 32);
  Value *resultTag = irb.CreateOr(lower, upper);

  // 상위 태그만 남겨두고 나머지는 0으로 만들기
  //  result_ptr = ptr || tag    ----> 실제 주소만 남고 상위 시그널 비트가 1일
  //  경우에만 세팅이 됨
  Value *resultPtr = irb.CreateOr(resultTag, pointer, prefix + ".ptr.result");

  Value *ptr = irb.CreateIntToPtr(
      resultPtr, Type::getInt8PtrTy(irb.getContext()), prefix + "unun_ptr");
  Value *res;
  if (origType->isPointerTy())
  {
    PointerType *pointerType = dyn_cast<PointerType>(origType);

    if (pointerType->getPointerElementType()->isStructTy())
    {
      Type *elementType = pointerType->getPointerElementType();
      StructType *st = dyn_cast<StructType>(elementType);
      if (strucTyToStructTy.count(st) > 0)
      {
        StructType *newSt = strucTyToStructTy[st];
        res = irb.CreateBitCast(ptr, newSt->getPointerTo(),
                                prefix + "new.strcut.unwrap");
      }
      else
        res = irb.CreateBitCast(ptr, origType, prefix + "old.struct.unwrap");
    }
    else if (isFunctionPtrTy(origType))
    {
      // errs() << "HERE?\n";
      FunctionType *ft =
          dyn_cast<FunctionType>(pointerType->getPointerElementType());
      FunctionType *newFt = createFunctionType(ft);
      res = irb.CreateBitCast(ptr, newFt->getPointerTo(), prefix + ".fpunwrap");
      // res = irb.CreateBitCast(ptr, origType, prefix + ".fpunwrap");
    }
    else if (isFunctionPtrPtrTy(origType))
    {
      PointerType *pt =
          dyn_cast<PointerType>(pointerType->getPointerElementType());
      FunctionType *ft = dyn_cast<FunctionType>(pt->getPointerElementType());
      FunctionType *newFt = createFunctionType(ft);
      res = irb.CreateBitCast(ptr, newFt->getPointerTo()->getPointerTo(),
                              prefix + ".fpunwrap");
      // res = irb.CreateBitCast(ptr, origType, prefix + ".fpunwrap");
    }
    // else if (pointerType->getElementType()->isArrayTy())
    // {
    //   ArrayType *origArrayTy = dyn_cast<ArrayType>(pointerType->getElementType());
    //   ArrayType *newArrayTy;
    //   if (origArrayTy->getArrayElementType()->isPointerTy())
    //   {
    //     newArrayTy = ArrayType::get(XMM, origArrayTy->getNumElements());
    //   }
    //   else if (origArrayTy->getArrayElementType()->isStructTy())
    //   {
    //     StructType *st = strucTyToStructTy[dyn_cast<StructType>(origArrayTy->getArrayElementType())];
    //     newArrayTy = ArrayType::get(st, origArrayTy->getNumElements());
    //   }
    //   else
    //     newArrayTy = origArrayTy;
    //   res = irb.CreateBitCast(ptr, newArrayTy, prefix + ".unwrap_");
    // }
    else
    {
      //
      std::string typeName;
      llvm::raw_string_ostream rso(typeName);

      origType->print(rso);
      res = irb.CreateBitCast(ptr, origType, prefix + ".unwrap_" + typeName);
    }
  }
  else
  {
    res = irb.CreateBitCast(ptr, origType, prefix + ".unwrap");
  }
  return res;
}
Value *MPAvailable::createL4Ptr(Value *ptr, IRBuilder<> &irb)
{
  assert(ptr->getType()->isPointerTy() && "Ptr must be PointerTy");
  Constant *nullValue = Constant::getNullValue(XMM);

  Value *vec1 = irb.CreateInsertElement(
      nullValue, ConstantInt::get(irb.getInt64Ty(), 0), (uint64_t)0);
  Value *ptrToInt64 = irb.CreatePtrToInt(ptr, irb.getInt64Ty());
  Value *vec2 = irb.CreateInsertElement(vec1, ptrToInt64, 1);
  return vec2;
}

Value *MPAvailable::ununTag(Value *xmmPtr, Type *origType, IRBuilder<> &irb,
                            DenseSet<Instruction *> &conList,
                            std::string prefix)
{
  // i128 -> i64 -> i64* -> T* (T is original Type)
  // Trunc instruction 이용
  // oritType must be Pointer
  assert(isXMMTy(xmmPtr->getType()) && "origType must be XMMTy.");
  APInt oneAPInt(64, 1);
  ConstantInt::get(irb.getInt64Ty(), 1);
  Constant *one = ConstantInt::get(irb.getInt64Ty(), 1);

  Value *lowerSignal = irb.CreateShl(one, 63);
  conList.insert(dyn_cast<Instruction>(lowerSignal));
  Value *upperSignal = irb.CreateShl(one, 31);
  conList.insert(dyn_cast<Instruction>(upperSignal));
  Value *signal = irb.CreateOr(lowerSignal, upperSignal);
  conList.insert(dyn_cast<Instruction>(signal));
  Value *tag =
      irb.CreateExtractElement(xmmPtr, (uint64_t)0, prefix + ".tag.extract");
  conList.insert(dyn_cast<Instruction>(tag));
  Value *pointer = irb.CreateExtractElement(xmmPtr, 1, prefix + ".ptr");
  conList.insert(dyn_cast<Instruction>(pointer));

  Value *removeTag = irb.CreateAnd(signal, tag);
  Constant *cons = dyn_cast<Constant>(removeTag);
  conList.insert(dyn_cast<Instruction>(removeTag));

  Value *lower = irb.CreateAnd(removeTag, lowerSignal);
  Value *upper = irb.CreateShl(removeTag, 32);
  Value *resultTag = irb.CreateOr(lower, upper);
  conList.insert(dyn_cast<Instruction>(lower));
  conList.insert(dyn_cast<Instruction>(upper));
  conList.insert(dyn_cast<Instruction>(resultTag));
  // 상위 태그만 남겨두고 나머지는 0으로 만들기
  //  result_ptr = ptr || tag    ----> 실제 주소만 남고 상위 시그널 비트가 1일
  //  경우에만 세팅이 됨
  Value *resultPtr = irb.CreateOr(resultTag, pointer, prefix + ".ptr.result");
  conList.insert(dyn_cast<Instruction>(resultPtr));
  Value *ptr = irb.CreateIntToPtr(
      resultPtr, Type::getInt8PtrTy(irb.getContext()), prefix + "realloc_ptr");
  conList.insert(dyn_cast<Instruction>(ptr));
  Value *res = irb.CreateBitCast(ptr, origType, prefix + ".unwrap");
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

void MPAvailable::replaceAll(Value *orig, Value *replacer)
{
  for (Value::user_iterator ui = orig->user_begin(); ui != orig->user_end();)
  {
    Value::user_iterator vui = ui;
    ui++;
    Instruction *inst = dyn_cast<Instruction>(*vui);
    for (int i = 0; i < inst->getNumOperands(); i++)
    {
      if (inst->getOperand(i) == orig)
      {
        inst->setOperand(i, replacer);
      }
    }
  }
}

void MPAvailable::verifyModule(Module &M)
{
  std::string filePath = M.getName().str() + ".ll";

  raw_ostream *out = &outs();
  std::error_code EC;
  out = new raw_fd_ostream(filePath, EC);
  *out << "Global Var :\n";
  for (GlobalVariable &GV : M.getGlobalList())
  {
    if (GV.getType()->isFunctionTy())
      continue;
    if (GV.isConstant())
      continue;
    if (!GV.hasInitializer())
      continue;
    GV.print(*out);
    *out << "\n";
  }
  *out << "Struct Type : \n";
  for (StructType *st : M.getIdentifiedStructTypes())
  {
    st->print(*out);
    *out << "\n";
  }
  for (Function &F : M)
  {
    if (F.isDeclaration())
      continue;
    *out << F.getName().str() << "\n";
    for (AttributeSet attrs : F.getAttributes())
    {
      *out << attrs.getAsString() << " ";
    }
    *out << "\n";
    F.print(*out);
    // for (Instruction& I : instructions(F)) {
    //   I.print(*out);
    //   *out << "\n";
    // }
  }

  // delete out;
}

void MPAvailable::preprocessGEP(GetElementPtrInst *gep)
{
  ConstantInt *ConstOffset = nullptr;
  APInt ConstOffsetVal(64, 0);
  if (gep->accumulateConstantOffset(*DL, ConstOffsetVal))
    ConstOffset = dyn_cast<ConstantInt>(
        GETCONSTANTINT(gep->getContext(), 64, ConstOffsetVal));

  gepToOffset[gep] = ConstOffset;
  gepToPositive[gep] = hasNegativeOffset(gep);
}

void MPAvailable::transFormation(Function *F) {}

void MPAvailable::preprocessModule(Module &M)
{
  for (Function &F : M)
  {
    for (Instruction &I : instructions(F))
    {
      switch (I.getOpcode())
      {
      case Instruction::GetElementPtr:
        preprocessGEP(dyn_cast<GetElementPtrInst>(&I));
        break;
      }
    }
  }
}
bool MPAvailable::isXMMTy(Type *type)
{
  // XMM Type 인지, XMMTYPE의 포인터는 FALSE
  if (type->isVectorTy())
  {
    VectorType *vt = dyn_cast<VectorType>(type);
    return vt->getElementType()->isIntegerTy(64);
  }
  return false;
}

bool MPAvailable::isXMMPtrTy(Type *type)
{
  // XMM Type 인지, XMMTYPE의 포인터는 FALSEf
  if (type->isPointerTy())
  {
    PointerType *pt = dyn_cast<PointerType>(type);
    if (isXMMTy(pt->getElementType()))
      return true;
  }
  return false;
}

Value *MPAvailable::createXmmTag(IRBuilder<> &irb, Value *size,
                                 std::string prefix = "")
{
  // 이 메소드는 태그만 만듬
  // 리턴후에 원래의 offet과 and 해야됨
  //  gep 전용
  //  size는 64bit
  Constant *nullValue = Constant::getNullValue(XMM);

  Value *tagVal;
  Value *UnderOffset = irb.CreateShl(size, 32, prefix + ".under");

  tagVal = irb.CreateOr(UnderOffset, size, prefix + ".tag");
  irb.CreateInsertElement(nullValue, tagVal, (uint64_t)0);

  Value *sizeAnd =
      irb.CreateAnd(size,
                    ConstantInt::get(IntegerType::get(irb.getContext(), 64),
                                     0xffffffffffffffff),
                    "size");

  Value *result = irb.CreateInsertElement(nullValue, sizeAnd, (uint64_t)1);
  return result;
}

void MPAvailable::handleCall(CallInst *CI)
{
  if (!CI)
    return;
  IRBuilder<> irb(CI);
  Function *calledFunc = CI->getCalledFunction();
  CallBase *cb = CI;

  if (calledFunc->getName() == "free")
  {
    handleFree(CI);
    return;
  }

  FunctionType *calledFuncType = calledFunc->getFunctionType();

  if (!calledFunc->isDeclaration())
  {
    if (transformFunctions.find(calledFunc) != transformFunctions.end())
    {
      errs() << "Create New Call! : " << calledFunc->getName() << "\n";
      typePrint(calledFunc->getType(), "Func Type");

      Value *ret = nullptr;
      std::vector<Value *> args;

      for (unsigned int i = 0; i < CI->arg_size(); i++)
      {
        args.push_back(CI->getArgOperand(i));
        ArrayRef<Value *> array = args;
        Type *fType = calledFuncType->getParamType(i);
        Type *aType = array[i]->getType();
        assert((i <= calledFuncType->getNumParams() || (fType == aType)) &&
               "Calling a function with a bad signature!");
      }

      if (!calledFuncType->getReturnType()->isVoidTy())
        ret = irb.CreateCall(calledFunc, args);
      else
      {
        CallInst *newCI = irb.CreateCall(calledFunc, args);
        typePrint(CI->getCalledOperand()->getType(), "CI Called Operand");
        typePrint(newCI->getCalledOperand()->getType(),
                  "What is Called Operand()?");
      }
      if (ret != nullptr)
      {
        CI->replaceAllUsesWith(ret);
      }
      CI->eraseFromParent();
    }
  }
  else if (calledFunc->isDeclaration())
  {
    for (unsigned int i = 0; i < CI->arg_size(); i++)
    {
      Type *argType;
      if (calledFuncType->isVarArg() && i >= calledFuncType->getNumParams())
      {
        argType =
            calledFuncType->getParamType(calledFuncType->getNumParams() - 1);
      }
      else
      {
        argType = calledFuncType->getParamType(i);
      }
      Value *arg = CI->getArgOperand(i);
      if (isXMMTy(arg->getType()))
      {
        Value *noPointer = ununTag(arg, argType, irb, arg->getName().str());
        CI->setArgOperand(i, noPointer);
      }
    }
  }
}
void MPAvailable::debugBCI(BitCastInst *bci)
{
  instPrint(bci, "bci print");
  for (User *user : bci->users())
  {
    Value *userV = dyn_cast<Value>(user);
    valuePrint(userV, "userV");
  }
}
void MPAvailable::handleFree(CallInst *CI)
{
  errs() << "Handle Free\n";
  Function *calledFunc = CI->getCalledFunction();
  IRBuilder<> irb(CI);

  Value *arg = CI->getArgOperand(0);
  valuePrint(arg, "Free");
  Value *unWrapValue;
  if (BitCastInst *bci = dyn_cast<BitCastInst>(arg))
  {
    Value *orig = bci->getOperand(0);
    if (isXMMTy(orig->getType()))
    {
      unWrapValue = ununTag(orig, Type::getInt8PtrTy(CI->getContext()), irb);
      CI->setArgOperand(0, unWrapValue);
      bci->eraseFromParent();
    }
  }
  else
  {
    if (!isXMMTy(arg->getType()))
      return;
    Value *unWrapValue =
        ununTag(arg, Type::getInt8PtrTy(CI->getContext()), irb);
    CI->setArgOperand(0, unWrapValue);
  }

  // irb.CreateStore(xmm_ai, setFlagV);
}

void MPAvailable::preAnalyzeGEP(Function *F)
{
  bool changed = true;

  while (changed)
  {
    changed = false;
    for (Instruction &I : instructions(F))
    {
      switch (I.getOpcode())
      {
      case Instruction::Alloca:
        if (I.getType()->getPointerElementType()->isPointerTy())
        {
          if (instructionToL4.find(&I) == instructionToL4.end())
          {
            changed = true;
            instructionToL4.insert(&I);
          }
        }
        break;
      case Instruction::Load:
      case Instruction::GetElementPtr:
        if (Instruction *opInst = dyn_cast<Instruction>(I.getOperand(0)))
        {
          if (instructionToL4.find(opInst) != instructionToL4.end() &&
              instructionToL4.find(&I) == instructionToL4.end())
          {
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

void MPAvailable::createWrappingFunction(Function &F)
{
  // if (F.getName().find("main") != std::string::npos) {
  //   usedFunctionPointer.insert(&F);
  //   return;
  // }
  // if (!checkShouldBeWrapped(F)) {
  //   return;
  // }
  // if(isPassFunction(&F)) return;
  // if (F.getName().find("_GLOBAL__") != std::string::npos)
  // {
  //   funcToFunc[&F] = &F;
  //   return;
  // }
  // if (F.getName().find("global") != std::string::npos)
  // {
  //   funcToFunc[&F] = &F;
  //   return;
  // }
  if (isUserAllocation(&F))
    return;
  if (isStringFunction(&F))
    return;

  bool isNeedTransform = true;
  // if (isUsedFunctionPointer(&F)) {
  //   // usedFunctionPointer.insert(&F);
  //   isNeedTransform = false;
  //   // return;
  // }
  // errs() << "Wrapping ... " << F.getName() << "\n";
  // if (isa<Constant>(&F)) return;
  bool mustWrapped = false;

  std::map<Value *, Value *> valToVal;
  std::map<StringRef, int> argToArg;
  std::map<BasicBlock *, BasicBlock *> basicToBasic;
  std::map<Value *, Type *> valToType;
  std::map<Value *, Value *> arrToPtr;
  Function *newFunc = funcToFunc[&F];
  int i = 0;
  // std::vector<Type*> plist;

  if (isNeedTransform)
  {
    for (Argument &arg : F.args())
    {
      Value *vArg = dyn_cast<Value>(&arg);
      if (!vArg->hasName())
        vArg->setName("temp");
      if (isFunctionPtrTy(arg.getType()))
      {
        argToArg[vArg->getName()] = i;
      }
      else if (arg.getType()->isPointerTy())
      {
        argToArg[vArg->getName()] = i;
      }
      else
      {
        argToArg.insert(std::pair<StringRef, int>(vArg->getName(), i));
      }

      AttributeList pal = F.getAttributes();
      AttributeSet attrs = pal.getParamAttributes(i);
      if (attrs.getAsString().find("byval") != std::string::npos)
      {
        valToVal[vArg] = newFunc->getArg(i);
      }
      if (attrs.getAsString().find("sret") != std::string::npos)
      {
        valToVal[vArg] = newFunc->getArg(i);
      }
      valToVal[vArg] = newFunc->getArg(i);
      i++;
    }
  }
  // } else {
  //   for (Argument& arg : F.args()) {
  //     Value* vArg = dyn_cast<Value>(&arg);
  //     argToArg[vArg->getName()] = i;
  //   }
  // }
  for (BasicBlock &BB : F.getBasicBlockList())
  {
    BasicBlock *clone =
        BasicBlock::Create(newFunc->getContext(), BB.getName(), newFunc);
    valToVal[&BB] = clone;
    basicToBasic[&BB] = clone;
  }
  for (detail::DenseMapPair<GlobalVariable *, GlobalVariable *> gPair : gToGV)
  {
    Value *key = gPair.first;
    Value *value = gPair.second;
    valToVal[key] = value;
  }
  for (detail::DenseMapPair<Value *, Value *> gArr : arrOfGlobalVal)
  {
    Value *key = gArr.first;
    Value *value = gArr.second;
    arrToPtr[key] = value;
  }
  for (detail::DenseMapPair<Function *, Function *> fPair : funcToFunc)
  {
    Value *key = fPair.first;
    Value *value = fPair.second;
    valToVal[key] = value;
  }
  for (BasicBlock &BB : F.getBasicBlockList())
  {
    cloneBB(newFunc, &BB, argToArg, valToVal, arrToPtr);
  }

  // replaceFunction(newFunc, &F);
  // F.eraseFromParent();
}

void MPAvailable::replaceFunction(Function *newFunc, Function *oldFunc)
{
  errs() << "Replace Function\n";
  for (User *user : oldFunc->users())
  {
    if (CallInst *CI = dyn_cast<CallInst>(user))
    {
      AttributeList PAL = CI->getAttributes();
      AttributeList newAttr;
      for (unsigned int ArgNo = 0; ArgNo < CI->getNumArgOperands(); ArgNo++)
      {
        errs() << "What is ATTR?:  "
               << PAL.getAttributes(ArgNo).getNumAttributes() << "\n";
        newAttr = PAL.removeAttributes(CI->getContext(), ArgNo);
      }
      IRBuilder<> irb(CI);
      std::vector<Value *> args;
      for (int i = 0; i < CI->getNumArgOperands(); i++)
      {
        Value *arg = CI->getArgOperand(i);
        if (isFunctionPtrTy(arg->getType()))
          args.push_back(arg);
        else if (arg->getType()->isPointerTy())
        {
          Value *ptrToInt =
              irb.CreatePtrToInt(arg, Type::getInt64Ty(CI->getContext()));
          args.push_back(ptrToInt);
          Value *nullValue =
              Constant::getNullValue(Type::getInt64Ty(CI->getContext()));
          args.push_back(nullValue);
        }
        else
          args.push_back(arg);
      }
      typePrint(newFunc->getFunctionType(), "newFuncType");
      Value *returnValue = irb.CreateCall(newFunc, args, CI->getName());
      for (User *ciUser : CI->users())
      {
        if (Instruction *inst = dyn_cast<Instruction>(ciUser))
        {
          for (int i = 0; i < inst->getNumOperands(); i++)
          {
            if (inst->getOperand(i) == CI)
            {
              inst->setOperand(i, returnValue);
            }
          }
        }
      }
      const AttrBuilder attrBuilder;
      for (int i = 0; i < args.size(); i++)
      {
        newAttr =
            newAttr.addAttributes(returnValue->getContext(), i, attrBuilder);
      }
      CallBase *CB = dyn_cast<CallBase>(returnValue);
      CB->setAttributes(PAL);
      CI->eraseFromParent();
      AttributeList Attrs = CI->getAttributes();

      // CI->setAttributes(Attrs);
    }
    else
    {
    }
  }
}
BasicBlock *MPAvailable::cloneBB(Function *cloneFunc, BasicBlock *orig,
                                 std::map<StringRef, int> &argToArg,
                                 std::map<Value *, Value *> &valToVal,
                                 std::map<Value *, Value *> &arrToPtr)
{
  BasicBlock *clone = dyn_cast<BasicBlock>(valToVal[orig]);

  IRBuilder<> irb(clone);
  Constant *falseCons = ConstantInt::getFalse(Type::getInt1Ty(irb.getContext()));

  for (Instruction &I : orig->getInstList())
  {
    // clone->getInstList().push_back(newInst);
    // Reset the insert point of IRB
    if (cloneFunc->getName() == "Wrapping_hashtable_getlock")
      instPrint(&I, cloneFunc->getName().str());
    switch (I.getOpcode())
    {
    case Instruction::Alloca:
    {
      // PASS
      AllocaInst *allocaInst = dyn_cast<AllocaInst>(&I);
      if (allocaInst->getName() == "argv.addr" || isArgsFunction(cloneFunc))
      {
        Instruction *newInst = I.clone();
        newInst->setName(I.getName());
        valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
        clone->getInstList().push_back(newInst);
        break;
      }
      if (allocaInst->getName() == "saved_stack")
      {
        Instruction *newInst = I.clone();
        newInst->setName(I.getName());
        valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
        clone->getInstList().push_back(newInst);
        break;
      }
      if (isFunctionPtrTy(allocaInst->getAllocatedType()))
      {
        FunctionType *ft = dyn_cast<FunctionType>(
            dyn_cast<PointerType>(allocaInst->getAllocatedType())
                ->getPointerElementType());
        FunctionType *newFt = createFunctionType(ft);
        Value *newInst =
            irb.CreateAlloca(newFt->getPointerTo(), nullptr, I.getName());
        // Instruction* newInst = I.clone();
        newInst->setName(I.getName());
        valToVal[dyn_cast<Value>(&I)] = newInst;
      }
      else if (allocaInst->getAllocatedType()->isPointerTy())
      {
        if (allocaInst->isArrayAllocation())
        {
          Value *size = instrumentWithByteSize(irb, &I, valToVal);

          Value *newPointer =
              irb.CreateAlloca(XMM, nullptr, I.getName().str() + ".l4");
          Value *newArray = irb.CreateAlloca(allocaInst->getAllocatedType(),
                                             size, allocaInst->getName());
          Value *OvSz = createMask(irb, size, irb.getContext());
          Value *PtrInt = irb.CreatePtrToInt(newArray, irb.getInt64Ty());
          Value *emptyVec = Constant::getNullValue(XMM);

          Value *vec0 = irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
          Value *vec1 = irb.CreateInsertElement(vec0, PtrInt, 1);

          irb.CreateStore(vec1, newPointer);
          valToVal[dyn_cast<Value>(&I)] = newPointer;
          arrToPtr[dyn_cast<Value>(&I)] = newPointer;
        }
        else
        {
          Value *replace = irb.CreateAlloca(XMM, nullptr, I.getName());

          valToVal[dyn_cast<Value>(&I)] = replace;
        }
      }
      else if (allocaInst->getAllocatedType()->isArrayTy())
      {
        Value *newArray;
        ArrayType *AT = dyn_cast<ArrayType>(allocaInst->getAllocatedType());

        if (AT->getArrayElementType()->isPointerTy())
        {

          ArrayType *newArrayType =
              ArrayType::get(XMM, AT->getArrayNumElements());

          newArray =
              irb.CreateAlloca(newArrayType, nullptr, allocaInst->getName());
          if (constVariables.count(allocaInst) > 0)
          {
            newArray = irb.CreateAlloca(allocaInst->getAllocatedType(), nullptr,
                                        allocaInst->getName());
          }
          else
            newArray =
                irb.CreateAlloca(newArrayType, nullptr, allocaInst->getName());
        }
        else
          newArray = irb.CreateAlloca(allocaInst->getAllocatedType(), nullptr,
                                      allocaInst->getName());

        Value *newPointer =
            irb.CreateAlloca(XMM, nullptr, I.getName().str() + ".l4.arrayty");
        AllocaInst *newAI = dyn_cast<AllocaInst>(newArray);
        newAI->setAlignment(allocaInst->getAlign());

        Type *type = allocaInst->getAllocatedType();
        ArrayType *arrType = dyn_cast<ArrayType>(type);
        Value *arrTypeSize =
            irb.getInt64(DL->getTypeAllocSize(arrType->getArrayElementType()));
        Value *arrSize = irb.getInt64(arrType->getArrayNumElements());
        Value *allocSize = irb.CreateMul(arrTypeSize, arrSize);

        Value *OvSz = createMask(irb, allocSize, irb.getContext());
        Value *PtrInt = irb.CreatePtrToInt(newArray, irb.getInt64Ty());
        Value *emptyVec = Constant::getNullValue(XMM);

        Value *vec0 = irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
        Value *vec1 = irb.CreateInsertElement(vec0, PtrInt, 1);

        irb.CreateStore(vec1, newPointer);
        valToVal[dyn_cast<Value>(&I)] = newPointer;
        arrToPtr[dyn_cast<Value>(&I)] = newPointer;
      }
      else if (allocaInst->isArrayAllocation())
      {
        Value *size = instrumentWithByteSize(irb, &I, valToVal);

        Value *newPointer =
            irb.CreateAlloca(XMM, nullptr, I.getName().str() + ".l4");
        Value *newArray = irb.CreateAlloca(allocaInst->getAllocatedType(), size,
                                           allocaInst->getName());
        Value *OvSz = createMask(irb, size, irb.getContext());
        Value *PtrInt = irb.CreatePtrToInt(newArray, irb.getInt64Ty());
        Value *emptyVec = Constant::getNullValue(XMM);

        Value *vec0 = irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
        Value *vec1 = irb.CreateInsertElement(vec0, PtrInt, 1);

        irb.CreateStore(vec1, newPointer);
        valToVal[dyn_cast<Value>(&I)] = newPointer;
        arrToPtr[dyn_cast<Value>(&I)] = newPointer;
      }
      else if (allocaInst->getAllocatedType()->isStructTy())
      {
        StructType *st = dyn_cast<StructType>(allocaInst->getAllocatedType());
        if (strucTyToStructTy.count(st) > 0)
        {
          StructType *newSt = strucTyToStructTy[st];
          Value *newAlloc = irb.CreateAlloca(newSt, nullptr, I.getName());
          valToVal[dyn_cast<Value>(&I)] = newAlloc;
        }
        else
        {
          Instruction *newInst = I.clone();
          newInst->setName(I.getName());
          valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
          clone->getInstList().push_back(newInst);
        }
      }
      else
      {
        Instruction *newInst = I.clone();
        newInst->setName(I.getName());
        valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
        clone->getInstList().push_back(newInst);
      }

      break;
    }
    case Instruction::Store:
    {
      Value *v0 = I.getOperand(0); // value
      Value *v1 = valToVal.count(I.getOperand(1)) > 0
                      ? valToVal[I.getOperand(1)]
                      : I.getOperand(1); // pointer
      if (argToArg.count(v0->getName()))
      {
        // Argument를 저장하는 과정
        // Argument 저장 통과
        int index = argToArg[v0->getName()];

        if (v0->getType()->isPointerTy())
        {
          if (isFunctionPtrTy(v0->getType()))
          {
            Value *arg = cloneFunc->getArg(index);
            irb.CreateStore(arg, v1);
            break;
          }
          if (AllocaInst *newAI = dyn_cast<AllocaInst>(I.getOperand(1)))
          {
            if (cloneFunc->getName() != "main")
            {
              Value *tag = cloneFunc->getArg(index);

              Value *bitcast = irb.CreateBitCast(tag, XMM_POINTER);
              Value *loadArg = irb.CreateLoad(bitcast);
              irb.CreateStore(loadArg, v1);
            }
            else
            {
              Value *arg = cloneFunc->getArg(index);
              instPrint(&I, "orig: ");
              valuePrint(arg, "arg");
              valuePrint(v1, "v1");
              irb.CreateStore(arg, v1);
            }
            // Value* ptr = cloneFunc->getArg(index + 1);
            // Value* nullL4 = Constant::getNullValue(XMM);
            // Value* tagVec = irb.CreateInsertElement(nullL4, tag,
            // (uint64_t)0); Value* ptrToInt =
            //     irb.CreatePtrToInt(ptr,
            //     Type::getInt64Ty(ptr->getContext()));
            // Value* L4 = irb.CreateInsertElement(tagVec, ptrToInt, 1);

            // Instruction* inst = dyn_cast<Instruction>(v1);
            // irb.CreateStore(L4, v1);
          }
          else if (isXMMPtrTy(v1->getType()))
          {
            // Value* tag = cloneFunc->getArg(index);

            // Value* ptr = cloneFunc->getArg(index + 1);
            // Value* nullL4 = Constant::getNullValue(XMM);
            // Value* tagVec = irb.CreateInsertElement(nullL4, tag,
            // (uint64_t)0); Value* ptrToInt =
            //     irb.CreatePtrToInt(ptr,
            //     Type::getInt64Ty(ptr->getContext()));
            // Value* L4 = irb.CreateInsertElement(tagVec, ptrToInt, 1);

            // Instruction* inst = dyn_cast<Instruction>(v1);
            Value *tag = cloneFunc->getArg(index);
            Value *bitcast = irb.CreateBitCast(tag, XMM_POINTER);
            Value *loadArg = irb.CreateLoad(bitcast);
            irb.CreateStore(loadArg, v1);
          }
          else if (isXMMTy(v1->getType()))
          {
            Value *ptr = cloneFunc->getArg(index);
            Value *newV1 = ununTag(v1, I.getOperand(1)->getType(), irb);
            irb.CreateStore(ptr, newV1);
          }
          else
          {
            // v1 is pointer Ty;
            Value *ptr = cloneFunc->getArg(index);

            Value *intToPtr =
                irb.CreateIntToPtr(ptr, v1->getType()->getPointerElementType());
            irb.CreateStore(intToPtr, v1);
          }
        }
        else
        {
          Value *arg = cloneFunc->getArg(index);
          // valuePrintGenerate(arg, irb);
          // valuePrintGenerate(v1, irb, true);
          irb.CreateStore(arg, v1);
        }

        break;
      }

      Value *value = I.getOperand(0);
      Value *pointer = I.getOperand(1);
      if (valToVal.count(pointer) > 0)
      {
        Value *newPointer = valToVal[pointer];
        Value *newValue;

        if (valToVal.count(value) > 0)
          newValue = valToVal[value];
        else
          newValue = value; // value is Constant
        // if(!newPointer ) newPointer = pointer;

        if (value->getType()->isPointerTy() && !isFunctionPtrTy(value->getType()))
        {
          //
          // 1) double pointer 인 경우
          // value 가 포인터인 경우를 여기서 처리하게 바꾸자
          // 밑에 있는 코드를 위로 끌어오기
          // null 넣는 코드는 밑에 있음

          // 2) 구조체의 멤버가 포인터인 경우
          // 구조체에서 계산할 때 gep를 통해 하고 그것이 XMM 타입으로 남기 때문에 여기서
          // 이에 대한 처리를 해줘야 함
          // 여기서 함수 포인터인 경우에 대해서 처리 해주면 될듯
          // 아니면 아예 밖으로 빼거나
          // 지금 이것이 문제임
          // 구조체의 멤버가 포인터일 경우 어떻게 할것인가
          // 일단 주소 align 생각하면 이 문제는 주소를 태그 자리에 저장해서 발생하는 문제
          if (isXMMTy(newValue->getType()))
          {
            if (isXMMTy(newPointer->getType()))
            {

              Value *replacePointer =
                  ununTag(newPointer, XMM_POINTER, irb, "SAVE.L4.");
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
            }
            else if (isXMMPtrTy(newPointer->getType()))
            {
              // valuePrintGenerate(newPointer, irb);
              irb.CreateStore(newValue, newPointer);
            }
            else
            {
              // Pointer is not XMM TYPE
              // so value untag
              Value *replaceValue =
                  ununTag(newValue, value->getType(), irb, "POINTER.NOT.XMM");

              if (replaceValue->getType()->getPointerTo() !=
                  newPointer->getType())
              {
                newPointer = irb.CreateBitCast(
                    newPointer, replaceValue->getType()->getPointerTo(),
                    "????");
              }
              // valuePrintGenerate(newPointer, irb);
              irb.CreateStore(replaceValue, newPointer);
            }
          }
          else
          {
            // value 가 XMM Type 이 아님
            //
            if (isXMMTy(newPointer->getType()))
            {
              // 일단 문제가 gep 임
              Value *replacePointer;
              std::string type_str;
              llvm::raw_string_ostream rso(type_str);
              value->getType()->print(rso);
              type_str.append(".");
              pointer->getType()->print(rso);
              type_str.append(".??");

              if (isDoublePtr(pointer->getType()))
              {
                replacePointer = ununTag(
                    newPointer, XMM_POINTER, irb, type_str);
                newValue = createXmmValue(irb, newValue);
                // newValue를 XMM타입으로 만들어주기
              }
              else
              {
                if (Constant *cons = dyn_cast<Constant>(newValue))
                {
                  newValue = Constant::getNullValue(XMM);
                  type_str.append(".cons");
                  replacePointer = ununTag(newPointer, XMM_POINTER, irb, type_str);
                  // valuePrintGenerate(replacePointer, irb);
                }
                else
                  replacePointer = ununTag(
                      newPointer, newValue->getType()->getPointerTo(), irb, type_str);
                // valuePrintGenerate(replacePointer, irb);
              }
              // valuePrintGenerate(replacePointer, irb);

              irb.CreateStore(newValue, replacePointer);
            }
            else if (isXMMPtrTy(newPointer->getType()))
            {
              Value *castVal = newValue;
              if (!newValue->getType()->isIntegerTy())
              {
                castVal = irb.CreatePtrToInt(newValue, irb.getInt64Ty());
              }
              Constant *nullVec = Constant::getNullValue(XMM);
              Constant *nullValue =
                  Constant::getNullValue(Type::getInt64Ty(clone->getContext()));
              Value *vec1 =
                  irb.CreateInsertElement(nullVec, nullValue, uint64_t(0));
              Value *vec2 = irb.CreateInsertElement(vec1, castVal, uint64_t(1));
              irb.CreateStore(vec2, newPointer);
            }
            else if (isFunctionPtrTy(newValue->getType()))
            {
            }
            else
            {
              // Ex) store i8* %84, i8** %saved_stack, align 8
              irb.CreateStore(newValue, newPointer);
            }
          }
        }
        else if (isFunctionPtrTy(newValue->getType()))
        {
        }
        else if (isXMMTy(newPointer->getType()))
        {
          // 통과

          Value *clearTag = ununTag(newPointer, pointer->getType(), irb);
          if (isXMMTy(newValue->getType()))
          {
            Value *clearVal = ununTag(newValue, value->getType(), irb);

            irb.CreateStore(clearVal, clearTag);
          }
          else
            irb.CreateStore(newValue, clearTag);
        }
        else
        {
          if (isXMMTy(newPointer->getType()->getPointerElementType()))
          {
            // 포인터의 element type이 XMM type임
            if (isXMMTy(newValue->getType()))
            {
              irb.CreateStore(newValue, newPointer);
            }
            else
            {
              Value *castVal = newValue;
              if (!newValue->getType()->isIntegerTy())
              {
                castVal = irb.CreatePtrToInt(newValue, irb.getInt64Ty());
              }
              Constant *nullVec = Constant::getNullValue(XMM);
              Constant *nullValue =
                  Constant::getNullValue(Type::getInt64Ty(clone->getContext()));
              Value *vec1 =
                  irb.CreateInsertElement(nullVec, nullValue, uint64_t(0));
              Value *vec2 = irb.CreateInsertElement(vec1, castVal, uint64_t(1));
              irb.CreateStore(vec2, newPointer);
            }
          }
          else
          {
            // 이 경우 거의 더블 포인터

            if (isXMMTy((newValue->getType())))
            {
              Value *replaceValue =
                  ununTag(newValue, I.getOperand(0)->getType(), irb);

              irb.CreateStore(replaceValue, newPointer);
            }
            else
            {
              StoreInst *si = irb.CreateStore(newValue, newPointer);
            }
          }
        }
      }
      else
      {
        // 글로벌 변수
        // ptr이 글로벌 변수
        //
        // 글로벌도 이제 그냥 변수처럼 취급해주기
        // 다 바꿨으니까

        StoreInst *si = dyn_cast<StoreInst>(&I);
        Value *ptr = si->getPointerOperand();
        if (GlobalVariable *gv = dyn_cast_or_null<GlobalVariable>(ptr))
        {
          Value *value = si->getValueOperand();
          Value *newValue = valToVal.count(value) ? valToVal[value] : value;

          if (gToGV.count(gv) > 0)
          {
            errs() << " 여기다\n";
            exit(0);
          }
          if (isXMMTy(newValue->getType()))
          {
            newValue = ununTag(newValue, value->getType(), irb);
          }

          irb.CreateStore(newValue, ptr);
        }
        else
        {
          // Ptr is ConstantExpr.
          // Global 변수일경우에 대해서 대처 해야함 포인터의 내부 element 의 포인터로 가는 경우
          // store %struct.av* %100, %struct.av** bitcast (%struct.av.149** @PL_curstack to %struct.av**), align 8
          Value *newValue = valToVal.count(value) ? valToVal[value] : value;
          // ptr = cloneConstantExpr(ptr,)
          if (ConstantExpr *cExpr = dyn_cast<ConstantExpr>(ptr))
          {
            ptr = cloneConstantExpr(cExpr, valToVal);
          }
          StoreInst *si = irb.CreateStore(newValue, ptr);
        }
      }
      break;
    }
    case Instruction::Load:
    {
      // Load 는 오히려 심플
      Value *origPointer = I.getOperand(0);

      if (valToVal.count(origPointer) > 0)
      {
        Value *pointer = valToVal[origPointer];
        if (isXMMTy(pointer->getType()))
        {
          // 여기서 포인터의 포인터일경우 에는 다르게 해야함

          Type *loadType = origPointer->getType();
          Value *clearTagPointer;
          if (I.getType()->isPointerTy() && !isFunctionPtrTy(I.getType()))
          {
            if (constAliases.count(dyn_cast<Instruction>(I.getOperand(0))))
            {
              clearTagPointer =
                  ununTag(pointer, I.getOperand(0)->getType(), irb,
                          origPointer->hasName()
                              ? origPointer->getName().str() + "CONST"
                              : "CONST");
            }
            else
              clearTagPointer =
                  ununTag(pointer, XMM_POINTER, irb,
                          origPointer->hasName()
                              ? origPointer->getName().str() + "XMM_POINTER_GET"
                              : "XMM_POINTER_GET");
            // clearTagPointer = ununTag(
            //     pointer, loadType, irb,
            //     origPointer->hasName() ? origPointer->getName().str() :
            //     "");
          }
          else
          {
            clearTagPointer = ununTag(
                pointer, loadType, irb,
                origPointer->hasName() ? origPointer->getName().str() : "");
          }
          Value *replaceInst;

          replaceInst =
              irb.CreateLoad(clearTagPointer, origPointer->hasName()
                                                  ? origPointer->getName().str()
                                                  : "unwrap_pointer");

          valToVal[dyn_cast<Value>(&I)] = replaceInst;
        }
        else
        {
          Value *newLoad = irb.CreateLoad(pointer);
          valToVal[dyn_cast<Value>(&I)] = newLoad;
        }
      }
      else
      {
        Value *op = I.getOperand(0);
        if (GlobalValue *gv = dyn_cast_or_null<GlobalValue>(op))
        {
          Instruction *newInst = I.clone();
          clone->getInstList().push_back(newInst);
          valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
        }
        else
        {
          // 찾앗다
          // example  %95 = load i32, i32* getelementptr inbounds
          // (%struct.stats_t, %struct.stats_t* @stats, i32 0, i32 5), align
          // 8 ConstantExpr
          Instruction *newInst = I.clone();
          if (ConstantExpr *cExpr = dyn_cast<ConstantExpr>(newInst->getOperand(0)))
          {
            Value *newOp = cloneConstantExpr(cExpr, valToVal);
            newInst = irb.CreateLoad(newOp, "new.cons");
          }
          else
          {
            clone->getInstList().push_back(newInst);
          }
          valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
        }
      }
      break;
    }
    case Instruction::GetElementPtr:
    {
      // 일단 GEP-> 타겟 포인터
      // GEP 복사 X
      // GEP의 Base Pointer 가 Struct Type 이라면,
      // Struct -> Struct' 로 매핑 (Struct 는 원래의 Struct, 변형된 것이
      // Struct') Struct' 의 멤버로 매핑되게... 하기 Struct' 의 멤버가
      // Double Pointer 에 대해서 하는 방법 생각하기

      GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(&I);
      Value *base = gep->getPointerOperand();
      Value *realBase = gep->getPointerOperand();

      if (argToArg.count(base->getName()))
      {
        // 인자를 지역변수에 저장할 때
        Value *newBase = cloneFunc->getArg(argToArg[base->getName()]);
        std::vector<Value *> plist;
        Value *newGEP;
        for (auto i = gep->idx_begin(); i != gep->idx_end(); i++)
        {
          Value *val = *i;
          if (valToVal.count(val) > 0)
          {
            plist.push_back(valToVal[val]);
          }
          else
          {
            plist.push_back(val);
          }
        }
        if (gep->isInBounds())
        {
          newGEP = irb.CreateInBoundsGEP(
              newBase, plist, gep->hasName() ? gep->getName() + "arg" : "arg");
        }
        else
        {
          newGEP = irb.CreateGEP(
              newBase, plist, gep->hasName() ? gep->getName() + "arg" : "arg");
        }
        valToVal[gep] = newGEP;
        break;
      }
      if (fixGEPforStruct(gep, valToVal, irb))
      {
        break;
      }
      if (valToVal.count(base) > 0)
      {
        // 여기는 변환되지 않은 구조체들에 대해서 처리 하는 곳
        PointerType *baseType = dyn_cast<PointerType>(base->getType());
        Value *tempPointer = valToVal[base];
        if (argToArg.count(tempPointer->getName()))
        {
          // argument
          // by value
          std::vector<Value *> plist;

          for (auto i = gep->idx_begin(); i != gep->idx_end(); i++)
          {
            Value *val = *i;
            if (valToVal.count(val) > 0)
            {
              plist.push_back(valToVal[val]);
            }
            else
            {
              plist.push_back(val);
            }
          }
          Value *newGEP;
          if (gep->isInBounds())
          {
            newGEP = irb.CreateInBoundsGEP(
                tempPointer, plist,
                gep->hasName() ? gep->getName() + "arg" : "arg");
          }
          else
          {
            newGEP =
                irb.CreateGEP(tempPointer, plist,
                              gep->hasName() ? gep->getName() + "arg" : "arg");
          }
          valToVal[gep] = newGEP;
          break;
        }
        if (baseType->getPointerElementType()->isStructTy())
        {
          // 이것도 마찬가지
          // SSA의 특성을 이용하자
          StructType *origStruct =
              dyn_cast<StructType>(baseType->getPointerElementType());

          StructType *newStruct = origStruct;
          Value *newBase = valToVal[base];
          if (isXMMTy(newBase->getType()))
          {
            Value *unTagBase =
                ununTag(newBase, newStruct->getPointerTo(), irb, "here?");
            std::vector<Value *> plist;
            for (auto i = gep->idx_begin(); i != gep->idx_end(); i++)
            {
              Value *val = *i;
              if (valToVal.count(val) > 0)
              {
                plist.push_back(valToVal[val]);
              }
              else
              {
                plist.push_back(val);
              }
            }
            if (gep->isInBounds())
            {
              Value *newGEP = irb.CreateInBoundsGEP(
                  unTagBase, plist,
                  gep->hasName() ? gep->getName() + "struct.inbound"
                                 : "struct.inbound");
              GetElementPtrInst *NewGEP = dyn_cast<GetElementPtrInst>(newGEP);

              assertGEP(newGEP);
              valToVal[dyn_cast<Value>(&I)] = newGEP;
            }
            else
            {
              Value *newGEP = irb.CreateGEP(unTagBase, plist);
              assertGEP(newGEP);
              valToVal[dyn_cast<Value>(&I)] = newGEP;
            }
          }
          else
          {
            Value *newBase = valToVal[base];
            if (arrToPtr.count(base) > 0)
            {
              Value *wrapPtr = arrToPtr[base];
              Value *l4Ptr = irb.CreateLoad(wrapPtr, "array.load");
              // Value *unWrapPtr = ununTag(l4Ptr, base->getType(), irb);
              PointerType *pt = dyn_cast<PointerType>(I.getType());
              ArrayType *at = dyn_cast<ArrayType>(pt->getElementType());
              Value *offset = emitGEPOffset(irb, *DL, gep, valToVal);

              if (at->getArrayElementType()->isPointerTy())
              {
                //함수 포인터 배열도 안 되게 해야함 
                if (constAliases.count(&I) > 0)
                  offset = offset;
                else if (isFunctionPtrTy(at->getArrayElementType()))
                  offset = offset;
                else
                  offset = irb.CreateMul(offset, ConstantInt::get(irb.getInt64Ty(), 2), "twox.offset");
              }
              // 더블 포인터면 두배가 되게 해주고
              // 스트럭트 타입이면 바꿔주고 해야함 -->struct type은 emitGEPOffset에서 해주고 있음
              Constant *nullVec = Constant::getNullValue(XMM);
              Value *tag = createOffsetMask(irb, offset);
              Value *v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
              Value *v1 = irb.CreateInsertElement(v0, offset, 1);
              Value *replaceInst =
                  irb.CreateAdd(l4Ptr, v1,
                                gep->hasName() ? gep->getName() + ".array"
                                               : l4Ptr->getName() + ".array");
              valToVal[dyn_cast<Value>(&I)] = replaceInst;
            }
            else
            {
              std::vector<Value *> plist;
              for (auto i = gep->idx_begin(); i != gep->idx_end(); i++)
              {
                Value *val = *i;
                if (valToVal.count(val) > 0)
                  plist.push_back(valToVal[val]);
                else
                  plist.push_back(val);
              }
              if (gep->isInBounds())
              {
                // 문제 찾았음 여기가 문제고

                Value *newGEP =
                    irb.CreateInBoundsGEP(newBase, plist, "HERE.PROBLEM");
                assertGEP(newGEP);
                valToVal[dyn_cast<Value>(&I)] = newGEP;
              }
              else
              {
                Value *newGEP = irb.CreateGEP(newBase, plist);
                assertGEP(newGEP);
                valToVal[dyn_cast<Value>(&I)] = newGEP;
              }
            }
          }
        }
        else if (base->getType()->getPointerElementType()->isArrayTy())
        {
          if (arrToPtr.count(base))
          {
            Value *wrapPtr = arrToPtr[base];
            Value *l4Ptr = irb.CreateLoad(wrapPtr);
            // Value *unWrapPtr = ununTag(l4Ptr, base->getType(), irb);

            Value *offset = emitGEPOffset(irb, *DL, gep, valToVal);
            PointerType *pt = dyn_cast<PointerType>(I.getType());
            ArrayType* at = dyn_cast<ArrayType>(pt->getElementType());
            if (pt->getElementType()->isPointerTy())
            {
              // 함수 포인터 배열도 안되게 해야함 
              if (constAliases.count(&I) > 0)
                offset = offset;
              else if (isFunctionPtrPtrTy(pt))
                  offset = offset;
              else
                offset = irb.CreateMul(offset, ConstantInt::get(irb.getInt64Ty(), 2), "twox.offset");
            }
            Constant *nullVec = Constant::getNullValue(XMM);
            Value *tag = createOffsetMask(irb, offset);
            Value *v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
            Value *v1 = irb.CreateInsertElement(v0, offset, 1);
            Value *replaceInst =
                irb.CreateAdd(l4Ptr, v1,
                              gep->hasName() ? gep->getName() + ".array"
                                             : l4Ptr->getName() + ".array");
            valToVal[dyn_cast<Value>(&I)] = replaceInst;
          }
          else
          {
            // 이 경우 ARRAY 인데 구조체의 배열일경우에 여기로 옴
            //  그냥 똑같이 해야할 듯
            //  여기서 그거 구현해서 할라면 할 수 있음
            //  하지만 안함
            Value *newBase = valToVal[base];
            Value *newGEP;
            if (isXMMTy(newBase->getType()))
            {
              ArrayType *AT =
                  dyn_cast<ArrayType>(base->getType()->getPointerElementType());
              if (AT->getArrayElementType()->isPointerTy())
              {
                Value *offset = emitGEPOffset(irb, *DL, gep, valToVal);

                Constant *two = ConstantInt::get(irb.getInt64Ty(), 2);
                offset = irb.CreateMul(offset, two, "twoX");

                // valuePrintGenerate(offset, irb);
                Constant *nullVec = Constant::getNullValue(XMM);
                Value *tag = createOffsetMask(irb, offset);
                Value *v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
                Value *v1 = irb.CreateInsertElement(v0, offset, 1);
                newGEP =
                    irb.CreateAdd(newBase, v1,
                                  gep->hasName() ? gep->getName()
                                                 : newBase->getName() + ".idx");
              }
              else
              {
                newGEP = splatGEP(gep, valToVal, irb);
              }
              valToVal[dyn_cast<Value>(gep)] = newGEP;
              break;
            }
            if (gep->isInBounds())
            {
              Value *newBase = valToVal[base];
              std::vector<Value *> plist;
              for (auto i = gep->idx_begin(); i != gep->idx_end(); i++)
              {
                Value *val = *i;
                Type *type = gep->getTypeAtIndex(
                    cast<PointerType>(
                        gep->getPointerOperand()->getType()->getScalarType())
                        ->getElementType(),
                    val);
                if (valToVal.count(val) > 0)
                  plist.push_back(valToVal[val]);
                else
                  plist.push_back(val);
              }
              Value *newGEP = irb.CreateInBoundsGEP(newBase, plist, "ARRAY");
              assertGEP(newGEP);
              valToVal[dyn_cast<Value>(gep)] = newGEP;
            }
          }
        }
        else if (AllocaInst *ai = dyn_cast<AllocaInst>(base))
        {
          if (ai->getAllocatedType()->isArrayTy())
          {
            Value *wrapPtr = arrToPtr[base];
            Value *l4Ptr = irb.CreateLoad(wrapPtr);
            Value *unWrapPtr = ununTag(l4Ptr, base->getType(), irb);

            Value *offset = emitGEPOffset(irb, *DL, gep, valToVal);

            Constant *nullVec = Constant::getNullValue(XMM);
            Value *tag = createOffsetMask(irb, offset);
            Value *v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
            Value *v1 = irb.CreateInsertElement(v0, offset, 1);
            Value *replaceInst =
                irb.CreateAdd(l4Ptr, v1,
                              gep->hasName() ? gep->getName() + ".array"
                                             : l4Ptr->getName() + ".array");
            valToVal[dyn_cast<Value>(&I)] = replaceInst;
          }
          else if (ai->isArrayAllocation())
          {
            Value *wrapPtr = arrToPtr[base];
            Value *l4Ptr = irb.CreateLoad(wrapPtr);

            Value *offset = emitGEPOffset(irb, *DL, gep, valToVal);

            Constant *nullVec = Constant::getNullValue(XMM);
            Value *tag = createOffsetMask(irb, offset);
            Value *v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
            Value *v1 = irb.CreateInsertElement(v0, offset, 1);
            Value *replaceInst = irb.CreateAdd(
                l4Ptr, v1,
                gep->hasName() ? gep->getName() : l4Ptr->getName() + ".idx");
            valToVal[dyn_cast<Value>(&I)] = replaceInst;
          }
          else
          {
            // 레퍼런스 변수 일수도 있음
            errs() << "error!\n";
            exit(0);
          }
        }
        else
        {
          // 배열도 아니고
          // 구조체도 아닌 곳
          Value *newBase = valToVal[base];

          if (isXMMPtrTy(newBase->getType()))
          {
            Value *offset = emitGEPOffset(irb, *DL, gep, valToVal);
            Value *ConstOffset = nullptr;
            bool isPositive = hasNegativeOffset(gep);

            Constant *nullVec = Constant::getNullValue(XMM);
            Value *tag = createOffsetMask(irb, offset);
            Value *v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
            Value *v1 = irb.CreateInsertElement(v0, offset, 1);
            Value *replaceInst = irb.CreateAdd(
                newBase, v1,
                gep->hasName() ? gep->getName() : newBase->getName() + ".idx");

            valToVal[dyn_cast<Value>(&I)] = replaceInst;
          }
          else if (isXMMTy(newBase->getType()))
          {
            // Value *unTagBase =
            //     ununTag(newBase, base->getType(), irb, "100.here");
            // std::vector<Value *> plist;
            // for (auto i = gep->idx_begin(); i != gep->idx_end(); i++)
            // {
            //   Value *val = *i;
            //   if (valToVal.count(val) > 0)
            //     plist.push_back(valToVal[val]);
            //   else
            //     plist.push_back(val);
            // }
            // Value *newGEP;
            // if (gep->isInBounds())
            // {
            //   newGEP = irb.CreateInBoundsGEP(unTagBase, plist);
            //   assertGEP(newGEP);
            // }
            // else
            // {
            //   newGEP = irb.CreateGEP(unTagBase, plist);
            //   assertGEP(newGEP);
            // }

            Value *offset = emitGEPOffset(irb, *this->DL, gep, valToVal);
            PointerType *pt =
                dyn_cast<PointerType>(gep->getPointerOperandType());
            if (pt->getPointerElementType()->isPointerTy())
            {
              Constant *two = ConstantInt::get(irb.getInt64Ty(), 2);
              offset = irb.CreateMul(offset, two, "twoX");
            }
            // valuePrintGenerate(offset, irb);
            Constant *nullVec = Constant::getNullValue(XMM);
            Value *tag = createOffsetMask(irb, offset);
            Value *v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
            Value *v1 = irb.CreateInsertElement(v0, offset, 1);
            Value *replaceInst = irb.CreateAdd(
                newBase, v1,
                gep->hasName() ? gep->getName() : newBase->getName() + ".idx");
            valToVal[dyn_cast<Value>(&I)] = replaceInst;
          }
          else
          {
            std::vector<Value *> plist;
            for (auto i = gep->idx_begin(); i != gep->idx_end(); i++)
            {
              Value *val = *i;
              Type *type = gep->getTypeAtIndex(
                  cast<PointerType>(
                      gep->getPointerOperand()->getType()->getScalarType())
                      ->getElementType(),
                  val);
              if (valToVal.count(val) > 0)
                plist.push_back(valToVal[val]);
              else
                plist.push_back(val);
            }
            if (gep->isInBounds())
            {
              Value *newGEP =
                  irb.CreateInBoundsGEP(newBase, plist, "isDouble?");
              assertGEP(newGEP);
              valToVal[dyn_cast<Value>(&I)] = newGEP;
            }
            else
            {
              Value *newGEP = irb.CreateGEP(newBase, plist);
              assertGEP(newGEP);
              valToVal[dyn_cast<Value>(&I)] = newGEP;
            }
          }
        }
      }
      else
      {
        // Base Pointer is global variable;
        // Value* newBase = valToVal[base];
        std::vector<Value *> plist;
        for (auto i = gep->idx_begin(); i != gep->idx_end(); i++)
        {
          Value *val = *i;
          // valuePrint(val, "op");
          if (valToVal.count(val) > 0)
            plist.push_back(valToVal[val]);
          else
            plist.push_back(val);
        }
        if (gep->isInBounds())
        {
          // valuePrint(base, "newBase");
          // instPrint(&I, "I");

          Value *newGEP = irb.CreateInBoundsGEP(base, plist, "global");
          if (!isa<ConstantExpr>(newGEP))
            assertGEP(newGEP);
          valToVal[dyn_cast<Value>(&I)] = newGEP;
        }
        else
        {
          Value *newGEP = irb.CreateGEP(base, plist);
          assertGEP(newGEP);
          valToVal[dyn_cast<Value>(&I)] = newGEP;
        }
      }
      break;
    }
    case Instruction::Call:
    {
      CallInst *CI = dyn_cast<CallInst>(&I);
      Function *callee = CI->getCalledFunction();
      Instruction *cloneI;
      if (!callee)
      {
        // if callee is null, callee is declaration.
        // 왜 인지 모르겠으나 declaration 함수가  null 인 경우가 있음
        // 이제 왜인지 알지
        // Caller에 해당하는 opearand가 ConstantExpr 인 경우임
        Value *newCons;

        // cloneI = I.clone();
        // clone->getInstList().push_back(cloneI);
        if (ConstantExpr *cExpr =
                dyn_cast<ConstantExpr>(CI->getCalledOperand()))
        {
          switch (cExpr->getOpcode())
          {
          case Instruction::BitCast:
            Value *op;
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
        }
        else if (Value *calleeVal = dyn_cast<Value>(CI->getCalledOperand()))
        {
          newCons = valToVal[calleeVal];
        }

        FunctionType *ft;
        if (newCons->getType()->isPointerTy())
        {
          PointerType *PT = dyn_cast<PointerType>(newCons->getType());
          ft = dyn_cast<FunctionType>(PT->getPointerElementType());
        }
        else
          ft = dyn_cast<FunctionType>(newCons->getType());

        std::vector<Value *> args;
        for (unsigned int i = 0; i < CI->getNumArgOperands(); i++)
        {
          Value *arg = CI->getArgOperand(i);
          if (valToVal.count(arg) > 0)
          {
            Value *newArg = valToVal[arg];

            Type *type = ft->getParamType(i);

            if (isXMMPtrTy(newArg->getType()))
            {
              if (arrToPtr.count(arg) > 0)
              {
                Value *wrapPtr = arrToPtr[arg];
                Value *l4Ptr = irb.CreateLoad(wrapPtr);
                Value *unWrapPtr = ununTag(l4Ptr, type, irb);
                args.push_back(unWrapPtr);
              }
              else
              {
                Value *ptr =
                    irb.CreateBitCast(newArg, irb.getInt64Ty()->getPointerTo());
                Value *idx = ConstantInt::get(irb.getInt64Ty(), 1);
                Value *newPtr =
                    irb.CreateInBoundsGEP(irb.getInt64Ty(), ptr, idx);
                Value *newInsertArg = irb.CreateBitCast(newPtr, type, "HERE");
                args.push_back(newInsertArg);
              }
            }
            else if (isXMMTy(newArg->getType()))
            {
              Value *tempArg = irb.CreateAlloca(XMM, nullptr, "temp.arg");
              irb.CreateStore(newArg, tempArg);

              Value *p = irb.CreateBitCast(tempArg, type);
              args.push_back(p);
            }
            else
              args.push_back(newArg);
          }
          else
            args.push_back(arg);
        }
        Value *newCI = irb.CreateCall(ft, newCons, args, CI->getName());
        valToVal[dyn_cast<Value>(CI)] = newCI;

        break;
      }
      if (callee->isDeclaration() || isUserAllocation(callee))
      {
        // 포인터들 다 언랩핑하기
        // 여기서는 오퍼랜드만 교체하기

        // 순서만 바꾸면 될듯
        cloneI = I.clone();
        clone->getInstList().push_back(cloneI);
        bool isPthread = false;
        CI = dyn_cast<CallInst>(cloneI);
        if (MemCpyInst *mci = dyn_cast<MemCpyInst>(&I))
        {
          Value *newValue;
          CallInst *tempCI = dyn_cast<CallInst>(&I);

          Value *op0 = valToVal.count(tempCI->getArgOperand(0)) > 0
                           ? valToVal[tempCI->getArgOperand(0)]
                           : tempCI->getArgOperand(0);
          Value *op1 = valToVal.count(tempCI->getArgOperand(1)) > 0
                           ? valToVal[tempCI->getArgOperand(1)]
                           : tempCI->getArgOperand(1);
          if (isXMMTy(op0->getType()))
          {
            op0 = ununTag(op0, irb.getInt8PtrTy(), irb);
          }
          if (isXMMTy(op1->getType()))
          {
            op1 = ununTag(op1, irb.getInt8PtrTy(), irb);
          }
          Value *Size = tempCI->getOperand(2);
          Size = valToVal.count(Size) ? valToVal[Size] : Size;
          if (!isa<Constant>(Size))
          {
          }
          else if (BitCastInst *bci = dyn_cast<BitCastInst>(op0))
          {
            if (StructType *st = dyn_cast<StructType>(
                    bci->getSrcTy()->getPointerElementType()))
            {
              // typePrint(st, "st");
              st = strucTyToStructTy.count(st) > 0 ? strucTyToStructTy[st] : st;
              unsigned int size = DL->getTypeAllocSize(st);
              Size = irb.getInt64(size);
            }
            else
            {
              unsigned int size = DL->getPointerTypeSize(
                  bci->getSrcTy()->getPointerElementType());
              Size = irb.getInt64(size);
            }
          }
          // valuePrint(op0, "op0");
          newValue = irb.CreateMemCpy(op0, mci->getDestAlign(), op1,
                                      mci->getSourceAlign(), Size);
          valToVal[&I] = newValue;
          cloneI->eraseFromParent();
          break;
        }
        for (unsigned int i = 0; i < CI->getNumArgOperands(); i++)
        {
          Value *arg = CI->getArgOperand(i);
          if (arg->getType()->isPointerTy())
          {
            PointerType *pt = dyn_cast<PointerType>(arg->getType());
            if (pt->getPointerElementType()->isFunctionTy())
              isPthread = true;
          }
        }
        if (CI->getCalledFunction()->getName() == "pthread_create")
          isPthread = true;

        IRBuilder<> tempIRB(cloneI);
        if (isPthread)
        {
          for (unsigned int i = 0; i < CI->getNumArgOperands(); i++)
          {
            Value *arg = CI->getArgOperand(i);
            Value *newOp;
            switch (i)
            {
            case 0:
            case 1:
            {
              if (valToVal.count(arg) > 0)
              {
                Value *newArg = valToVal[arg];
                if (isXMMTy(newArg->getType()))
                {
                  newOp = ununTag(newArg, arg->getType(), tempIRB);
                }
                else
                {
                  newOp = newArg;
                }
              }
              else
              {
                newOp = arg;
              }

              CI->setOperand(i, newOp);

              break;
            }

            case 2:
            {
              if (valToVal.count(arg) > 0)
              {
                newOp = valToVal[arg];
              }
              else
              {
                // arg is global function
                newOp = arg;
              }
              CI->setOperand(i, newOp);
              break;
            }
            case 3:
            {
              if (valToVal.count(arg) > 0)
              {
                Value *newArg = valToVal[arg];
                if (isXMMTy(newArg->getType()))
                {
                  Value *tempArg =
                      tempIRB.CreateAlloca(XMM, nullptr, "temp.arg");
                  tempIRB.CreateStore(newArg, tempArg);
                  newOp = tempIRB.CreateBitCast(tempArg, arg->getType());
                }
                else
                {
                  Constant *nullXMM = Constant::getNullValue(XMM);
                  Value *intToPtr = tempIRB.CreatePtrToInt(
                      newArg, Type::getInt64Ty(arg->getContext()));
                  Value *newArg = tempIRB.CreateInsertElement(nullXMM, intToPtr,
                                                              (uint64_t)1);
                  Value *tempArg =
                      tempIRB.CreateAlloca(XMM, nullptr, "temp.arg");
                  tempIRB.CreateStore(newArg, tempArg);
                  newOp = tempIRB.CreateBitCast(tempArg, arg->getType());
                }
              }
              else
              {
                Constant *nullXMM = Constant::getNullValue(XMM);

                Value *tempArg = tempIRB.CreateAlloca(XMM, nullptr, "temp.arg");
                tempIRB.CreateStore(arg, tempArg);
                newOp = tempIRB.CreateBitCast(tempArg, arg->getType());
              }
              CI->setOperand(i, newOp);
              break;
            }
            default:
            {
              if (valToVal.count(arg) > 0)
              {
              }
              else
              {
              }
              break;
            }
            }
          }
          break;
        }
        for (unsigned int i = 0; i < CI->getNumArgOperands(); i++)
        {
          Value *arg = CI->getArgOperand(i);

          if (valToVal.count(arg) > 0)
          {
            Value *newArg = valToVal[arg];
            if (arg->getType()->isPointerTy())
            {
              if (isXMMTy(newArg->getType()))
              {
                Value *newOp;

                newOp = ununTag(newArg, arg->getType(), tempIRB);
                CI->setArgOperand(i, newOp);
              }
              else if (Function *funcPointer = dyn_cast<Function>(newArg))
              {
                CI->setArgOperand(i, newArg);
              }
              else if (isXMMPtrTy(newArg->getType()))
              {
                // untag  안하는 이유
                // int * a;
                // &a가 인자로 넘어가서
                // if(arrToPtr.count(arg) > 0){
                //   // 배열 언랩핑후 하면 됨

                // } else {
                //   // not array
                // }

                if (arrToPtr.count(arg) > 0)
                {
                  Value *wrapPtr = arrToPtr[arg];
                  Value *l4Ptr = tempIRB.CreateLoad(wrapPtr);
                  Value *unWrapPtr = ununTag(l4Ptr, arg->getType(), tempIRB);
                  CI->setArgOperand(i, unWrapPtr);
                }
                else
                {
                  std::list<Value *> plist;
                  Value *idx = ConstantInt::get(irb.getInt64Ty(), 1);
                  // Value* newPtr = irb.CreateInBoundsGEP(
                  //     irb.getInt64Ty()->getPointerTo(), newArg, idx);
                  IRBuilder<> tempIRB(getInsertPointBefore(CI));
                  Value *newPtr =
                      tempIRB.CreateBitCast(newArg, arg->getType(), "HERE2");
                  CI->setArgOperand(i, newPtr);
                }
              }
              else
              {
                if (isPthread)
                {
                }
                else
                {
                  CI->setArgOperand(i, newArg);
                }
              }
            }
            else
            {
              if (isXMMPtrTy(newArg->getType()))
              {
                // untag  안하는 이유
                // int * a;
                // &a가 인자로 넘어가서
                // if(arrToPtr.count(arg) > 0){
                //   // 배열 언랩핑후 하면 됨

                // } else {
                //   // not array
                // }

                if (arrToPtr.count(arg) > 0)
                {
                  Value *wrapPtr = arrToPtr[arg];
                  Value *l4Ptr = tempIRB.CreateLoad(wrapPtr);
                  Value *unWrapPtr = ununTag(l4Ptr, arg->getType(), tempIRB);
                  CI->setArgOperand(i, unWrapPtr);
                }
                else
                {
                  std::list<Value *> plist;
                  Value *idx = ConstantInt::get(irb.getInt64Ty(), 1);
                  // Value* newPtr = irb.CreateInBoundsGEP(
                  //     irb.getInt64Ty()->getPointerTo(), newArg, idx);
                  IRBuilder<> tempIRB(getInsertPointBefore(CI));
                  Value *newPtr =
                      tempIRB.CreateBitCast(newArg, arg->getType(), "HERE2");
                  CI->setArgOperand(i, newPtr);
                }
              }
              else
                CI->setArgOperand(i, newArg);
            }
          }
        }
        valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(cloneI);
        // malloc 때문에 break; 안함

        if (isAllocation(&I) || isUserAllocation(callee))
        {
          Value *ptr = dyn_cast<Value>(cloneI); // maskMallocWrapper(irb, I);
          if (isStackValue(&I))
            break;
          Value *Size = instrumentWithByteOfMalloc(
              irb, dyn_cast<Instruction>(valToVal[dyn_cast<Value>(&I)]),
              valToVal);
          if (isCalloc(callee) || isMalloc(callee) || isUserAllocation(callee))
          {
            bool isNeedFix = fixParamAllocInst(I, valToVal, irb, true);
            if (isNeedFix)
            {
              cloneI->eraseFromParent();
              Size = instrumentWithByteOfMalloc(
                  irb, dyn_cast<Instruction>(valToVal[dyn_cast<Value>(&I)]),
                  valToVal);
            }
            ptr = valToVal[dyn_cast<Value>(&I)];
            Instruction *next = I.getNextNode();

            Value *allocaVar;
            BitCastInst *bci = nullptr;
            Instruction *origStore;

            // 일단 태그 만들기

            Value *OvSz = createMask(irb, Size, module->getContext());
            Value *PtrInt = irb.CreatePtrToInt(ptr, irb.getInt64Ty());
            Value *emptyVec = Constant::getNullValue(XMM);

            Value *vec0 = irb.CreateInsertElement(emptyVec, OvSz, (uint64_t)0);
            Value *vec1 =
                irb.CreateInsertElement(vec0, PtrInt, 1, "malloc.result");
            valToVal[dyn_cast<Value>(&I)] = vec1;
          }
          else if (isRealloc(callee))
          {
            // 여기서 스토어까지 다해야됨
            CallInst *origCI = dyn_cast<CallInst>(&I);

            Value *arg1 = origCI->getArgOperand(0);
            Value *arg2 = CI->getArgOperand(1);

            if (isXMMTy(arg1->getType()))
            {
              Value *OvSz = createMask(irb, Size, module->getContext());
              Value *idx = ConstantInt::get(irb.getInt64Ty(), 1);

              Value *newTagAddress = irb.CreateInBoundsGEP(
                  irb.getInt64Ty()->getPointerTo(), CI->getArgOperand(0), idx);
              Instruction *newStore = irb.CreateStore(OvSz, newTagAddress);
            }
            else if (isXMMPtrTy(arg1->getType()))
            {
            }
            Value *newArg = arg1;
          }
          else
          {
            errs() << "확인되지 않은 allocation\n";
            exit(0);
          }
        }
        break;
      }
      if (callee->isVarArg())
      {
        Instruction *cloneI = I.clone();
        clone->getInstList().push_back(cloneI);
        IRBuilder<> irb(cloneI);
        CI = dyn_cast<CallInst>(cloneI);
        for (unsigned int i = 0; i < CI->getNumArgOperands(); i++)
        {
          Value *arg = CI->getArgOperand(i);
          if (valToVal.count(arg) > 0)
          {
            Value *newArg = valToVal[arg];
            CI->setArgOperand(i, newArg);
          }
        }
        valToVal[dyn_cast<Value>(&I)] = cloneI;
      }
      if (funcToFunc.count(callee) > 0)
      {
        // 함수가 대체되는 경우
        Function *newCallee = funcToFunc[callee];
        if (isArgsFunction(callee))
        {
          std::vector<Value *> plist;
          for (unsigned i = 0; i < CI->getNumArgOperands(); i++)
          {
            Value *newParam = valToVal.count(CI->getArgOperand(i)) > 0
                                  ? valToVal[CI->getArgOperand(i)]
                                  : CI->getArgOperand(i);
            plist.push_back(newParam);
          }
          Value *newCall = irb.CreateCall(newCallee, plist);
          valToVal[&I] = newCall;
          break;
        }
        std::vector<Value *> plist;
        AttributeList al = callee->getAttributes();

        CI->getAttributes();
        std::vector<Type *> emptyTypes;
        std::vector<Value *> emptyArgs;
        Value *stacksave = irb.CreateIntrinsic(Intrinsic::stacksave, emptyTypes, emptyArgs);
        for (unsigned int i = 0; i < CI->arg_size(); i++)
        {
          AttributeSet attrs = al.getParamAttributes(i);
          // if the function has variable arguments, the problem occur.
          // 내일 여기부터 해결하자

          Value *funcArg = newCallee->getArg(i);
          Value *arg = CI->getArgOperand(i);

          if (attrs.getAsString().find("byval") != std::string::npos)
          {
            Value *newArg = valToVal.count(arg) ? valToVal[arg] : arg;
            if (isXMMTy(newArg->getType()))
            {
              newArg = ununTag(newArg, arg->getType(), irb);
            }
            plist.push_back(newArg);

            continue;
          }
          else if (attrs.getAsString().find("sret") != std::string::npos)
          {
            Value *newArg = valToVal.count(arg) ? valToVal[arg] : arg;
            if (isXMMTy(newArg->getType()))
            {
              newArg = ununTag(newArg, arg->getType(), irb);
            }
            plist.push_back(newArg);
            continue;
          }
          // 일단 타입별로
          //
          //
          if (isFunctionPtrTy(funcArg->getType()))
          {
            Value *newArg = valToVal.count(arg) ? valToVal[arg] : arg;
            plist.push_back(newArg);
          }
          else if (funcArg->getType()->isPointerTy())
          {
            if (valToVal.count(arg) > 0)
            {
              Value *newArg = valToVal[arg];
              Value *tempArg = irb.CreateAlloca(XMM, nullptr, "temp.arg");
              AllocaInst *AI = dyn_cast<AllocaInst>(tempArg);
              if (isXMMTy(newArg->getType()))
              {
                irb.CreateStore(newArg, tempArg);
                Value *bitCast = irb.CreateBitCast(tempArg, funcArg->getType());
                plist.push_back(bitCast);

                // Value* ptr = irb.CreateExtractElement(newArg, (uint64_t)1);
                // Value* tag = irb.CreateExtractElement(newArg, (uint64_t)0);
                // plist.push_back(tag);
                // plist.push_back(ptr);
              }
              else
              {
                Value *ptr = newArg->getType()->isPointerTy()
                                 ? irb.CreatePtrToInt(newArg, irb.getInt64Ty())
                                 : irb.CreateBitCast(newArg, irb.getInt64Ty());

                Constant *nullVec = Constant::getNullValue(XMM);
                Value *vec2 =
                    irb.CreateInsertElement(nullVec, ptr, uint64_t(1));
                irb.CreateStore(vec2, tempArg);
                Value *bitCast = irb.CreateBitCast(tempArg, funcArg->getType());
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
            }
            else
            {
              Value *newArg;
              if (isa<Instruction>(arg))
              {
                Instruction *newInst = I.clone();
                clone->getInstList().push_back(newInst);

                newArg = irb.CreatePtrToInt(newInst, irb.getInt64Ty());
                // 일단 가변변수를 가진 함수에서 문제가 발생함
                // 가변 변수를 가진 함수들이 호출하는 callee 들도 하지 않을것인지...
              }
              else
                newArg = irb.CreatePtrToInt(arg, irb.getInt64Ty());

              Value *nullValue = Constant::getNullValue(irb.getInt64Ty());
              Constant *nullVec = Constant::getNullValue(XMM);
              Value *v1 =
                  irb.CreateInsertElement(nullVec, nullValue, (uint64_t)0);
              Value *v2 = irb.CreateInsertElement(v1, newArg, (uint64_t)1);
              Value *tempArg = irb.CreateAlloca(XMM, nullptr, "temp.arg");
              irb.CreateStore(v2, tempArg);

              Value *p = irb.CreateBitCast(tempArg, funcArg->getType());
              plist.push_back(p);
              // 여기서는 포인터에 원래값
              // 태그에는 널 넣기
            }
          }
          else
          {
            if (valToVal.count(arg) > 0)
            {
              plist.push_back(valToVal[arg]);
            }
            else
            {
              plist.push_back(arg);
              // 그냥 arg 넣어주기
              // 거의 왠만하면 constant 일듯
            }
          }
        }

        Value *newVal = irb.CreateCall(newCallee, plist, I.getName());
        CallInst *newCallInst = dyn_cast<CallInst>(newVal);
        std::vector<Value *> stackrestoreParam;
        std::vector<Type *> stackrestoreTypes;
        stackrestoreParam.push_back(stacksave);
        // stackrestoreTypes.push_back(stacksave->getType());
        irb.CreateIntrinsic(Intrinsic::stackrestore, stackrestoreTypes, stackrestoreParam);

        AttributeList AL;

        // AttributeSet reAS = CI->getAttributes(AttributeList::ReturnIndex);

        for (unsigned int i = 0; i < newCallInst->getNumArgOperands(); ++i)
        {

          AttributeSet asCI = CI->getAttributes().getAttributes(
              i + AttributeList::FirstArgIndex);
          AttrBuilder B(asCI);

          for (Attribute attr : asCI)
          {
            Attribute newAttr = attr;
            if (attr.hasAttribute(Attribute::AttrKind::Alignment))
            {

              valuePrint(newCallInst->getArgOperand(i), "??");
              Align al =
                  newCallInst->getArgOperand(i)->getPointerAlignment(*DL);

              newAttr =
                  Attribute::getWithAlignment(newCallInst->getContext(), al);
            }
            if (attr.hasAttribute(Attribute::AttrKind::ByVal))
            {
              if (attr.isTypeAttribute())
              {
                Type *attrType = attr.getValueAsType();
                if (attrType->isStructTy())
                {
                  StructType *st = dyn_cast<StructType>(attrType);
                  st = strucTyToStructTy.count(st) > 0 ? strucTyToStructTy[st]
                                                       : st;
                  newAttr = Attribute::getWithByValType(
                      newCallInst->getContext(), st);
                }
              }
            }

            newCallInst->addAttribute(i + AttributeList::FirstArgIndex,
                                      newAttr);
          }
        }
        // newCallInst->setAttributes(AL);

        valToVal[dyn_cast<Value>(&I)] = newVal;
      }
      else if (!callee->isDeclaration())
      {
        // if callee is normal function (param are not pointerty.) and not
        // declaration function!
        Instruction *cloneI = I.clone();
        clone->getInstList().push_back(cloneI);
        IRBuilder<> irb(cloneI);
        CI = dyn_cast<CallInst>(cloneI);
        for (unsigned int i = 0; i < CI->getNumArgOperands(); i++)
        {
          Value *arg = CI->getArgOperand(i);
          if (valToVal.count(arg) > 0)
          {
            Value *newArg = valToVal[arg];
            CI->setArgOperand(i, newArg);
          }
        }
        valToVal[dyn_cast<Value>(&I)] = cloneI;
      }
      break;
    }
    case Instruction::ICmp:
    {
      Instruction *newInst = I.clone();
      newInst->setName(I.getName());
      ICmpInst *iCmp = dyn_cast<ICmpInst>(&I);

      Value *op1 = iCmp->getOperand(0);
      Value *op2 = iCmp->getOperand(1);
      op1 = valToVal.count(op1) > 0 ? valToVal[op1] : op1;
      op2 = valToVal.count(op2) > 0 ? valToVal[op2] : op2;

      if (isXMMTy(op1->getType()))
      {
        op1 = ununTag(op1, iCmp->getOperand(0)->getType(), irb);
      }
      if (isXMMTy(op2->getType()))
      {
        op2 = ununTag(op2, iCmp->getOperand(1)->getType(), irb);
      }

      if (op1->getType() != op2->getType())
      {
        if (Constant *cons = dyn_cast<Constant>(op1))
        {
          op1 = Constant::getNullValue(op2->getType());
        }
        else if (Constant *cons = dyn_cast<Constant>(op2))
          op2 = Constant::getNullValue(op1->getType());
        else
        {
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
      if (arrToPtr.count(I.getOperand(0)))
      {
        Value *newOp = valToVal.count(I.getOperand(0)) > 0 ? valToVal[I.getOperand(0)] : I.getOperand(0);
        Value *newVal = irb.CreateLoad(newOp);
        valToVal[dyn_cast<Value>(&I)] = newVal;
        valuePrint(newVal, "newVal");
        break;
      }
      if (valToVal.count(I.getOperand(0)) > 0)
      {
        if (isAllocation(getInsertPointBefore(&I)))
        {
          if (isMalloc(getInsertPointBefore(&I)) || isCalloc(getInsertPointBefore(&I)))
            valToVal[dyn_cast<Value>(&I)] = valToVal[I.getOperand(0)];
          else if (isRealloc(getInsertPointBefore(&I)))
          {
            Instruction *newInst = I.clone();
            newInst->setOperand(0, valToVal[I.getOperand(0)]);
            clone->getInstList().push_back(newInst);
            valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
          }
          break;
        }
        BitCastInst *bci = dyn_cast<BitCastInst>(&I);

        Value *op = valToVal[I.getOperand(0)];

        if (isXMMTy(op->getType()))
        {
          // 이거 고치자 이게 문제임
          // Value *newOp = ununTag(op, I.getOperand(0)->getType(), irb);
          // Instruction *newInst = I.clone();
          // clone->getInstList().push_back(newInst);
          // newInst->setOperand(0, newOp);
          // newInst->setName("WHY");
          valToVal[dyn_cast<Value>(&I)] = op;
        }
        else if (isXMMPtrTy(op->getType()))
        {
          valToVal[&I] = op;
          arrToPtr[&I] = op;
          break;
        }
        else
        {
          Instruction *newInst;
          Value *newVal;
          if (bci->getDestTy()->getPointerElementType()->isStructTy())
          {
            StructType *st =
                dyn_cast<StructType>(bci->getDestTy()->getPointerElementType());

            st = findStruct(st);
            if (strucTyToStructTy.count(st) > 0)
              st = strucTyToStructTy[st];
            if (op->getType()->getPointerElementType() == st)
              valToVal[&I] = op;
            else
              // newVal = irb.CreateBitCast(op, st->getPointerTo());
              valToVal[&I] = irb.CreateBitCast(op, st->getPointerTo());
          }
          else
          {
            newInst = I.clone();
            newInst->setName("HEREBITCAST");
            newInst->setOperand(0, op);
            clone->getInstList().push_back(newInst);
            valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
          }
        }
        break;
      }
      else
      {
      }
      break;
    case Instruction::PHI:
    {
      PHINode *phi = dyn_cast<PHINode>(&I);
      Instruction *newInst = I.clone();
      PHINode *newPhi = dyn_cast<PHINode>(newInst);

      for (int i = 0; i < I.getNumOperands(); i++)
      {
        if (valToVal.count(I.getOperand(i)))
        {
          if (isXMMTy(valToVal[I.getOperand(i)]->getType()))
          {
            if (I.getOperand(i)->getType() ==
                valToVal[I.getOperand(i)]->getType())
            {
              Value *newVal = ununTag(valToVal[I.getOperand(i)],
                                      I.getOperand(i)->getType(), irb);
              newInst->setOperand(i, newVal);
            }
          }
          else
          {
            newInst->setOperand(i, valToVal[I.getOperand(i)]);
          }
        }
      }

      for (int i = 0; i < phi->getNumIncomingValues(); i++)
      {
        BasicBlock *bb = newPhi->getIncomingBlock(i);
        BasicBlock *newBB = dyn_cast<BasicBlock>(valToVal[bb]);
        newPhi->replaceIncomingBlockWith(bb, newBB);
      }
      valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
      clone->getInstList().push_back(newInst);
      break;
    }
    case Instruction::Br:
    {
      Instruction *newInst = I.clone();
      newInst->setName(I.getName());
      BranchInst *newBr = dyn_cast<BranchInst>(newInst);
      if (newBr->isConditional())
      {
        Value *oldCond = newBr->getCondition();
        Value *newCond =
            valToVal.count(oldCond) > 0 ? valToVal[oldCond] : oldCond;
        if (isa<ConstantInt>(oldCond))
        {
          ConstantInt *cons = dyn_cast<ConstantInt>(oldCond);
          newCond = ConstantInt::get(cons->getType(), cons->getValue());
        }

        newBr->setCondition(newCond);
      }
      for (int i = 0; i < I.getNumOperands(); i++)
      {
        Value *newArg = valToVal.count(I.getOperand(i)) > 0
                            ? valToVal[I.getOperand(i)]
                            : I.getOperand(i);

        newInst->setOperand(i, newArg);
      }
      clone->getInstList().push_back(newInst);
      break;
    }
    case Instruction::ZExt:
    case Instruction::SExt:
    {
      Instruction *newInst = I.clone();
      newInst->setOperand(0, valToVal[I.getOperand(0)]);
      valToVal[dyn_cast<Value>(&I)] = dyn_cast<Value>(newInst);
      clone->getInstList().push_back(newInst);
      break;
    }
    case Instruction::ExtractValue:
    {
      ExtractValueInst *evi = dyn_cast<ExtractValueInst>(&I);
      Value *op = evi->getAggregateOperand();
      op = valToVal.count(op) > 0 ? valToVal[op] : op;
      ArrayRef<unsigned int> indices = evi->getIndices();
      Value *newVal = irb.CreateExtractValue(op, indices);
      valToVal[&I] = newVal;
      break;
    }
    case Instruction::Ret:
    {
      Type *returnType = cloneFunc->getReturnType();
      if (returnType->isVoidTy())
      {
        Instruction *newInst = I.clone();
        clone->getInstList().push_back(newInst);
        break;
      }
      ReturnInst *ret = dyn_cast<ReturnInst>(&I);
      if (ret->getNumOperands() == 0)
      {
        Instruction *newInst = I.clone();
        clone->getInstList().push_back(newInst);
        break;
      }
      Value *returnValue = ret->getReturnValue();

      if (isa<ConstantPointerNull>(returnValue))
      {
        if (isXMMTy(returnType))
        {
          Value *newNullRet = Constant::getNullValue(XMM);
          irb.CreateRet(newNullRet);
        }
        else
        {
          Instruction *newInst = I.clone();
          clone->getInstList().push_back(newInst);
        }
        break;
      }

      Instruction *newInst = I.clone();
      if (valToVal.count(I.getOperand(0)) > 0)
      {
        Value *returnValue = valToVal[I.getOperand(0)];
        if (!isXMMTy(returnValue->getType()) && isXMMTy(returnType))
        {
          Value *newReturn = createL4Ptr(returnValue, irb);
          newInst->setOperand(0, newReturn);
        }
        else if (isXMMTy(returnValue->getType()) && !isXMMTy(returnType))
        {
          Value *newReturn = ununTag(returnValue, returnType, irb);
          newInst->setOperand(0, newReturn);
        }
        else
          newInst->setOperand(0, valToVal[I.getOperand(0)]);
      }
      clone->getInstList().push_back(newInst);
      break;
    }
    default:
      Instruction *newInst = I.clone();
      newInst->setName(I.getName());
      for (int i = 0; i < I.getNumOperands(); i++)
      {
        if (valToVal.count(I.getOperand(i)))
        {
          if (isXMMTy(valToVal[I.getOperand(i)]->getType()))
          {
            if (I.getOperand(i)->getType()->isPointerTy())
            {
              Value *newVal = ununTag(valToVal[I.getOperand(i)],
                                      I.getOperand(i)->getType(), irb);
              newInst->setOperand(i, newVal);
            }
            else
            {
              errs() << "newVal should be PointerTy!\n";
              exit(0);
              // newInst->setOperand(i, newVal);
            }
          }
          else
          {
            newInst->setOperand(i, valToVal[I.getOperand(i)]);
          }
        }
      }
      clone->getInstList().push_back(newInst);
      if (Value *ov = dyn_cast<Value>(&I))
        valToVal[ov] = dyn_cast<Value>(newInst);
      break;
    }
  }

  return clone;
}
void MPAvailable::eraseFunction(Function *function)
{
  for (Instruction &inst : instructions(function))
  {
    if (function->getInstructionCount() == 0)
      break;
    for (User *use : inst.users())
    {
    }
  }
}

Instruction *MPAvailable::handleAlloca(AllocaInst *alloca, IRBuilder<> &irb)
{
  if (alloca->getAllocatedType()->isPointerTy())
  {
  }
}

void MPAvailable::declareWrappingFunction(Function &F)
{
  // if (F.getName() == "main") {
  //   usedFunctionPointer.insert(&F);
  //   return;
  // }
  // if (isPassFunction(&F)) {
  //   funcToFunc[&F] = &F;
  //   return;
  // }
  if (F.getName().find("_GLOBAL__") != std::string::npos)
  {
    funcToFunc[&F] = &F;
    return;
  }
  // if (F.getName().find("global") != std::string::npos)
  // {
  //   funcToFunc[&F] = &F;
  //   return;
  // }
  if (isUserAllocation(&F) || isStringFunction(&F))
  {
    funcToFunc[&F] = &F;
    // errs() << "String Function ::" << F.getName() << "\n";
    return;
  }
  if (F.isVarArg())
  {
    errs() << F.getName() + " has var arg : ";
    typePrint(F.getFunctionType(), "F");
    funcToFunc[&F] = &F;
    return;
  }
  bool isNeedTransform = false;
  if (isUsedFunctionPointer(&F))
  {
    // usedFunctionPointer.insert(&F);
    isNeedTransform = true;
    // return;
  }
  bool mustWrapped = false;
  Function *newFunc;
  std::map<Value *, Value *> valToVal;
  std::map<StringRef, int> argToArg;
  std::map<BasicBlock *, BasicBlock *> basicToBasic;
  std::map<Value *, Type *> valToType;
  // if (isa<Constant>(&F)) return;

  int i = 0;
  std::vector<Type *> plist;

  for (Argument &arg : F.args())
  {
    Value *vArg = dyn_cast<Value>(&arg);
    if (isFunctionPtrTy(arg.getType()))
    {
      PointerType *ptrTy = dyn_cast<PointerType>(arg.getType());
      Type *elementType = ptrTy->getPointerElementType();
      FunctionType *funcType = dyn_cast<FunctionType>(elementType);
      Type *newType = createFunctionType(funcType);
      plist.push_back(newType->getPointerTo());
    }
    else if (arg.getType()->isPointerTy())
    {
      plist.push_back(createNewPointerType(arg.getType()));
    }
    // else {
    //    plist.push_back(arg.getType());
    //  }
    //  i++;
    else
      plist.push_back(arg.getType());
  }

  // else {
  //   for (Argument& arg : F.args()) {
  //     Value* vArg = dyn_cast<Value>(&arg);
  //     plist.push_back(arg.getType());
  //   }
  // }
  Type *returnType;
  if (F.getReturnType()->isPointerTy())
  {
    if (isNeedTransform)
    {

      returnType = createNewPointerType(F.getReturnType());
    }
    else
      returnType = XMM;
  }
  else
  {
    returnType = F.getReturnType();
    if (returnType->isStructTy())
    {
      StructType *st = dyn_cast<StructType>(returnType);
      if (st->isLiteral())
      {
        st = findStruct(st);
      }
      returnType =
          strucTyToStructTy.count(st) > 0 ? strucTyToStructTy[st] : returnType;
    }
  }
  // typePrint(F.getFunctionType(), F.getName().str());
  FunctionType *newFT = FunctionType::get(returnType, plist, F.isVarArg());
  // typePrint(newFT, "Wrapping_" + F.getName().str());

  newFunc = Function::Create(newFT, F.getLinkage(), "Wrapping_" + F.getName());

  std::vector<AttributeSet> argAttrVec;
  Module *m = F.getParent();

  m->getFunctionList().insert(F.getIterator(), newFunc);
  // m->getFunctionList().insert(Module::iterator(F), newFunc);

  AttributeList pal = F.getAttributes();

  AttrBuilder fnAttr = pal.getFnAttributes();

  // newFunc->copyAttributesFrom(&F);

  // AttributeList newAttrList = newFunc->getAttributes();
  // errs() << "Fn attr : " << pal.getFnAttributes().getAsString() << "\n";
  newFunc->addAttributes(AttributeList::FunctionIndex, pal.getFnAttributes());
  // errs() << "ret attr : " << pal.getRetAttributes().getAsString() << "\n";
  // alignment는 바꿀수 없음!
  for (int i = 0; i < F.arg_size(); i++)
  {
    // newAttrList = newAttrList.removeParamAttributes(F.getContext(), i);
    // AttrBuilder B(pal.getFnAttributes());
    AttrBuilder B(pal.getParamAttributes(i));
    if (F.getArg(i)->hasByValAttr() || F.getArg(i)->hasInAllocaAttr() ||
        F.getArg(i)->hasStructRetAttr() || F.getArg(i)->hasReturnedAttr())
    {
      if (F.getArg(i)->hasByValAttr())
      {
        Attribute attr = F.getArg(i)->getAttribute(Attribute::AttrKind::ByVal);
        if (attr.isTypeAttribute())
        {
          Type *type = attr.getValueAsType();
          if (type->isStructTy())
          {
            StructType *st = dyn_cast<StructType>(type);
            st = strucTyToStructTy.count(st) > 0 ? strucTyToStructTy[st] : st;
            B.removeAttribute(Attribute::AttrKind::ByVal);
            B.addAttribute(
                Attribute::getWithByValType(newFunc->getContext(), st));
          }
        }
      }
      if (PointerType *pt = dyn_cast<PointerType>(F.getArg(i)->getType()))
      {
        if (pt->getPointerElementType()->isStructTy())
        {
          StructType *st = dyn_cast<StructType>(pt->getPointerElementType());
          StructType *newSt =
              strucTyToStructTy.count(st) > 0 ? strucTyToStructTy[st] : st;
          // AttributeSet as = newAttrList.getParamAttributes(i);

          Align al = DL->getPrefTypeAlign(newSt);
          // as.getAlignment()
          B.addAlignmentAttr(al);
          newFunc->addAttributes(AttributeList::FirstArgIndex + i, B);

          // pal.removeParamAttributes(newFunc->getContext(), i);
          // pal.addParamAttributes(newFunc->getContext(), i, B);
        }
      }
    }
    // newFunc->addParamAttrs(i, B);
  }
  newFunc->addAttributes(AttributeList::ReturnIndex, pal.getRetAttributes());

  // newFunc->setAttributes(newAttrList);
  // newFunc->setAttributes(newAttrList);
  // for (int i = 0; i < F.arg_size(); i++){

  // }
  // const AttrBuilder newAttrBuilder;

  // for (int i = 0; i < newFunc->arg_size(); i++){
  //   newAttrList = newAttrList.addParamAttributes(newFunc->getContext(), i,
  //                                                newAttrBuilder);
  // }
  // const AttributeList resultAttrList = newAttrList;

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

Value *MPAvailable::createOffsetMask(IRBuilder<> &irb, Value *offset)
{
  Value *over = irb.CreateShl(offset, 32);
  Value *result = irb.CreateOr(over, offset);
  return result;
}

void MPAvailable::replaceStructTy(Module &M)
{
  int size = 0;
  int beforeSize = 0;

  for (StructType *st : M.getIdentifiedStructTypes())
  {
    createStructureType(st);
  }
  while (beforeSize != strucTyToStructTy.size())
  {
    beforeSize = strucTyToStructTy.size();
    for (StructType *st : M.getIdentifiedStructTypes())
    {
      createStructureType(st);
    }
  }
}

void MPAvailable::replaceStructTyInFunction(Function &F)
{
  // gep만 펼치기
  for (Instruction &I : instructions(F))
  {
    if (I.getOpcode() == Instruction::GetElementPtr)
    {
      IRBuilder<> irb(&I);
      GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(&I);
      gep_type_iterator GTI = gep_type_begin(gep);
      Value *base = gep->getPointerOperand()->stripPointerCasts();
      for (User::op_iterator i = gep->op_begin() + 1, e = gep->op_end(); i != e;
           ++i, ++GTI)
      {
        Value *Op = *i;

        base = irb.CreateGEP(GTI.getIndexedType(), base, Op);
        // valuePrint(base, "split gep ");
      }
      if (base != gep->getPointerOperand()->stripPointerCasts())
      {
        // typePrint(gep->getType(), "orig gep type");
        // typePrint(base->getType(), "replacing type");
        gep->replaceAllUsesWith(base);
        gep->eraseFromParent();
      }
    }
  }
}

Value *MPAvailable::cloneConstantExpr(ConstantExpr *cExpr, std::map<Value *, Value *> &valToVal)
{
  // store %struct.stackinfo* %102, %struct.stackinfo** bitcast (%struct.stackinfo.188** @PL_curstackinfo to %struct.stackinfo**), align 8
  //   %157 = load %struct.stackinfo*, %struct.stackinfo** bitcast (%struct.stackinfo.188** @PL_curstackinfo to %struct.stackinfo**), align 8
  // %new.cons3 = load i8*, i8** getelementptr inbounds ([3 x %struct.spec_fd_t], [3 x %struct.spec_fd_t]* @spec_fd, i64 0, i64 0, i32 3), align 8
  switch (cExpr->getOpcode())
  {
  case Instruction::BitCast:
  {
    if (valToVal.count(cExpr->getOperand(0)))
    {
      Value *operand = valToVal[cExpr->getOperand(0)];
      if (isXMMPtrTy(operand->getType()))
      {
        valToVal[cExpr] = operand;
        return operand;
      }
    }
    return ConstantExpr::getBitCast(cExpr->getOperand(0), cExpr->getType());
  }
  case Instruction::GetElementPtr:
  {
    GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(cExpr->getAsInstruction());

    if (valToVal.count(gep->getPointerOperand()))
    {
      //   makeArrayRef(gep->idx_begin(), gep->idx_end());
      ArrayRef<Use> arr = makeArrayRef(gep->idx_begin(), gep->idx_end());
      std::vector<Value *> param;
      for (Value *use : arr)
      {
        param.push_back(use);
      }
      return ConstantExpr::getInBoundsGetElementPtr(gep->getType(),
                                                    dyn_cast<Constant>(gep->getPointerOperand()),
                                                    param);
      // ConstantExpr::getInBoundsGetElementPtr()
    }
  }
  default:
    return cExpr;
  }
}
Value *MPAvailable::instrumentWithByteOfMalloc(IRBuilder<> &B, Instruction *I,
                                               std::map<Value *, Value *> &valToVal)
{
  // it is for only malloc and user allocation
  AllocationType CallType = getCallType(I);
  switch (CallType)
  {
  case Malloc:
    if (valToVal.count(I->getOperand(0)) > 0)
      return valToVal[I->getOperand(0)];
    return I->getOperand(0);
  case Calloc:
    CallInst *CS = dyn_cast<CallInst>(I);
    Value *NumElements = valToVal.count(CS->getArgOperand(0)) > 0
                             ? valToVal[CS->getArgOperand(0)]
                             : CS->getArgOperand(0);
    Value *ElementSize = valToVal.count(CS->getArgOperand(1)) > 0
                             ? valToVal[CS->getArgOperand(1)]
                             : CS->getArgOperand(1);
    return B.CreateMul(NumElements, ElementSize);
  }
  if (valToVal.count(I->getOperand(0)) > 0)
    return valToVal[I->getOperand(0)];
  return I->getOperand(0);
}
Value *
MPAvailable::instrumentWithByteSize(IRBuilder<> &B, Instruction *I,
                                    std::map<Value *, Value *> &valToVal)
{
  AllocationType CallType = getCallType(I);
  int SizeArg = getSizeArg(I);

  switch (CallType)
  {
  case Malloc:
  {
    CallInst *CS = dyn_cast<CallInst>(I);

    if (valToVal.count(CS->getArgOperand(SizeArg)) > 0)
      return valToVal[CS->getArgOperand(SizeArg)];
    return CS->getArgOperand(SizeArg);
  }
  case Realloc:
  {
    CallInst *CS = dyn_cast<CallInst>(I);
    if (valToVal.count(CS->getArgOperand(1)) > 0)
      return valToVal[CS->getArgOperand(1)];
    return CS->getArgOperand(1);
  }
  case Calloc:
  {
    CallInst *CS = dyn_cast<CallInst>(I);
    Value *NumElements = valToVal.count(CS->getArgOperand(0)) > 0
                             ? valToVal[CS->getArgOperand(0)]
                             : CS->getArgOperand(0);
    Value *ElementSize = valToVal.count(CS->getArgOperand(1)) > 0
                             ? valToVal[CS->getArgOperand(1)]
                             : CS->getArgOperand(1);
    return B.CreateMul(NumElements, ElementSize);
  }
  case Alloca:
  {
    AllocaInst *AI = cast<AllocaInst>(I);
    Value *Size = B.getInt64(DL->getTypeAllocSize(AI->getAllocatedType()));
    Value *arraySize = valToVal.count(AI->getArraySize()) > 0
                           ? valToVal[AI->getArraySize()]
                           : AI->getArraySize();
    if (AI->isArrayAllocation())
      Size = B.CreateMul(Size, arraySize);

    return Size;
  }
  case AllocaNone:
    return nullptr;
  default:
    return nullptr;
  }
  return nullptr; /* never reached */
}
bool MPAvailable::checkShouldBeWrapped(Function &F)
{
  for (int i = 0; i < F.arg_size(); i++)
  {
    Value *arg = F.getArg(i);
    if (arg->getType()->isPointerTy())
    {
      return true;
    }
  }
  if (F.getReturnType()->isPointerTy())
    return true;
  return false;
}
void MPAvailable::findDoublePtrMalloc(Function &F)
{
  bool isDoublePtrMalloc = false;
  for (Instruction &I : instructions(F))
  {
    if (isMalloc(&I))
    {
      CallInst *CI = dyn_cast<CallInst>(&I);
      if (CI->getNumUses() > 0)
      {
        for (Value *use : CI->users())
        {
          if (BitCastInst *bci = dyn_cast<BitCastInst>(use))
          {
            if (dyn_cast<PointerType>(bci->getType())
                    ->getElementType()
                    ->isPointerTy())
              isDoublePtrMalloc = true;
          }
        }
      }
      if (isDoublePtrMalloc)
      {
        IRBuilder<> irb(getInsertPointBefore(&I));
        Value *op = CI->getOperand(0);
        Value *newOp = irb.CreateMul(op, ConstantInt::get(op->getType(), 2));
        CI->setOperand(0, newOp);
      }
    }
  }
}

void MPAvailable::runOnStructInstrument(Module &M)
{
  // 이 작업 때문에 memset, memcpy에 들어가는 함수도 무시하게 됨
  // 일단 넘어가자...
  for (StructType *st : M.getIdentifiedStructTypes())
  {
    if (st->getName().find("anon") != StringRef::npos)
      externStructs.insert(st);
  }
  for (Function &F : M)
  {
    if (F.isDeclaration())
    {
      FunctionType *funcType = F.getFunctionType();
      for (Type *type : funcType->params())
      {
        if (type->isPointerTy())
        {
          PointerType *pt = dyn_cast<PointerType>(type);
          if (pt->getElementType()->isStructTy())
          {
            StructType *st = dyn_cast<StructType>(pt->getElementType());
            // typePrint(st, "Extern Struct:");
            externStructs.insert(st);
          }
        }
        if (type->isStructTy())
        {
          StructType *st = dyn_cast<StructType>(type);
          // typePrint(st, "Extern Struct:");
          externStructs.insert(st);
        }
      }
    }
  }
  bool changed = true;
  while (changed)
  {
    int before = externStructs.size();
    for (StructType *st : externStructs)
    {
      for (Type *type : st->elements())
      {
        if (type->isPointerTy())
        {
          PointerType *pt = dyn_cast<PointerType>(type);
          if (pt->getElementType()->isStructTy())
          {
            StructType *st = dyn_cast<StructType>(pt->getElementType());
            externStructs.insert(st);
          }
        }
        if (type->isStructTy())
        {
          StructType *addingST = dyn_cast<StructType>(type);
          externStructs.insert(addingST);
        }
      }
    }
    changed = before != externStructs.size();
  }

  /* debug code
  errs() << "size: " << externStructs.size() << "\n";
  for (Type *type : externStructs) {
    typePrint(type, "inserting set ");
  } */
}
bool MPAvailable::isExternStruct(Type *type)
{
  if (type->isStructTy())
  {
    StructType *st = dyn_cast<StructType>(type);
    if (externStructs.count(st) > 0)
      return true;
  }
  return false;
}

bool MPAvailable::fixParamAllocInst(Instruction &I,
                                    std::map<Value *, Value *> &valToVal,
                                    IRBuilder<> &irb, bool isNeededNewInst)
{
  if (CallInst *ci = dyn_cast<CallInst>(&I))
  {
    if (isMalloc(&I) || isCalloc(&I) || isUserAllocation(ci->getCalledFunction()))
    {
      for (User *use : ci->users())
      {
        if (BitCastInst *bci = dyn_cast<BitCastInst>(use))
        {
          if (dyn_cast<PointerType>(bci->getDestTy())
                  ->getPointerElementType()
                  ->isStructTy())
          {
            // instPrint(bci, "bci");
            StructType *st =
                dyn_cast<StructType>(dyn_cast<PointerType>(bci->getDestTy())
                                         ->getPointerElementType());

            if (strucTyToStructTy.count(st) > 0)
            {
              // errs() << " New Struct!!\n";
              Value *op = isCalloc(&I) ? ci->getOperand(1) : ci->getOperand(0);
              Value *newParam;
              if (ConstantInt *cons = dyn_cast<ConstantInt>(op))
              {
                APInt intOp = cons->getValue();
                unsigned int arrayIntSize = this->DL->getTypeAllocSize(st);
                int index = intOp.getZExtValue() / arrayIntSize;
                unsigned int convertSize =
                    this->DL->getTypeAllocSize(strucTyToStructTy[st]);
                unsigned int newOp;
                newOp = isCalloc(&I) ? convertSize : convertSize * index;
                newParam = GETCONSTANTINT(
                    op->getContext(),
                    op->getType()->getIntegerBitWidth(), newOp);
              }
              else
              {
                op = valToVal.count(op) > 0 ? valToVal[op] : op;
                unsigned int arrayIntSize = this->DL->getTypeAllocSize(st);
                Value *div = GETCONSTANTINT(
                    op->getContext(),
                    op->getType()->getIntegerBitWidth(),
                    arrayIntSize);
                unsigned int newTypeSize =
                    this->DL->getTypeAllocSize(strucTyToStructTy[st]);
                Value *mul = irb.CreateUDiv(op, div);
                Value *newStSize = GETCONSTANTINT(
                    op->getContext(),
                    op->getType()->getIntegerBitWidth(),
                    newTypeSize);
                ConstantInt *ciTemp = dyn_cast<ConstantInt>(newStSize);
                if (isCalloc(&I))
                  newParam = GETCONSTANTINT(op->getContext(), op->getType()->getIntegerBitWidth(), newTypeSize);
                else
                {
                  newParam = irb.CreateMul(
                      mul, newStSize,
                      "ciTemp." + ciTemp->getValue().toString(10, true) + "." +
                          strucTyToStructTy[st]->getStructName());
                }
              }
              if (isNeededNewInst)
              {
                std::vector<Value *> params;
                if (isCalloc(&I))
                {
                  Value *op0 = ci->getOperand(0);
                  op0 = valToVal.count(op0) ? valToVal[op0] : op0;
                  params.push_back(op0);
                }
                params.push_back(newParam);
                // typePrint(ci->getCalledFunction()->getType(), "ci");
                Value *newCall =
                    irb.CreateCall(ci->getCalledFunction(), params);
                valToVal[ci] = newCall;
                return true;
              }
              else
              {
                if (isCalloc(&I))
                {
                  Value *op0 = ci->getOperand(0);
                  op0 = valToVal.count(op0) ? valToVal[op0] : op0;
                  ci->setArgOperand(0, op0);
                  ci->setArgOperand(1, newParam);
                }
                else
                  ci->setArgOperand(0, newParam);
              }
            }
          }
          else if (dyn_cast<PointerType>(bci->getDestTy())
                       ->getPointerElementType()
                       ->isPointerTy())
          {
            Value *op = isCalloc(&I) ? ci->getOperand(1) : ci->getOperand(0);
            op = valToVal.count(op) > 0 ? valToVal[op] : op;
            if (op->getType()->getIntegerBitWidth() != 64)
              op = irb.CreateZExt(op, irb.getInt64Ty());
            Value *mul = GETCONSTANTINT(op->getContext(), 64, 2);
            Value *newParam = irb.CreateMul(op, mul);
            if (ci->getArgOperand(0)->getType()->getIntegerBitWidth() !=
                newParam->getType()->getIntegerBitWidth())
            {
              newParam = irb.CreateZExtOrTrunc(newParam,
                                               ci->getArgOperand(0)->getType());
            }
            if (isNeededNewInst)
            {
              std::vector<Value *> params;
              if (isCalloc(&I))
              {
                Value *op0 = ci->getOperand(0);
                op0 = valToVal.count(op0) ? valToVal[op0] : op0;
                params.push_back(op0);
              }
              params.push_back(newParam);
              Value *newCall = irb.CreateCall(ci->getCalledFunction(), params);
              valToVal[ci] = newCall;
              return true;
            }
            else
            {
              if (isCalloc(&I))
              {
                Value *op0 = ci->getOperand(0);
                op0 = valToVal.count(op0) ? valToVal[op0] : op0;
                ci->setArgOperand(0, op0);
                ci->setArgOperand(1, newParam);
              }
              else
                ci->setArgOperand(0, newParam);
            }
          }
        }
      }
    }
  }
  return false;
}

bool MPAvailable::fixGEPforStruct(GetElementPtrInst *gep,
                                  std::map<Value *, Value *> &valToVal,
                                  IRBuilder<> &irb, bool needReplace)
{
  // 오직 struct 구조가 바뀌는 경우에 한해서만 하자
  // 카피가 필요하면 transformation 함수에서 해줄 것

  Value *pointer = gep->getPointerOperand();
  Type *pointerType = gep->getSourceElementType();
  Type *gepType = gep->getResultElementType();

  // if (pointerType == gepType)
  //   return false; //포인터, 배열 접근

  // typePrint(pointerType, "gep pointer type");
  if (pointerType->isStructTy())
  {
    StructType *pointerSt = dyn_cast<StructType>(pointerType);
    if (strucTyToStructTy.count(pointerSt) > 0)
    {
      Value *newGEP;
      std::vector<Value *> plist;
      Value *newPtr = valToVal.count(pointer) > 0 ? valToVal[pointer] : pointer;

      if (isXMMTy(newPtr->getType()))
      {
        // unwrapping 해주면 됨
        // 배열이거나, 링크드 리스트 이거나
        if (gep->getNumIndices() < 2)
          return false;
        Value *index1 = gep->getOperand(1);
        Value *index2 = gep->getOperand(2);

        ConstantInt *consIndex2 = dyn_cast_or_null<ConstantInt>(index2);
        if (consIndex2 == nullptr)
          return false;

        if (index1->getType()->getIntegerBitWidth() != 64)
          index1 = irb.CreateZExtOrBitCast(index1, irb.getInt64Ty());
        index1 = irb.CreateMul(index1, irb.getInt64(16));

        StructType *st =
            dyn_cast<StructType>(pointer->getType()->getPointerElementType());
        st = strucTyToStructTy[st];
        uint64_t size = DL->getStructLayout(st)->getElementOffset(
            consIndex2->getZExtValue());

        Value *offset = irb.CreateAdd(index1, irb.getInt64(size));
        Constant *nullVec = Constant::getNullValue(XMM);
        Value *tag = createOffsetMask(irb, offset);
        Value *v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
        Value *v1 = irb.CreateInsertElement(v0, offset, 1);

        llvm::StringRef name = gep->hasName() ? gep->getName() : "fix";
        Value *replaceInst = irb.CreateAdd(newPtr, v1, name);
        // newPtr = ununTag(newPtr, pointer->getType(), irb);
        valToVal[gep] = replaceInst;
        return true;
      }
      // 그게 아닐 경우에 대해서만 하기 밑처럼 처리하면 됨
      for (auto i = gep->idx_begin(); i != gep->idx_end(); i++)
      {
        Value *val = *i;
        if (valToVal.count(val) > 0)
        {
          plist.push_back(valToVal[val]);
        }
        else
        {
          // valuePrint(val, "val");
          plist.push_back(val);
        }
      }
      if (gep->isInBounds())
      {
        newGEP = irb.CreateInBoundsGEP(newPtr, plist, "fix");
      }
      else
      {
        newGEP = irb.CreateGEP(newPtr, plist);
      }
      valToVal[gep] = newGEP;
      // if (needReplace) willBeRemoveSet.insert(gep);
      return true;
    }
  }
  return false;
}

Value *MPAvailable::splatGEP(GetElementPtrInst *gep,
                             std::map<Value *, Value *> &valToVal,
                             IRBuilder<> &irb)
{
  Value *offset = emitGEPOffset(irb, *DL, gep, valToVal);
  Value *basePointer = valToVal[gep->getPointerOperand()];

  // 더블포인터면 offset 을 두배 해주기
  PointerType *pt = dyn_cast<PointerType>(gep->getPointerOperandType());
  if (pt->getPointerElementType()->isPointerTy())
  {
    Constant *two = ConstantInt::get(irb.getInt64Ty(), 2);
    offset = irb.CreateMul(offset, two, "twoX");
  }

  Constant *nullVec = Constant::getNullValue(XMM);
  Value *tag = createOffsetMask(irb, offset);
  Value *v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
  Value *v1 = irb.CreateInsertElement(v0, offset, 1);
  std::string name = "";
  if (gep->hasName())
    name.append(gep->getName());
  else
    name.append("SPLAT");

  if (ConstantInt *cons = dyn_cast_or_null<ConstantInt>(offset))
  {
    APInt val = cons->getUniqueInteger();
    std::string valToString = val.toString(10, false);
    name.append("." + valToString);
  }
  Value *replaceInst = irb.CreateAdd(basePointer, v1, name);
  return replaceInst;
}
Value *MPAvailable::splatGEP2(GetElementPtrInst *gep,
                              std::map<Value *, Value *> &valToVal,
                              IRBuilder<> &irb)
{
  Value *offset = emitGEPOffset(irb, *DL, gep, valToVal);

  Constant *nullVec = Constant::getNullValue(XMM);
  Value *tag = createOffsetMask(irb, offset);
  Value *v0 = irb.CreateInsertElement(nullVec, tag, (uint64_t)0);
  Value *v1 = irb.CreateInsertElement(v0, offset, 1);

  Value *replaceInst = irb.CreateAdd(gep->getPointerOperand(), v1, "SPLATGEP");
  return replaceInst;
  // valToVal[dyn_cast<Value>(gep)] = replaceInst;
}

void MPAvailable::verifyGlobalValue(Module &M)
{
  errs() << "Verify Global Value \n";
  for (GlobalVariable &GV : M.getGlobalList())
  {
    if (gToGV.count(&GV) > 0)
    {
      valuePrint(&GV, "original global");
      valuePrint(gToGV[&GV], "new global");
    }
    else
    {
      if (GV.isConstant())
        continue;
      valuePrint(&GV, "============GV========");
      // if(isa<Constant>(&GV)) continue;
      if (!GV.getName().equals("spec_fd"))
        continue;
      for (Value *user : GV.materialized_users())
      {
        errs() << "cExpr:: \n";
        if (ConstantExpr *cExpr = dyn_cast<ConstantExpr>(user))
        {
          if (cExpr->isConstantUsed())
            errs() << "Use\n";
          else
            errs() << "No Use!!\n";
        }
        // valuePrint(user, "GV->user");
        // errs() <<"function: ";
        // errs() << dyn_cast<Instruction>(user)->getFunction()->getName()<< "\n";
        // errs() <<"Parent : " ;
        // errs() << dyn_cast<Instruction>(user)->getParent()->getParent()->getName() <<"\n";
      }
      errs() << "end\n";
    }
  }
}

FunctionType *MPAvailable::createFunctionType(FunctionType *ft)
{
  std::vector<Type *> plist;
  for (unsigned int i = 0; i < ft->getNumParams(); i++)
  {
    Type *type = ft->getParamType(i);
    if (isFunctionPtrTy(type))
    {
      FunctionType *elementFt =
          dyn_cast<FunctionType>(type->getPointerElementType());
      // typePrint(type, "type");
      Type *newType = createFunctionType(elementFt);
      plist.push_back(newType->getPointerTo());
    }
    else if (type->isPointerTy())
    {
      Type *newType = createNewPointerType(type);
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
  Type *returnType;
  if (ft->getReturnType()->isPointerTy())
    returnType = XMM;
  else
    returnType = ft->getReturnType();
  return FunctionType::get(returnType, plist, ft->isVarArg());
}
std::vector<Value *>
MPAvailable::getCallArgs(CallInst *CI, FunctionType *ft,
                         std::map<Value *, Value *> &valToVal,
                         IRBuilder<> &irb)
{
  std::vector<Value *> plist;
  Value *calledFunc = CI->getCalledOperand();
  // typePrint(calledFunc->getType(), "calledFunc");

  for (unsigned int i = 0; i < CI->arg_size(); i++)
  {
    Type *argType = ft->getParamType(i);
    Value *arg = CI->getArgOperand(i);
    // 일단 타입별로
    //
    //
    if (isFunctionPtrTy(arg->getType()))
    {
      Value *newArg = valToVal.count(arg) ? valToVal[arg] : arg;
      // valuePrint(newArg, "newArg");
      plist.push_back(newArg);
    }
    else if (arg->getType()->isPointerTy())
    {
      if (valToVal.count(arg) > 0)
      {
        Value *newArg = valToVal[arg];
        if (isXMMTy(newArg->getType()))
        {
          Value *ptr = irb.CreateExtractElement(newArg, (uint64_t)1);
          Value *tag = irb.CreateExtractElement(newArg, (uint64_t)0);
          plist.push_back(tag);
          plist.push_back(ptr);
        }
        else
        {
          // constant null 채워서 주기
          Value *ptr = newArg->getType()->isPointerTy()
                           ? irb.CreatePtrToInt(newArg, irb.getInt64Ty())
                           : irb.CreateBitCast(newArg, irb.getInt64Ty());
          Value *tag = ConstantInt::get(irb.getInt64Ty(), 0);
          plist.push_back(tag);
          plist.push_back(ptr);
        }
      }
      else
      {
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
    }
    else
    {
      if (valToVal.count(arg) > 0)
      {
        plist.push_back(valToVal[arg]);
      }
      else
      {
        plist.push_back(arg);
        // 그냥 arg 넣어주기
        // 거의 왠만하면 constant 일듯
      }
    }
  }
  return plist;
}
void MPAvailable::valuePrintGenerate(Value *val, IRBuilder<> &irb, bool isPointer)
{
  static bool init = false;
  static GlobalVariable *gvar_ptr_abc;
  static GlobalVariable *pointer;
  static GlobalVariable *value;
  Module &M = *this->module;

  if (!init)
  {
    init = true;

    Constant *pointerString;
    Constant *valueString;

    pointerString = ConstantDataArray::getString(M.getContext(), "ADDRPRINT pointer: %p \n");
    valueString = ConstantDataArray::getString(M.getContext(), "ADDRPRINT value: %p \n");
    Module &M = *this->module;
    pointer = new GlobalVariable(
        /*Module=*/M,
        /*Type=*/pointerString->getType(),
        /*isConstant=*/true,
        /*Linkage=*/GlobalValue::PrivateLinkage,
        /*Initializer=*/pointerString, // has initializer,
                                       // specified below
        /*Name=*/"pointer_print");
    pointer->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);

    value = new GlobalVariable(
        /*Module=*/M,
        /*Type=*/valueString->getType(),
        /*isConstant=*/true,
        /*Linkage=*/GlobalValue::PrivateLinkage,
        /*Initializer=*/valueString, // has initializer,
                                     // specified below
        /*Name=*/"value_print");
    value->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
  }
  std::vector<Value *> cExprPlist;

  cExprPlist.push_back(ConstantInt::get(Type::getInt64Ty(M.getContext()), 0));
  cExprPlist.push_back(ConstantInt::get(Type::getInt64Ty(M.getContext()), 0));
  // typePrint(gvar_ptr_abc->getType(), "type");
  // valuePrint(gvar_ptr_abc, "gvar_ptr_abc");
  Value *arg;
  if (isPointer)
    arg = ConstantExpr::getInBoundsGetElementPtr(
        pointer->getValueType(), pointer, cExprPlist);
  else
    arg = ConstantExpr::getInBoundsGetElementPtr(
        value->getValueType(), value, cExprPlist);
  std::vector<Value *> calleeList;
  calleeList.push_back(arg);
  calleeList.push_back(val);

  irb.CreateCall(printFunction, calleeList);
}

Type *MPAvailable::createNewPointerType(Type *type)
{
  if (!type->isPointerTy())
    return type;
  PointerType *ptype = dyn_cast<PointerType>(type);
  Type *elementType = ptype->getPointerElementType();

  if (elementType->isPointerTy())
  {
    return createNewPointerType(elementType)->getPointerTo();
  }
  else
  {
    if (elementType->isStructTy())
    {
      StructType *st = dyn_cast<StructType>(elementType);
      Type *newType = strucTyToStructTy.count(st) > 0
                          ? strucTyToStructTy[st]->getPointerTo()
                          : elementType->getPointerTo();
      return newType;
    }
    else
    {
      return elementType->getPointerTo();
    }
  }
}
StructType *MPAvailable::findStruct(StructType *st)
{
  for (StructType *mSt : module->getIdentifiedStructTypes())
  {
    if (mSt->isOpaque() || mSt->isLiteral())
      return st;
    if (mSt->isLayoutIdentical(st))
      return mSt;
  }
  return st;
}
void MPAvailable::removeConstantExpr(Module &M)
{
  std::set<ConstantExpr *> destroySet;
  for (Function &F : M)
  {
    // errs() << "======" << F.getName() << "=======\n";
    for (Instruction &I : instructions(F))
    {
      switch (I.getOpcode())
      {
      case Instruction::Load:
      case Instruction::Store:
        for (int i = 0; i < I.getNumOperands(); i++)
        {
          Value *op = I.getOperand(i);
          if (ConstantExpr *cExpr = dyn_cast<ConstantExpr>(op))
          {

            // instPrint(&I, "orig");

            Instruction *newInst = getAsInstruction(cExpr, &I);
            //      instPrint(newInst, "newInst");
            I.setOperand(i, newInst);
            destroySet.insert(cExpr);
            //    instPrint(&I, "set operand");
          }
        }
        break;
      default:
        break;
      }
    }
  }
  for (ConstantExpr *cExpr : destroySet)
  {
    cExpr->destroyConstant();
  }
}

void MPAvailable::removeUserAlloc(Module &M)
{
  for (Function &F : M)
  {
  }
}
Value *MPAvailable::createXmmValue(IRBuilder<> &irb, Value *value)
{
  Value *newValue;
  Constant *nullVec = Constant::getNullValue(XMM);
  Constant *nullValue =
      Constant::getNullValue(irb.getInt64Ty());
  Value *vec1 =
      irb.CreateInsertElement(nullVec, nullValue, uint64_t(0));

  if (value->getType()->isPointerTy())
  {
    Value *ptrToInt = irb.CreatePtrToInt(value, irb.getInt64Ty());
    newValue = irb.CreateInsertElement(vec1, ptrToInt, uint64_t(1));
  }
  else if (value->getType()->isIntegerTy())
  {
    Value *castVal = value;
    if (!value->getType()->getPrimitiveSizeInBits() == 64)
      castVal = irb.CreateZExtOrBitCast(value, irb.getInt64Ty());
    newValue = irb.CreateInsertElement(vec1, castVal, uint64_t(1));
  }
  return newValue;
}
void MPAvailable::removeGlobalValue(Module &M)
{
  for (detail::DenseMapPair<GlobalVariable *, GlobalVariable *> gPair : gToGV)
  {
    Value *key = gPair.first;
    if (arrOfGlobalVal.count(key) > 0)
      continue;
    valuePrint(key, "global value removing : ");

    gPair.first->replaceAllUsesWith(UndefValue::get(gPair.first->getType()));
    Constant *cons;
    if (gPair.first->hasInitializer())
    {
      cons = gPair.first->getInitializer();
    }
    gPair.first->eraseFromParent();
    // cons->destroyConstant();
    // cons->hasOneUse
    if (cons)
    {
      if (!cons->isNullValue())
        cons->destroyConstant();
    }
  }
  for (GlobalVariable *GV : removeGlobals)
  {
    GV->replaceAllUsesWith(UndefValue::get(GV->getType()));

    Constant *cons;
    if (GV->hasInitializer())
    {
      cons = GV->getInitializer();
    }
    GV->eraseFromParent();
    // cons->destroyConstant();
    // cons->hasOneUse
    if (cons)
    {
      if (!cons->isNullValue())
        cons->destroyConstant();
    }
  }
}

bool MPAvailable::isGlobalConstant(Value *op)
{
  //  valuePrint(op, "isGlobalConstant");
  if (ConstantExpr *cExpr = dyn_cast<ConstantExpr>(op))
  {
    Value *pointer;
    if (cExpr->getOpcode() == Instruction::GetElementPtr)
    {
      pointer = cExpr->getOperand(0);
    }
    else if (cExpr->getOpcode() == Instruction::BitCast)
    {
      pointer = cExpr->getOperand(0);
    }
    else
      return false;
    if (pointer)
    {
      // valuePrint(pointer, "pointer");
      if (GlobalVariable *gv = dyn_cast<GlobalVariable>(pointer))
      {
        if (gv->isConstant())
          return true;
      }
    }
  }
  return false;
}

void MPAvailable::checkConstValue(Module &M)
{
  // 저장이 글로벌 변수에만 되야되고 스토어가 한 번만 이루어져야 함
  errs() << "check const value\n";

  for (Function &F : M)
  {
    for (Instruction &I : instructions(&F))
    {
      switch (I.getOpcode())
      {
      case Instruction::Alloca:
      {
        AllocaInst *AI = dyn_cast<AllocaInst>(&I);
        if (AI->getAllocatedType()->isArrayTy())
        {
          std::set<Value *> aliases;
          bool isConst = false;
          for (Value *user : AI->users())
          {
            aliases.insert(user);
          }
          unsigned int storeCount = 0;
          for (Value *alias : aliases)
          {
            for (User *user : alias->users())
            {
              if (StoreInst *si = dyn_cast<StoreInst>(user))
              {
                storeCount++;
                if (isGlobalConstant(si->getValueOperand()))
                {
                  isConst = true;
                }
              }
              else if (MemCpyInst *mcy = dyn_cast<MemCpyInst>(user))
              {
                storeCount++;
                if (isGlobalConstant(mcy->getArgOperand(1)))
                {
                  isConst = true;
                }
              }
              else if (Instruction *inst = dyn_cast<Instruction>(user))
              {
                if (inst->mayWriteToMemory())
                {
                  storeCount++;
                }
              }
            }
          }
          if (storeCount == 1 && isConst)
          {
            ArrayType *allocType = dyn_cast<ArrayType>(AI->getAllocatedType());
            if (allocType->getArrayElementType()->isPointerTy())
            {
              instPrint(&I, "const value");
              constVariables.insert(&I);
            }
          }
        }
        break;
      }
      default:
        break;
      }
    }
  }
}
void MPAvailable::makeConstAliasList()
{
  for (Value *val : constVariables)
  {
    for (User *use : val->users())
    {
      if (Instruction *inst = dyn_cast<Instruction>(use))
      {
        instPrint(inst, "const alias");
        constAliases.insert(inst);
      }
    }
  }
}

static RegisterPass<MPAvailable> MPAVAILABLE("mpav", "MPAvailable");
