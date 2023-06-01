//===- llvm/unittest/IR/AsmWriter.cpp - AsmWriter tests -------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
#include "llvm/BinaryFormat/Dwarf.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Module.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

using namespace llvm;
using ::testing::HasSubstr;

namespace {

TEST(AsmWriterTest, DebugPrintDetachedInstruction) {

  // PR24852: Ensure that an instruction can be printed even when it
  // has metadata attached but no parent.
  LLVMContext Ctx;
  auto Ty = Type::getInt32Ty(Ctx);
  auto Poison = PoisonValue::get(Ty);
  std::unique_ptr<BinaryOperator> Add(BinaryOperator::CreateAdd(Poison, Poison));
  Add->setMetadata(
      "", MDNode::get(Ctx, {ConstantAsMetadata::get(ConstantInt::get(Ty, 1))}));
  std::string S;
  raw_string_ostream OS(S);
  Add->print(OS);
  EXPECT_THAT(OS.str(),
              HasSubstr("<badref> = add i32 poison, poison, !<empty"));
}

TEST(AsmWriterTest, DebugPrintDetachedArgument) {
  LLVMContext Ctx;
  auto Ty = Type::getInt32Ty(Ctx);
  auto Arg = new Argument(Ty);

  std::string S;
  raw_string_ostream OS(S);
  Arg->print(OS);
  EXPECT_EQ(S, "i32 <badref>");
  delete Arg;
}

TEST(AsmWriterTest, DumpDIExpression) {
  LLVMContext Ctx;
  uint64_t Ops[] = {
    dwarf::DW_OP_constu, 4,
    dwarf::DW_OP_minus,
    dwarf::DW_OP_deref,
  };
  DIExpression *Expr = DIExpression::get(Ctx, Ops);
  std::string S;
  raw_string_ostream OS(S);
  Expr->print(OS);
  EXPECT_EQ("!DIExpression(DW_OP_constu, 4, DW_OP_minus, DW_OP_deref)",
            OS.str());
}

TEST(AsmWriterTest, PrintAddrspaceWithNullOperand) {
  LLVMContext Ctx;
  Module M("test module", Ctx);
  SmallVector<Type *, 3> FArgTypes;
  FArgTypes.push_back(Type::getInt64Ty(Ctx));
  FunctionType *FTy = FunctionType::get(Type::getVoidTy(Ctx), FArgTypes, false);
  Function *F = Function::Create(FTy, Function::ExternalLinkage, "", &M);
  Argument *Arg0 = F->getArg(0);
  Value *Args[] = {Arg0};
  std::unique_ptr<CallInst> Call(CallInst::Create(F, Args));
  // This will make Call's operand null.
  Call->dropAllReferences();

  std::string S;
  raw_string_ostream OS(S);
  Call->print(OS);
  EXPECT_THAT(OS.str(), HasSubstr("<cannot get addrspace!>"));
}

TEST(AsmWriterTest, PrintNullOperandBundle) {
  LLVMContext C;
  Type *Int32Ty = Type::getInt32Ty(C);
  FunctionType *FnTy = FunctionType::get(Int32Ty, Int32Ty, /*isVarArg=*/false);
  Value *Callee = Constant::getNullValue(PointerType::getUnqual(C));
  Value *Args[] = {ConstantInt::get(Int32Ty, 42)};
  std::unique_ptr<BasicBlock> NormalDest(BasicBlock::Create(C));
  std::unique_ptr<BasicBlock> UnwindDest(BasicBlock::Create(C));
  OperandBundleDef Bundle("bundle", UndefValue::get(Int32Ty));
  std::unique_ptr<InvokeInst> Invoke(
      InvokeInst::Create(FnTy, Callee, NormalDest.get(), UnwindDest.get(), Args,
                         Bundle, "result"));
  // Makes the operand bundle null.
  Invoke->dropAllReferences();
  Invoke->setNormalDest(NormalDest.get());
  Invoke->setUnwindDest(UnwindDest.get());

  std::string S;
  raw_string_ostream OS(S);
  Invoke->print(OS);
  EXPECT_THAT(OS.str(), HasSubstr("<null operand bundle!>"));
}

class DIExprAsmWriterTest : public testing::Test {
public:
  DIExprAsmWriterTest() : Builder(Context), OS(S) {}

protected:
  LLVMContext Context;
  Type *Int32Ty = Type::getInt32Ty(Context);
  Type *Int64Ty = Type::getInt64Ty(Context);
  DIExprBuilder Builder;
  std::string S;
  raw_string_ostream OS;
};

TEST_F(DIExprAsmWriterTest, Empty) {
  DIExpr *Expr = Builder.intoExpr();
  Expr->print(OS);
  EXPECT_EQ("!DIExpr()", OS.str());
}

TEST_F(DIExprAsmWriterTest, Referrer) {
  Builder.append<DIOp::Referrer>(Int64Ty).intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpReferrer(i64))", OS.str());
}

TEST_F(DIExprAsmWriterTest, Arg) {
  Builder.append<DIOp::Arg>(1, Int64Ty).intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpArg(1, i64))", OS.str());
}

TEST_F(DIExprAsmWriterTest, TypeObject) {
  Builder.append<DIOp::TypeObject>(Int64Ty).intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpTypeObject(i64))", OS.str());
}

TEST_F(DIExprAsmWriterTest, Constant) {
  Builder
      .append<DIOp::Constant>(
          static_cast<ConstantData *>(ConstantInt::get(Int32Ty, 1)))
      .intoExpr()
      ->print(OS);
  EXPECT_EQ("!DIExpr(DIOpConstant(i32 1))", OS.str());
}

TEST_F(DIExprAsmWriterTest, Convert) {
  Builder.append<DIOp::Convert>(Int64Ty).intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpConvert(i64))", OS.str());
}

TEST_F(DIExprAsmWriterTest, Reinterpret) {
  Builder.append<DIOp::Reinterpret>(Int64Ty).intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpReinterpret(i64))", OS.str());
}

TEST_F(DIExprAsmWriterTest, BitOffset) {
  Builder.append<DIOp::BitOffset>(Int64Ty).intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpBitOffset(i64))", OS.str());
}

TEST_F(DIExprAsmWriterTest, ByteOffset) {
  Builder.append<DIOp::ByteOffset>(Int64Ty).intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpByteOffset(i64))", OS.str());
}

TEST_F(DIExprAsmWriterTest, Composite) {
  Builder.append<DIOp::Composite>(2, Int64Ty).intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpComposite(2, i64))", OS.str());
}

TEST_F(DIExprAsmWriterTest, Extend) {
  Builder.append<DIOp::Extend>(2).intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpExtend(2))", OS.str());
}

TEST_F(DIExprAsmWriterTest, Select) {
  Builder.append<DIOp::Select>().intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpSelect())", OS.str());
}

TEST_F(DIExprAsmWriterTest, AddrOf) {
  Builder.append<DIOp::AddrOf>(5).intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpAddrOf(5))", OS.str());
}

TEST_F(DIExprAsmWriterTest, Deref) {
  Builder.append<DIOp::Deref>(Int64Ty).intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpDeref(i64))", OS.str());
}

TEST_F(DIExprAsmWriterTest, Read) {
  Builder.append<DIOp::Read>().intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpRead())", OS.str());
}

TEST_F(DIExprAsmWriterTest, Add) {
  Builder.append<DIOp::Add>().intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpAdd())", OS.str());
}

TEST_F(DIExprAsmWriterTest, Sub) {
  Builder.append<DIOp::Sub>().intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpSub())", OS.str());
}

TEST_F(DIExprAsmWriterTest, Mul) {
  Builder.append<DIOp::Mul>().intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpMul())", OS.str());
}

TEST_F(DIExprAsmWriterTest, Div) {
  Builder.append<DIOp::Div>().intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpDiv())", OS.str());
}

TEST_F(DIExprAsmWriterTest, Shr) {
  Builder.append<DIOp::Shr>().intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpShr())", OS.str());
}

TEST_F(DIExprAsmWriterTest, Shl) {
  Builder.append<DIOp::Shl>().intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpShl())", OS.str());
}

TEST_F(DIExprAsmWriterTest, PushLane) {
  Builder.append<DIOp::PushLane>(Int64Ty).intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpPushLane(i64))", OS.str());
}

TEST_F(DIExprAsmWriterTest, MultipleOps) {
  Builder.insert(Builder.begin(),
                 {DIOp::Variant{std::in_place_type<DIOp::Referrer>, Int32Ty},
                  DIOp::Variant{std::in_place_type<DIOp::Referrer>, Int64Ty},
                  DIOp::Variant{std::in_place_type<DIOp::Add>}});
  Builder.intoExpr()->print(OS);
  EXPECT_EQ("!DIExpr(DIOpReferrer(i32), DIOpReferrer(i64), DIOpAdd())",
            OS.str());
}
}
