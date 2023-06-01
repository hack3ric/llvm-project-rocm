//===- llvm/unittest/AsmParser/AsmParserTest.cpp - asm parser unittests ---===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/StringRef.h"
#include "llvm/AsmParser/Parser.h"
#include "llvm/AsmParser/SlotMapping.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/SourceMgr.h"
#include "gtest/gtest.h"

using namespace llvm;

namespace {

TEST(AsmParserTest, NullTerminatedInput) {
  LLVMContext Ctx;
  StringRef Source = "; Empty module \n";
  SMDiagnostic Error;
  auto Mod = parseAssemblyString(Source, Error, Ctx);

  EXPECT_TRUE(Mod != nullptr);
  EXPECT_TRUE(Error.getMessage().empty());
}

#ifdef GTEST_HAS_DEATH_TEST
#ifndef NDEBUG

TEST(AsmParserTest, NonNullTerminatedInput) {
  LLVMContext Ctx;
  StringRef Source = "; Empty module \n\1\2";
  SMDiagnostic Error;
  std::unique_ptr<Module> Mod;
  EXPECT_DEATH(Mod = parseAssemblyString(Source.substr(0, Source.size() - 2),
                                         Error, Ctx),
               "Buffer is not null terminated!");
}

#endif
#endif

TEST(AsmParserTest, SlotMappingTest) {
  LLVMContext Ctx;
  StringRef Source = "@0 = global i32 0\n !0 = !{}\n !42 = !{i32 42}";
  SMDiagnostic Error;
  SlotMapping Mapping;
  auto Mod = parseAssemblyString(Source, Error, Ctx, &Mapping);

  EXPECT_TRUE(Mod != nullptr);
  EXPECT_TRUE(Error.getMessage().empty());

  ASSERT_EQ(Mapping.GlobalValues.size(), 1u);
  EXPECT_TRUE(isa<GlobalVariable>(Mapping.GlobalValues[0]));

  EXPECT_EQ(Mapping.MetadataNodes.size(), 2u);
  EXPECT_EQ(Mapping.MetadataNodes.count(0), 1u);
  EXPECT_EQ(Mapping.MetadataNodes.count(42), 1u);
  EXPECT_EQ(Mapping.MetadataNodes.count(1), 0u);
}

TEST(AsmParserTest, TypeAndConstantValueParsing) {
  LLVMContext Ctx;
  SMDiagnostic Error;
  StringRef Source = "define void @test() {\n  entry:\n  ret void\n}";
  auto Mod = parseAssemblyString(Source, Error, Ctx);
  ASSERT_TRUE(Mod != nullptr);
  auto &M = *Mod;

  const Value *V;
  V = parseConstantValue("double 3.5", Error, M);
  ASSERT_TRUE(V);
  EXPECT_TRUE(V->getType()->isDoubleTy());
  ASSERT_TRUE(isa<ConstantFP>(V));
  EXPECT_TRUE(cast<ConstantFP>(V)->isExactlyValue(3.5));

  V = parseConstantValue("i32 42", Error, M);
  ASSERT_TRUE(V);
  EXPECT_TRUE(V->getType()->isIntegerTy());
  ASSERT_TRUE(isa<ConstantInt>(V));
  EXPECT_TRUE(cast<ConstantInt>(V)->equalsInt(42));

  V = parseConstantValue("<4 x i32> <i32 0, i32 1, i32 2, i32 3>", Error, M);
  ASSERT_TRUE(V);
  EXPECT_TRUE(V->getType()->isVectorTy());
  ASSERT_TRUE(isa<ConstantDataVector>(V));

  V = parseConstantValue("i32 add (i32 1, i32 2)", Error, M);
  ASSERT_TRUE(V);
  ASSERT_TRUE(isa<ConstantInt>(V));

  V = parseConstantValue("ptr blockaddress(@test, %entry)", Error, M);
  ASSERT_TRUE(V);
  ASSERT_TRUE(isa<BlockAddress>(V));

  V = parseConstantValue("ptr undef", Error, M);
  ASSERT_TRUE(V);
  ASSERT_TRUE(isa<UndefValue>(V));

  EXPECT_FALSE(parseConstantValue("duble 3.25", Error, M));
  EXPECT_EQ(Error.getMessage(), "expected type");

  EXPECT_FALSE(parseConstantValue("i32 3.25", Error, M));
  EXPECT_EQ(Error.getMessage(), "floating point constant invalid for type");

  EXPECT_FALSE(parseConstantValue("ptr @foo", Error, M));
  EXPECT_EQ(Error.getMessage(), "expected a constant value");

  EXPECT_FALSE(parseConstantValue("i32 3, ", Error, M));
  EXPECT_EQ(Error.getMessage(), "expected end of string");
}

TEST(AsmParserTest, TypeAndConstantValueWithSlotMappingParsing) {
  LLVMContext Ctx;
  SMDiagnostic Error;
  StringRef Source =
      "%st = type { i32, i32 }\n"
      "@v = common global [50 x %st] zeroinitializer, align 16\n"
      "%0 = type { i32, i32, i32, i32 }\n"
      "@g = common global [50 x %0] zeroinitializer, align 16\n"
      "define void @marker4(i64 %d) {\n"
      "entry:\n"
      "  %conv = trunc i64 %d to i32\n"
      "  store i32 %conv, ptr getelementptr inbounds "
      "    ([50 x %st], ptr @v, i64 0, i64 1, i32 0), align 16\n"
      "  store i32 %conv, ptr getelementptr inbounds "
      "    ([50 x %0], ptr @g, i64 0, i64 1, i32 0), align 16\n"
      "  ret void\n"
      "}";
  SlotMapping Mapping;
  auto Mod = parseAssemblyString(Source, Error, Ctx, &Mapping);
  ASSERT_TRUE(Mod != nullptr);
  auto &M = *Mod;

  const Value *V;
  V = parseConstantValue("ptr getelementptr inbounds ([50 x %st], ptr "
                         "@v, i64 0, i64 1, i32 0)",
                         Error, M, &Mapping);
  ASSERT_TRUE(V);
  ASSERT_TRUE(isa<ConstantExpr>(V));

  V = parseConstantValue("ptr getelementptr inbounds ([50 x %0], ptr "
                         "@g, i64 0, i64 1, i32 0)",
                         Error, M, &Mapping);
  ASSERT_TRUE(V);
  ASSERT_TRUE(isa<ConstantExpr>(V));
}

TEST(AsmParserTest, TypeWithSlotMappingParsing) {
  LLVMContext Ctx;
  SMDiagnostic Error;
  StringRef Source =
      "%st = type { i32, i32 }\n"
      "@v = common global [50 x %st] zeroinitializer, align 16\n"
      "%0 = type { i32, i32, i32, i32 }\n"
      "@g = common global [50 x %0] zeroinitializer, align 16\n"
      "define void @marker4(i64 %d) {\n"
      "entry:\n"
      "  %conv = trunc i64 %d to i32\n"
      "  store i32 %conv, ptr getelementptr inbounds "
      "    ([50 x %st], ptr @v, i64 0, i64 0, i32 0), align 16\n"
      "  store i32 %conv, ptr getelementptr inbounds "
      "    ([50 x %0], ptr @g, i64 0, i64 0, i32 0), align 16\n"
      "  ret void\n"
      "}";
  SlotMapping Mapping;
  auto Mod = parseAssemblyString(Source, Error, Ctx, &Mapping);
  ASSERT_TRUE(Mod != nullptr);
  auto &M = *Mod;

  // Check we properly parse integer types.
  Type *Ty;
  Ty = parseType("i32", Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isIntegerTy());
  ASSERT_TRUE(Ty->getPrimitiveSizeInBits() == 32);

  // Check we properly parse integer types with exotic size.
  Ty = parseType("i13", Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isIntegerTy());
  ASSERT_TRUE(Ty->getPrimitiveSizeInBits() == 13);

  // Check we properly parse floating point types.
  Ty = parseType("float", Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isFloatTy());

  Ty = parseType("double", Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isDoubleTy());

  // Check we properly parse struct types.
  // Named struct.
  Ty = parseType("%st", Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isStructTy());

  // Check the details of the struct.
  StructType *ST = cast<StructType>(Ty);
  ASSERT_TRUE(ST->getNumElements() == 2);
  for (unsigned i = 0, e = ST->getNumElements(); i != e; ++i) {
    Ty = ST->getElementType(i);
    ASSERT_TRUE(Ty->isIntegerTy());
    ASSERT_TRUE(Ty->getPrimitiveSizeInBits() == 32);
  }

  // Anonymous struct.
  Ty = parseType("%0", Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isStructTy());

  // Check the details of the struct.
  ST = cast<StructType>(Ty);
  ASSERT_TRUE(ST->getNumElements() == 4);
  for (unsigned i = 0, e = ST->getNumElements(); i != e; ++i) {
    Ty = ST->getElementType(i);
    ASSERT_TRUE(Ty->isIntegerTy());
    ASSERT_TRUE(Ty->getPrimitiveSizeInBits() == 32);
  }

  // Check we properly parse vector types.
  Ty = parseType("<5 x i32>", Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isVectorTy());

  // Check the details of the vector.
  auto *VT = cast<FixedVectorType>(Ty);
  ASSERT_TRUE(VT->getNumElements() == 5);
  ASSERT_TRUE(VT->getPrimitiveSizeInBits().getFixedValue() == 160);
  Ty = VT->getElementType();
  ASSERT_TRUE(Ty->isIntegerTy());
  ASSERT_TRUE(Ty->getPrimitiveSizeInBits() == 32);

  // Opaque struct.
  Ty = parseType("%opaque", Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isStructTy());

  ST = cast<StructType>(Ty);
  ASSERT_TRUE(ST->isOpaque());

  // Check we properly parse pointer types.
  Ty = parseType("ptr", Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isPointerTy());

  // Check that we reject types with garbage.
  Ty = parseType("i32 garbage", Error, M, &Mapping);
  ASSERT_TRUE(!Ty);
}

TEST(AsmParserTest, TypeAtBeginningWithSlotMappingParsing) {
  LLVMContext Ctx;
  SMDiagnostic Error;
  StringRef Source =
      "%st = type { i32, i32 }\n"
      "@v = common global [50 x %st] zeroinitializer, align 16\n"
      "%0 = type { i32, i32, i32, i32 }\n"
      "@g = common global [50 x %0] zeroinitializer, align 16\n"
      "define void @marker4(i64 %d) {\n"
      "entry:\n"
      "  %conv = trunc i64 %d to i32\n"
      "  store i32 %conv, ptr getelementptr inbounds "
      "    ([50 x %st], ptr @v, i64 0, i64 0, i32 0), align 16\n"
      "  store i32 %conv, ptr getelementptr inbounds "
      "    ([50 x %0], ptr @g, i64 0, i64 0, i32 0), align 16\n"
      "  ret void\n"
      "}";
  SlotMapping Mapping;
  auto Mod = parseAssemblyString(Source, Error, Ctx, &Mapping);
  ASSERT_TRUE(Mod != nullptr);
  auto &M = *Mod;
  unsigned Read;

  // Check we properly parse integer types.
  Type *Ty;
  Ty = parseTypeAtBeginning("i32", Read, Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isIntegerTy());
  ASSERT_TRUE(Ty->getPrimitiveSizeInBits() == 32);
  ASSERT_TRUE(Read == 3);

  // Check we properly parse integer types with exotic size.
  Ty = parseTypeAtBeginning("i13", Read, Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isIntegerTy());
  ASSERT_TRUE(Ty->getPrimitiveSizeInBits() == 13);
  ASSERT_TRUE(Read == 3);

  // Check we properly parse floating point types.
  Ty = parseTypeAtBeginning("float", Read, Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isFloatTy());
  ASSERT_TRUE(Read == 5);

  Ty = parseTypeAtBeginning("double", Read, Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isDoubleTy());
  ASSERT_TRUE(Read == 6);

  // Check we properly parse struct types.
  // Named struct.
  Ty = parseTypeAtBeginning("%st", Read, Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isStructTy());
  ASSERT_TRUE(Read == 3);

  // Check the details of the struct.
  StructType *ST = cast<StructType>(Ty);
  ASSERT_TRUE(ST->getNumElements() == 2);
  for (unsigned i = 0, e = ST->getNumElements(); i != e; ++i) {
    Ty = ST->getElementType(i);
    ASSERT_TRUE(Ty->isIntegerTy());
    ASSERT_TRUE(Ty->getPrimitiveSizeInBits() == 32);
  }

  // Anonymous struct.
  Ty = parseTypeAtBeginning("%0", Read, Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isStructTy());
  ASSERT_TRUE(Read == 2);

  // Check the details of the struct.
  ST = cast<StructType>(Ty);
  ASSERT_TRUE(ST->getNumElements() == 4);
  for (unsigned i = 0, e = ST->getNumElements(); i != e; ++i) {
    Ty = ST->getElementType(i);
    ASSERT_TRUE(Ty->isIntegerTy());
    ASSERT_TRUE(Ty->getPrimitiveSizeInBits() == 32);
  }

  // Check we properly parse vector types.
  Ty = parseTypeAtBeginning("<5 x i32>", Read, Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isVectorTy());
  ASSERT_TRUE(Read == 9);

  // Check the details of the vector.
  auto *VT = cast<FixedVectorType>(Ty);
  ASSERT_TRUE(VT->getNumElements() == 5);
  ASSERT_TRUE(VT->getPrimitiveSizeInBits().getFixedValue() == 160);
  Ty = VT->getElementType();
  ASSERT_TRUE(Ty->isIntegerTy());
  ASSERT_TRUE(Ty->getPrimitiveSizeInBits() == 32);

  // Opaque struct.
  Ty = parseTypeAtBeginning("%opaque", Read, Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isStructTy());
  ASSERT_TRUE(Read == 7);

  ST = cast<StructType>(Ty);
  ASSERT_TRUE(ST->isOpaque());

  // Check we properly parse pointer types.
  // One indirection.
  Ty = parseTypeAtBeginning("ptr", Read, Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isPointerTy());
  ASSERT_TRUE(Read == 3);

  // Check that we reject types with garbage.
  Ty = parseTypeAtBeginning("i32 garbage", Read, Error, M, &Mapping);
  ASSERT_TRUE(Ty);
  ASSERT_TRUE(Ty->isIntegerTy());
  ASSERT_TRUE(Ty->getPrimitiveSizeInBits() == 32);
  // We go to the next token, i.e., we read "i32" + ' '.
  ASSERT_TRUE(Read == 4);
}

TEST(AsmParserTest, InvalidDataLayoutStringCallback) {
  LLVMContext Ctx;
  SMDiagnostic Error;
  // Note the invalid i8:7 part
  // Overalign i32 as marker so we can check that indeed this DL was used,
  // and not some default.
  StringRef InvalidDLStr =
      "e-m:e-p:64:64-i8:7-i16:16-i32:64-i64:64-f80:128-n8:16:32:64";
  StringRef FixedDLStr =
      "e-m:e-p:64:64-i8:8-i16:16-i32:64-i64:64-f80:128-n8:16:32:64";
  Expected<DataLayout> ExpectedFixedDL = DataLayout::parse(FixedDLStr);
  ASSERT_TRUE(!ExpectedFixedDL.takeError());
  DataLayout FixedDL = ExpectedFixedDL.get();
  std::string Source = ("target datalayout = \"" + InvalidDLStr + "\"\n").str();
  MemoryBufferRef SourceBuffer(Source, "<string>");

  // Check that we reject the source without a DL override.
  SlotMapping Mapping1;
  auto Mod1 = parseAssembly(SourceBuffer, Error, Ctx, &Mapping1);
  EXPECT_TRUE(Mod1 == nullptr);

  // Check that we pass the correct DL str to the callback,
  // that fixing the DL str from the callback works,
  // and that the resulting module has the correct DL.
  SlotMapping Mapping2;
  auto Mod2 = parseAssembly(
      SourceBuffer, Error, Ctx, &Mapping2,
      [&](StringRef Triple, StringRef DLStr) -> std::optional<std::string> {
        EXPECT_EQ(DLStr, InvalidDLStr);
        return std::string{FixedDLStr};
      });
  ASSERT_TRUE(Mod2 != nullptr);
  EXPECT_EQ(Mod2->getDataLayout(), FixedDL);
}

class DIExprAsmParserTest : public testing::Test {
protected:
  LLVMContext Context;
  Type *Int64Ty = Type::getInt64Ty(Context);
  Type *Int32Ty = Type::getInt32Ty(Context);
  Type *Int16Ty = Type::getInt16Ty(Context);
  Type *Int8Ty = Type::getInt8Ty(Context);
  Type *FloatTy = Type::getFloatTy(Context);
  std::string IR;
  std::unique_ptr<Module> M;

  // NB: Can only be called once per test; acts as SetUp with an argument.
  DIExpr *parseDIExpr(Twine Expr) {
    IR = ("!named = !{" + Expr + "}").str();
    SMDiagnostic Err;
    M = parseAssemblyString(IR, Err, Context);
    if (!M)
      return nullptr;
    NamedMDNode *N = M->getNamedMetadata("named");
    if (!N || N->getNumOperands() != 1u || !isa<DIExpr>(N->getOperand(0)))
      return nullptr;
    return cast<DIExpr>(N->getOperand(0));
  }
};

TEST_F(DIExprAsmParserTest, Empty) {
  DIExpr *Expr = parseDIExpr("!DIExpr()");
  EXPECT_TRUE(Expr != nullptr);
  DIExprViewer Viewer = Expr->viewer();
  ASSERT_EQ(std::distance(Viewer.begin(), Viewer.end()), 0u);
}

TEST_F(DIExprAsmParserTest, Referrer) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpReferrer(i32))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Referrer(Int32Ty)}));
}

TEST_F(DIExprAsmParserTest, Arg) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpArg(3, float))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Arg(3, FloatTy)}));
}

TEST_F(DIExprAsmParserTest, TypeObject) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpTypeObject(i32))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::TypeObject(Int32Ty)}));
}

TEST_F(DIExprAsmParserTest, Constant) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpConstant(float 2.0))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>(
                {DIOp::Constant(ConstantFP::get(Context, APFloat(2.0f)))}));
}

TEST_F(DIExprAsmParserTest, Reinterpret) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpReinterpret(i32 addrspace(5)*))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>(
                {DIOp::Reinterpret(PointerType::get(Context, 5))}));
}

TEST_F(DIExprAsmParserTest, BitOffset) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpBitOffset(i32))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::BitOffset(Int32Ty)}));
}

TEST_F(DIExprAsmParserTest, ByteOffset) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpByteOffset(i32))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::ByteOffset(Int32Ty)}));
}

TEST_F(DIExprAsmParserTest, Composite) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpComposite(2, i8))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Composite(2, Int8Ty)}));
}

TEST_F(DIExprAsmParserTest, Extend) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpExtend(2))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Extend(2)}));
}

TEST_F(DIExprAsmParserTest, Select) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpSelect())");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Select()}));
}

TEST_F(DIExprAsmParserTest, AddrOf) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpAddrOf(7))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::AddrOf(7)}));
}

TEST_F(DIExprAsmParserTest, Deref) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpDeref(i32))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Deref(Int32Ty)}));
}

TEST_F(DIExprAsmParserTest, Read) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpRead())");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Read()}));
}

TEST_F(DIExprAsmParserTest, Add) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpAdd())");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Add()}));
}

TEST_F(DIExprAsmParserTest, Sub) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpSub())");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Sub()}));
}

TEST_F(DIExprAsmParserTest, Mul) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpMul())");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Mul()}));
}

TEST_F(DIExprAsmParserTest, Div) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpDiv())");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Div()}));
}

TEST_F(DIExprAsmParserTest, Shr) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpShr())");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Shr()}));
}

TEST_F(DIExprAsmParserTest, Shl) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpShl())");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::Shl()}));
}

TEST_F(DIExprAsmParserTest, PushLane) {
  DIExpr *Expr = parseDIExpr("!DIExpr(DIOpPushLane(i32))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>({DIOp::PushLane(Int32Ty)}));
}

TEST_F(DIExprAsmParserTest, MultipleOps) {
  DIExpr *Expr = parseDIExpr(R"(!DIExpr(
    DIOpArg(0, i8),
    DIOpArg(1, i8),
    DIOpAdd(),
    DIOpArg(2, i8),
    DIOpComposite(2, i16),
    DIOpReinterpret(i8 addrspace(1)*)
  ))");
  EXPECT_TRUE(Expr != nullptr);
  ASSERT_EQ(SmallVector<DIOp::Variant>(Expr->viewer().range()),
            SmallVector<DIOp::Variant>(
                {DIOp::Arg(0, Int8Ty), DIOp::Arg(1, Int8Ty), DIOp::Add(),
                 DIOp::Arg(2, Int8Ty), DIOp::Composite(2, Int16Ty),
                 DIOp::Reinterpret(PointerType::get(Int8Ty, 1))}));
}

} // end anonymous namespace
