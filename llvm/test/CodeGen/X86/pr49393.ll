; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-unknown-linux-gnu | FileCheck %s

define void @f() {
; CHECK-LABEL: f:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    xorl %eax, %eax
; CHECK-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; CHECK-NEXT:    movapd %xmm0, %xmm1
; CHECK-NEXT:    mulsd %xmm0, %xmm1
; CHECK-NEXT:    subsd %xmm0, %xmm1
; CHECK-NEXT:    .p2align 4, 0x90
; CHECK-NEXT:  .LBB0_1: # %for.cond
; CHECK-NEXT:    # =>This Inner Loop Header: Depth=1
; CHECK-NEXT:    imull %eax, %eax
; CHECK-NEXT:    cwtl
; CHECK-NEXT:    xorps %xmm2, %xmm2
; CHECK-NEXT:    cvtsi2sd %eax, %xmm2
; CHECK-NEXT:    mulsd %xmm0, %xmm2
; CHECK-NEXT:    mulsd %xmm0, %xmm2
; CHECK-NEXT:    movapd %xmm2, %xmm3
; CHECK-NEXT:    mulsd %xmm1, %xmm3
; CHECK-NEXT:    mulsd %xmm0, %xmm2
; CHECK-NEXT:    movapd %xmm1, %xmm4
; CHECK-NEXT:    subsd %xmm3, %xmm4
; CHECK-NEXT:    addsd %xmm2, %xmm4
; CHECK-NEXT:    cvttsd2si %xmm4, %eax
; CHECK-NEXT:    jmp .LBB0_1
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.cond, %entry
  %b.0 = phi i16 [ 0, %entry ], [ %conv77, %for.cond ]
  %mul18 = mul i16 %b.0, %b.0
  %arrayidx.real = load double, double* undef, align 1
  %arrayidx.imag = load double, double* undef, align 1
  %mul_ac = fmul fast double %arrayidx.real, %arrayidx.real
  %0 = fadd fast double 0.000000e+00, %arrayidx.real
  %sub.r = fsub fast double %mul_ac, %0
  %sub.i = fsub fast double 0.000000e+00, %arrayidx.imag
  %conv28 = sitofp i16 %mul18 to double
  %mul_bc32 = fmul fast double %arrayidx.imag, %conv28
  %mul_bd46 = fmul fast double %mul_bc32, %arrayidx.imag
  %mul_r49 = fsub fast double 0.000000e+00, %mul_bd46
  %mul_ac59 = fmul fast double %mul_r49, %sub.r
  %mul_bc48 = fmul fast double %mul_bc32, %arrayidx.real
  %mul_i50 = fadd fast double 0.000000e+00, %mul_bc48
  %1 = fmul fast double %mul_i50, %sub.i
  %.neg = fneg fast double %0
  %.neg19 = fmul fast double %1, -1.000000e+00
  %.neg20 = fadd fast double %.neg, %mul_ac
  %2 = fadd fast double %.neg20, %mul_ac59
  %sub.r75 = fadd fast double %2, %.neg19
  %conv77 = fptosi double %sub.r75 to i16
  br label %for.cond
}
