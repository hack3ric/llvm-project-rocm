; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -passes=attributor -S < %s | FileCheck %s --check-prefixes=CHECK
; RUN: opt -passes=attributor -attributor-print-call-graph -S -disable-output < %s | FileCheck %s --check-prefixes=DOT

define dso_local void @func1() {
; CHECK-LABEL: @func1(
; CHECK-NEXT:    br label [[TMP2:%.*]]
; CHECK:       1:
; CHECK-NEXT:    unreachable
; CHECK:       2:
; CHECK-NEXT:    call void @func3()
; CHECK-NEXT:    ret void
;
  %1 = icmp ne i32 0, 0
  br i1 %1, label %2, label %3

2:                                                ; preds = %0
  call void @func2()
  br label %3

3:                                                ; preds = %2, %0
  call void () @func3()
  ret void
}

declare void @func3()
declare void @func4()

define dso_local void @func2() {
; CHECK-LABEL: @func2(
; CHECK-NEXT:    call void @func4()
; CHECK-NEXT:    ret void
;
  call void @func4()
  ret void
}


define void @func5(i32 %0) {
; CHECK-LABEL: @func5(
; CHECK-NEXT:    [[TMP2:%.*]] = icmp ne i32 [[TMP0:%.*]], 0
; CHECK-NEXT:    [[TMP3:%.*]] = select i1 [[TMP2]], ptr @func4, ptr @func3
; CHECK-NEXT:    [[TMP4:%.*]] = icmp eq ptr [[TMP3]], @func3
; CHECK-NEXT:    br i1 [[TMP4]], label [[TMP5:%.*]], label [[TMP6:%.*]]
; CHECK:       5:
; CHECK-NEXT:    call void @func3()
; CHECK-NEXT:    br label [[TMP9:%.*]]
; CHECK:       6:
; CHECK-NEXT:    br i1 true, label [[TMP7:%.*]], label [[TMP8:%.*]]
; CHECK:       7:
; CHECK-NEXT:    call void @func4()
; CHECK-NEXT:    br label [[TMP9]]
; CHECK:       8:
; CHECK-NEXT:    unreachable
; CHECK:       9:
; CHECK-NEXT:    ret void
;
  %2 = icmp ne i32 %0, 0
  %3 = select i1 %2, ptr @func4, ptr @func3
  call void () %3()
  ret void
}

define i32 @musttailCall(i32 %0) {
; CHECK-LABEL: @musttailCall(
; CHECK-NEXT:    [[TMP2:%.*]] = icmp ne i32 [[TMP0:%.*]], 0
; CHECK-NEXT:    [[TMP3:%.*]] = select i1 [[TMP2]], ptr @func4, ptr @func3
; CHECK-NEXT:    [[C:%.*]] = musttail call i32 [[TMP3]](i32 0)
; CHECK-NEXT:    ret i32 [[C]]
;
  %2 = icmp ne i32 %0, 0
  %3 = select i1 %2, ptr @func4, ptr @func3
  %c = musttail call i32 (i32) %3(i32 0)
  ret i32 %c
}

declare i32 @retI32()
declare void @takeI32(i32)
declare float @retFloatTakeFloat(float)
declare void @void()

define i32 @non_matching_fp1(i1 %c1, i1 %c2, i1 %c) {
; CHECK-LABEL: @non_matching_fp1(
; CHECK-NEXT:    [[FP1:%.*]] = select i1 [[C1:%.*]], ptr @retI32, ptr @takeI32
; CHECK-NEXT:    [[FP2:%.*]] = select i1 [[C2:%.*]], ptr @retFloatTakeFloat, ptr @void
; CHECK-NEXT:    [[FP:%.*]] = select i1 [[C:%.*]], ptr [[FP1]], ptr [[FP2]]
; CHECK-NEXT:    [[TMP1:%.*]] = icmp eq ptr [[FP]], @takeI32
; CHECK-NEXT:    br i1 [[TMP1]], label [[TMP2:%.*]], label [[TMP3:%.*]]
; CHECK:       2:
; CHECK-NEXT:    [[CALL1:%.*]] = call i32 @takeI32(i32 42)
; CHECK-NEXT:    br label [[TMP15:%.*]]
; CHECK:       3:
; CHECK-NEXT:    [[TMP4:%.*]] = icmp eq ptr [[FP]], @retI32
; CHECK-NEXT:    br i1 [[TMP4]], label [[TMP5:%.*]], label [[TMP6:%.*]]
; CHECK:       5:
; CHECK-NEXT:    [[CALL2:%.*]] = call i32 @retI32(i32 42)
; CHECK-NEXT:    br label [[TMP15]]
; CHECK:       6:
; CHECK-NEXT:    [[TMP7:%.*]] = icmp eq ptr [[FP]], @void
; CHECK-NEXT:    br i1 [[TMP7]], label [[TMP8:%.*]], label [[TMP9:%.*]]
; CHECK:       8:
; CHECK-NEXT:    [[CALL3:%.*]] = call i32 @void(i32 42)
; CHECK-NEXT:    br label [[TMP15]]
; CHECK:       9:
; CHECK-NEXT:    br i1 true, label [[TMP10:%.*]], label [[TMP14:%.*]]
; CHECK:       10:
; CHECK-NEXT:    [[TMP11:%.*]] = bitcast i32 42 to float
; CHECK-NEXT:    [[TMP12:%.*]] = call float @retFloatTakeFloat(float [[TMP11]])
; CHECK-NEXT:    [[TMP13:%.*]] = bitcast float [[TMP12]] to i32
; CHECK-NEXT:    br label [[TMP15]]
; CHECK:       14:
; CHECK-NEXT:    unreachable
; CHECK:       15:
; CHECK-NEXT:    [[CALL_PHI:%.*]] = phi i32 [ [[CALL1]], [[TMP2]] ], [ [[CALL2]], [[TMP5]] ], [ [[CALL3]], [[TMP8]] ], [ [[TMP13]], [[TMP10]] ]
; CHECK-NEXT:    ret i32 [[CALL_PHI]]
;
  %fp1 = select i1 %c1, ptr @retI32, ptr @takeI32
  %fp2 = select i1 %c2, ptr @retFloatTakeFloat, ptr @void
  %fp = select i1 %c, ptr %fp1, ptr %fp2
  %call = call i32 %fp(i32 42)
  ret i32 %call
}

define void @non_matching_fp2(i1 %c1, i1 %c2, i1 %c, ptr %unknown) {
; CHECK-LABEL: @non_matching_fp2(
; CHECK-NEXT:    [[FP1:%.*]] = select i1 [[C1:%.*]], ptr @retI32, ptr @takeI32
; CHECK-NEXT:    [[FP2:%.*]] = select i1 [[C2:%.*]], ptr @retFloatTakeFloat, ptr [[UNKNOWN:%.*]]
; CHECK-NEXT:    [[FP:%.*]] = select i1 [[C:%.*]], ptr [[FP1]], ptr [[FP2]]
; CHECK-NEXT:    [[TMP1:%.*]] = icmp eq ptr [[FP]], @takeI32
; CHECK-NEXT:    br i1 [[TMP1]], label [[TMP2:%.*]], label [[TMP3:%.*]]
; CHECK:       2:
; CHECK-NEXT:    call void @takeI32()
; CHECK-NEXT:    br label [[TMP10:%.*]]
; CHECK:       3:
; CHECK-NEXT:    [[TMP4:%.*]] = icmp eq ptr [[FP]], @retI32
; CHECK-NEXT:    br i1 [[TMP4]], label [[TMP5:%.*]], label [[TMP6:%.*]]
; CHECK:       5:
; CHECK-NEXT:    call void @retI32()
; CHECK-NEXT:    br label [[TMP10]]
; CHECK:       6:
; CHECK-NEXT:    [[TMP7:%.*]] = icmp eq ptr [[FP]], @retFloatTakeFloat
; CHECK-NEXT:    br i1 [[TMP7]], label [[TMP8:%.*]], label [[TMP9:%.*]]
; CHECK:       8:
; CHECK-NEXT:    call void @retFloatTakeFloat()
; CHECK-NEXT:    br label [[TMP10]]
; CHECK:       9:
; CHECK-NEXT:    call void [[FP]]()
; CHECK-NEXT:    br label [[TMP10]]
; CHECK:       10:
; CHECK-NEXT:    ret void
;
  %fp1 = select i1 %c1, ptr @retI32, ptr @takeI32
  %fp2 = select i1 %c2, ptr @retFloatTakeFloat, ptr %unknown
  %fp = select i1 %c, ptr %fp1, ptr %fp2
  call void %fp()
  ret void
}

define i32 @non_matching_unknown(i1 %c, ptr %fn) {
; CHECK-LABEL: @non_matching_unknown(
; CHECK-NEXT:    [[FP:%.*]] = select i1 [[C:%.*]], ptr @retI32, ptr [[FN:%.*]]
; CHECK-NEXT:    [[TMP1:%.*]] = icmp eq ptr [[FP]], @retI32
; CHECK-NEXT:    br i1 [[TMP1]], label [[TMP2:%.*]], label [[TMP3:%.*]]
; CHECK:       2:
; CHECK-NEXT:    [[CALL1:%.*]] = call i32 @retI32(i32 42)
; CHECK-NEXT:    br label [[TMP4:%.*]]
; CHECK:       3:
; CHECK-NEXT:    [[CALL2:%.*]] = call i32 [[FP]](i32 42)
; CHECK-NEXT:    br label [[TMP4]]
; CHECK:       4:
; CHECK-NEXT:    [[CALL_PHI:%.*]] = phi i32 [ [[CALL1]], [[TMP2]] ], [ [[CALL2]], [[TMP3]] ]
; CHECK-NEXT:    ret i32 [[CALL_PHI]]
;
  %fp = select i1 %c, ptr @retI32, ptr %fn
  %call = call i32 %fp(i32 42)
  ret i32 %call
}

; This function is used in a "direct" call but with a different signature.
; We check that it does not show up above in any of the if-cascades because
; the address is not actually taken.
declare void @usedOnlyInCastedDirectCall(i32)
define void @usedOnlyInCastedDirectCallCaller() {
; CHECK-LABEL: @usedOnlyInCastedDirectCallCaller(
; CHECK-NEXT:    call void @usedOnlyInCastedDirectCall()
; CHECK-NEXT:    ret void
;
  call void @usedOnlyInCastedDirectCall()
  ret void
}

define internal void @usedByGlobal() {
; CHECK-LABEL: @usedByGlobal(
; CHECK-NEXT:    ret void
;
  ret void
}
@G = global ptr @usedByGlobal

define void @broker(ptr %unknown) !callback !0 {
; CHECK-LABEL: @broker(
; CHECK-NEXT:    call void [[UNKNOWN:%.*]]()
; CHECK-NEXT:    ret void
;
  call void %unknown()
  ret void
}

define void @func6() {
; CHECK-LABEL: @func6(
; CHECK-NEXT:    call void @broker(ptr nocapture nofree noundef nonnull @func3)
; CHECK-NEXT:    ret void
;
  call void @broker(ptr @func3)
  ret void
}

define void @func7(ptr %unknown) {
; CHECK-LABEL: @func7(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp eq ptr [[UNKNOWN:%.*]], @func3
; CHECK-NEXT:    br i1 [[TMP1]], label [[TMP2:%.*]], label [[TMP3:%.*]]
; CHECK:       2:
; CHECK-NEXT:    call void @func3()
; CHECK-NEXT:    br label [[TMP6:%.*]]
; CHECK:       3:
; CHECK-NEXT:    br i1 true, label [[TMP4:%.*]], label [[TMP5:%.*]]
; CHECK:       4:
; CHECK-NEXT:    call void @func4()
; CHECK-NEXT:    br label [[TMP6]]
; CHECK:       5:
; CHECK-NEXT:    unreachable
; CHECK:       6:
; CHECK-NEXT:    ret void
;
  call void %unknown(), !callees !2
  ret void
}

; Check there's no crash if something that isn't a function appears in !callees
define void @undef_in_callees() {
; CHECK-LABEL: @undef_in_callees(
; CHECK-NEXT:  cond.end.i:
; CHECK-NEXT:    unreachable
;
cond.end.i:
  call void undef(ptr undef, i32 undef, ptr undef), !callees !3
  ret void
}

define void @as_cast(ptr %arg) {
; OWRDL-LABEL: @as_cast(
; OWRDL-NEXT:    [[FP:%.*]] = load ptr addrspace(1), ptr [[ARG:%.*]], align 8
; OWRDL-NEXT:    tail call addrspace(1) void [[FP]]()
; OWRDL-NEXT:    ret void
;
; CWRLD-LABEL: @as_cast(
; CWRLD-NEXT:    [[FP:%.*]] = load ptr addrspace(1), ptr [[ARG:%.*]], align 8
; CWRLD-NEXT:    [[FP_AS0:%.*]] = addrspacecast ptr addrspace(1) [[FP]] to ptr
; CWRLD-NEXT:    [[TMP1:%.*]] = icmp eq ptr [[FP_AS0]], @func3
; CWRLD-NEXT:    br i1 [[TMP1]], label [[TMP2:%.*]], label [[TMP3:%.*]]
; CWRLD:       2:
; CWRLD-NEXT:    tail call void @func3()
; CWRLD-NEXT:    br label [[TMP21:%.*]]
; CWRLD:       3:
; CWRLD-NEXT:    [[TMP4:%.*]] = icmp eq ptr [[FP_AS0]], @func4
; CWRLD-NEXT:    br i1 [[TMP4]], label [[TMP5:%.*]], label [[TMP6:%.*]]
; CWRLD:       5:
; CWRLD-NEXT:    tail call void @func4()
; CWRLD-NEXT:    br label [[TMP21]]
; CWRLD:       6:
; CWRLD-NEXT:    [[TMP7:%.*]] = icmp eq ptr [[FP_AS0]], @retI32
; CWRLD-NEXT:    br i1 [[TMP7]], label [[TMP8:%.*]], label [[TMP9:%.*]]
; CWRLD:       8:
; CWRLD-NEXT:    call void @retI32()
; CWRLD-NEXT:    br label [[TMP21]]
; CWRLD:       9:
; CWRLD-NEXT:    [[TMP10:%.*]] = icmp eq ptr [[FP_AS0]], @takeI32
; CWRLD-NEXT:    br i1 [[TMP10]], label [[TMP11:%.*]], label [[TMP12:%.*]]
; CWRLD:       11:
; CWRLD-NEXT:    call void @takeI32()
; CWRLD-NEXT:    br label [[TMP21]]
; CWRLD:       12:
; CWRLD-NEXT:    [[TMP13:%.*]] = icmp eq ptr [[FP_AS0]], @retFloatTakeFloat
; CWRLD-NEXT:    br i1 [[TMP13]], label [[TMP14:%.*]], label [[TMP15:%.*]]
; CWRLD:       14:
; CWRLD-NEXT:    call void @retFloatTakeFloat()
; CWRLD-NEXT:    br label [[TMP21]]
; CWRLD:       15:
; CWRLD-NEXT:    [[TMP16:%.*]] = icmp eq ptr [[FP_AS0]], @retFloatTakeFloatFloatNoundef
; CWRLD-NEXT:    br i1 [[TMP16]], label [[TMP17:%.*]], label [[TMP18:%.*]]
; CWRLD:       17:
; CWRLD-NEXT:    call void @retFloatTakeFloatFloatNoundef()
; CWRLD-NEXT:    br label [[TMP21]]
; CWRLD:       18:
; CWRLD-NEXT:    br i1 true, label [[TMP19:%.*]], label [[TMP20:%.*]]
; CWRLD:       19:
; CWRLD-NEXT:    tail call void @void()
; CWRLD-NEXT:    br label [[TMP21]]
; CWRLD:       20:
; CWRLD-NEXT:    unreachable
; CWRLD:       21:
; CWRLD-NEXT:    ret void
;
; CHECK-LABEL: @as_cast(
; CHECK-NEXT:    [[FP:%.*]] = load ptr addrspace(1), ptr [[ARG:%.*]], align 8
; CHECK-NEXT:    tail call addrspace(1) void [[FP]]()
; CHECK-NEXT:    ret void
;
  %fp = load ptr addrspace(1), ptr %arg, align 8
  tail call addrspace(1) void %fp()
  ret void
}

!0 = !{!1}
!1 = !{i64 0, i1 false}
!2 = !{ptr @func3, ptr @func4}
!3 = distinct !{ptr undef, ptr null}

; UTC_ARGS: --disable

; DOT-DAG: Node[[FUNC1:0x[a-z0-9]+]] [shape=record,label="{func1}"];
; DOT-DAG: Node[[FUNC2:0x[a-z0-9]+]] [shape=record,label="{func2}"];
; DOT-DAG: Node[[FUNC3:0x[a-z0-9]+]] [shape=record,label="{func3}"];
; DOT-DAG: Node[[FUNC4:0x[a-z0-9]+]] [shape=record,label="{func4}"];
; DOT-DAG: Node[[FUNC5:0x[a-z0-9]+]] [shape=record,label="{func5}"];
; DOT-DAG: Node[[FUNC6:0x[a-z0-9]+]] [shape=record,label="{func6}"];
; DOT-DAG: Node[[FUNC7:0x[a-z0-9]+]] [shape=record,label="{func7}"];

; DOT-DAG: Node[[BROKER:0x[a-z0-9]+]] [shape=record,label="{broker}"];

; DOT-DAG: Node[[FUNC1]] -> Node[[FUNC3]];
; DOT-DAG: Node[[FUNC2]] -> Node[[FUNC4]];
; DOT-DAG: Node[[FUNC5]] -> Node[[FUNC3]];
; DOT-DAG: Node[[FUNC5]] -> Node[[FUNC4]];

; DOT-DAG: Node[[FUNC6]] -> Node[[BROKER]];

; This one gets added because of the callback metadata.
; DOT-DAG: Node[[FUNC6]] -> Node[[FUNC3]];

; These ones are added because of the callees metadata.
; DOT-DAG: Node[[FUNC7]] -> Node[[FUNC3]];
; DOT-DAG: Node[[FUNC7]] -> Node[[FUNC4]];

; UTC_ARGS: --enable

; UNLIM: [[META0:![0-9]+]] = !{!1}
; UNLIM: [[META1:![0-9]+]] = !{i64 0, i1 false}
; UNLIM: [[META2:![0-9]+]] = distinct !{ptr undef, ptr null}
; LIMI2: [[META0:![0-9]+]] = !{ptr @void, ptr @retFloatTakeFloat}
; LIMI2: [[META1:![0-9]+]] = !{ptr @void}
; LIMI2: [[META2:![0-9]+]] = !{!3}
; LIMI2: [[META3:![0-9]+]] = !{i64 0, i1 false}
; LIMI2: [[META4:![0-9]+]] = distinct !{ptr undef, ptr null}
; LIMI0: [[META0:![0-9]+]] = !{ptr @func4, ptr @internal_good}
; LIMI0: [[META1:![0-9]+]] = !{ptr @func3, ptr @func4}
; LIMI0: [[META2:![0-9]+]] = !{ptr @takeI32, ptr @retI32, ptr @void, ptr @retFloatTakeFloat}
; LIMI0: [[META3:![0-9]+]] = !{ptr @takeI32, ptr @retI32, ptr @void}
; LIMI0: [[META4:![0-9]+]] = !{!5}
; LIMI0: [[META5:![0-9]+]] = !{i64 0, i1 false}
; LIMI0: [[META6:![0-9]+]] = distinct !{ptr undef, ptr null}
;; NOTE: These prefixes are unused and the list is autogenerated. Do not add tests below this line:
; DOT: {{.*}}
