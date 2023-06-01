; RUN: llvm-as < %s | llvm-dis | llvm-as | llvm-dis | FileCheck %s
; RUN: verify-uselistorder %s

; CHECK: !named = !{!0, !1}
!named = !{!0, !1}

; CHECK: !0 = distinct !DIFragment(type: i32)
!0 = distinct !DIFragment(type: i32)

; CHECK: !1 = distinct !DIFragment(type: i32)
!1 = distinct !DIFragment(type: i32)
