; RUN: llvm-as < %s | llvm-bcanalyzer -dump | FileCheck %s

!named = !{!0, !1}

; CHECK:      <METADATA_BLOCK
; CHECK-NEXT: <FRAGMENT op0=1/>
!0 = distinct !DIFragment(type: i32)
; CHECK-NEXT: <FRAGMENT op0=1/>
!1 = distinct !DIFragment(type: i32)
