/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl edsl_futex_wait
.type edsl_futex_wait,@function
edsl_futex_wait:
    movl %esi, %edx
    xorl %r10d, %r10d
    xorl %r8d, %r8d
    xorl %r9d, %r9d
    jmp edsl_futex_wait_stub
.size edsl_futex_wait,.-edsl_futex_wait
.globl edsl_futex_wake
.type edsl_futex_wake,@function
edsl_futex_wake:
    xorl %r10d, %r10d
    xorl %r8d, %r8d
    xorl %r9d, %r9d
    jmp edsl_futex_wake_stub
.size edsl_futex_wake,.-edsl_futex_wake
.section .note.GNU-stack,"",@progbits
