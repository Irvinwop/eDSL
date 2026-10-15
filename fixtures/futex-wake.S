/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#ifndef EDSL_FUTEX_SYSCALL
#define EDSL_FUTEX_SYSCALL 202
#endif
#ifndef EDSL_FUTEX_WAKE_OP
#define EDSL_FUTEX_WAKE_OP 129
#endif
#ifndef EDSL_FUTEX_WAKE_COUNT
#define EDSL_FUTEX_WAKE_COUNT 1
#endif
.section .text.edsl_futex_wake_stub,"ax",@progbits
.globl edsl_futex_wake_stub
.type edsl_futex_wake_stub,@function
edsl_futex_wake_stub:
    movl $EDSL_FUTEX_SYSCALL, %eax
    movl $EDSL_FUTEX_WAKE_OP, %esi
    movl $EDSL_FUTEX_WAKE_COUNT, %edx
    syscall
    ret
.size edsl_futex_wake_stub,.-edsl_futex_wake_stub
.section .note.GNU-stack,"",@progbits
