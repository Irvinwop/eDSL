/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#ifndef EDSL_FUTEX_SYSCALL
#define EDSL_FUTEX_SYSCALL 202
#endif
#ifndef EDSL_FUTEX_WAIT_OP
#define EDSL_FUTEX_WAIT_OP 128
#endif
#ifndef EDSL_FUTEX_RETURN
#define EDSL_FUTEX_RETURN 0xc3
#endif
.section .text.edsl_futex_wait_stub,"ax",@progbits
.globl edsl_futex_wait_stub
.type edsl_futex_wait_stub,@function
edsl_futex_wait_stub:
    movl $EDSL_FUTEX_SYSCALL, %eax
    movl $EDSL_FUTEX_WAIT_OP, %esi
    syscall
    .byte EDSL_FUTEX_RETURN
.size edsl_futex_wait_stub,.-edsl_futex_wait_stub
.section .note.GNU-stack,"",@progbits
