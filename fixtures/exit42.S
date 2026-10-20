/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#ifndef EDSL_EXIT_STATUS
#define EDSL_EXIT_STATUS 42
#endif
#ifndef EDSL_EXIT_SYSCALL
#define EDSL_EXIT_SYSCALL 60
#endif
.text
.globl _start
.type _start, @function
_start:
    movl $EDSL_EXIT_STATUS, %edi
    movl $EDSL_EXIT_SYSCALL, %eax
    syscall
.size _start, .-_start
.section .note.GNU-stack,"",@progbits
