/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#ifndef EDSL_WRITE_COUNT
#define EDSL_WRITE_COUNT 3
#endif
#ifndef EDSL_WRITE_DESCRIPTOR
#define EDSL_WRITE_DESCRIPTOR 1
#endif
#ifndef EDSL_WRITE_FIRST_BYTE
#define EDSL_WRITE_FIRST_BYTE 0x4f
#endif
.text
.globl _start
.type _start, @function
_start:
    movl $EDSL_WRITE_DESCRIPTOR, %edi
    movl $message, %esi
    movl $EDSL_WRITE_COUNT, %edx
    movl $1, %eax
    syscall
    movl $42, %edi
    movl $60, %eax
    syscall
.size _start, .-_start
message:
    .byte EDSL_WRITE_FIRST_BYTE, 0x4b, 0x0a
.section .note.GNU-stack,"",@progbits
