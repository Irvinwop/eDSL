/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* A complete 68-byte named extent with unreachable, authenticated suffix text. */
.section .text
.globl profiled
.type profiled, @function
profiled:
    mov $42, %eax
    ret
    .rept 30
    .byte 0x66, 0x90
    .endr
    nop
    ret
.size profiled, .-profiled
.section .note.GNU-stack,"",@progbits
