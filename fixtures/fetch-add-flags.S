/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl edsl_observe_fetch_add
.type edsl_observe_fetch_add,@function
/* (function, cell, delta, flags_out): preserve SysV stack alignment and capture
 * the flags immediately after RET, before any arithmetic can overwrite them. */
edsl_observe_fetch_add:
    push %rbx
    mov %rcx, %rbx
    mov %rdi, %r11
    mov %rsi, %rdi
    mov %edx, %esi
    call *%r11
    pushfq
    pop %rdx
    mov %rdx, (%rbx)
    pop %rbx
    ret
.size edsl_observe_fetch_add, .-edsl_observe_fetch_add
.section .note.GNU-stack,"",@progbits
