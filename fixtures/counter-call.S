/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl edsl_run_counter
.type edsl_run_counter,@function
/* SysV (function, shared word, count, remaining_out) to the verified routine's
 * RDI/RCX interface. Capture RCX immediately after the tested code returns. */
edsl_run_counter:
    push %rbx
    mov %rcx, %rbx
    mov %rdi, %r11
    mov %rsi, %rdi
    mov %rdx, %rcx
    call *%r11
    mov %rcx, (%rbx)
    pop %rbx
    ret
.size edsl_run_counter, .-edsl_run_counter
.section .note.GNU-stack,"",@progbits
