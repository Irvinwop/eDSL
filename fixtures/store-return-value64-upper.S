/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl edsl_store_return_value64_upper
.type edsl_store_return_value64_upper,@function
edsl_store_return_value64_upper:
    movq %rdi, %rcx
    addq $4, %rcx
    movl (%rcx), %edx
    movq %rsi, %rax
    movq %rax, (%rdi)
    ret
.size edsl_store_return_value64_upper,.-edsl_store_return_value64_upper
.section .note.GNU-stack,"",@progbits
