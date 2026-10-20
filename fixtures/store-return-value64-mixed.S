/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl edsl_store_return_value64_mixed
.type edsl_store_return_value64_mixed,@function
edsl_store_return_value64_mixed:
    xorl %eax, %eax
    movq %rsi, %rax
    movq %rax, (%rdi)
    movl %eax, (%rdi)
    ret
.size edsl_store_return_value64_mixed,.-edsl_store_return_value64_mixed
.section .note.GNU-stack,"",@progbits
