/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl store_return32_copied
.type store_return32_copied,@function
store_return32_copied:
    movq %rdi, %rax
    movl %esi, (%rax)
    ret
.size store_return32_copied, .-store_return32_copied
.section .note.GNU-stack,"",@progbits
