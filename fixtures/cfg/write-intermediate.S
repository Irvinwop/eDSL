/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl write_word_intermediate
.type write_word_intermediate,@function
write_word_intermediate:
    incq %rsi
    movl %esi, (%rdi)
    decq %rsi
    movl %esi, (%rdi)
    ret
.size write_word_intermediate,.-write_word_intermediate
.section .note.GNU-stack,"",@progbits
