/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl write_word_moves
.type write_word_moves,@function
write_word_moves:
    movl %esi, %ecx
    movl %ecx, (%rdi)
    movl (%rdi), %ecx
    ret
.size write_word_moves,.-write_word_moves
.section .note.GNU-stack,"",@progbits
