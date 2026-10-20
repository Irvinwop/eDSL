/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl cfg_early
.type cfg_early,@function
cfg_early:
    xorl %eax, %eax
    testq %rsi, %rsi
    je 1f
    movl $1, %eax
    ret
1:  ret
.size cfg_early,.-cfg_early
.section .note.GNU-stack,"",@progbits
