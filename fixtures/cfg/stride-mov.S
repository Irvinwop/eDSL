/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.intel_syntax noprefix
.text
.globl sum_stride_mov
.type sum_stride_mov, @function
sum_stride_mov:
  mov eax, 0
.Lheader:
  test rsi, rsi
  je .Lreturn
  add eax, DWORD PTR [rdi]
  dec rsi
  add rdi, 8
  jmp .Lheader
.Lreturn:
  ret
.size sum_stride_mov, .-sum_stride_mov
.section .note.GNU-stack,"",@progbits
