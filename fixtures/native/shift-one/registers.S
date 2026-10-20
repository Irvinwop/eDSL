/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
 * SysV run(input[10], seed<8, Snapshot*), project-owned stable ordinary RAM.
 * Actual observed order: RAX RCX RDX RBX RSP RBP R8 R9 R12 R13 R15.
 * R14 is the capture pointer, R10 scratch. The five omitted GPRs have NO
 * physical values in the TSV. Callee-saved GPRs and the live RSP are restored.
 * MOV and balanced PUSHFQ/POP-to-GPR surround the labeled instruction.
 * No POPFQ. ADD outside the window establishes dirty arithmetic flag seeds.
 */
.section .rodata.shift_one_seeds,"a",@progbits
.p2align 2
shift_one_seeds:
.long 0,0
.long 0xffffffff,1
.long 0x7fffffff,1
.long 0x80000000,0x80000000
.long 0x0000000f,1
.long 0x7ffffffe,1
.long 0,1
.long 0xfffffffe,1

.macro SNAPSHOT offset
movq %rax, \offset+0(%r14)
movq %rcx, \offset+8(%r14)
movq %rdx, \offset+16(%r14)
movq %rbx, \offset+24(%r14)
movq %rsp, \offset+32(%r14)
movq %rbp, \offset+40(%r14)
movq %r8,  \offset+48(%r14)
movq %r9,  \offset+56(%r14)
movq %r12, \offset+64(%r14)
movq %r13, \offset+72(%r14)
movq %r15, \offset+80(%r14)
.endm

.macro OBSERVE name, encoded_operand, rex
.section .text.shift_one_\name,"ax",@progbits
.p2align 4
.globl shift_one_\name
.type shift_one_\name,@function
shift_one_\name:
pushq %rbx
pushq %rbp
pushq %r12
pushq %r13
pushq %r14
pushq %r15
movq %rdx, %r14
movq %rdi, %r10
leaq shift_one_seeds(%rip), %rdi
movl %esi, %esi
movl (%rdi,%rsi,8), %edx
addl 4(%rdi,%rsi,8), %edx
movq 0(%r10), %rax
movq 8(%r10), %rcx
movq 16(%r10), %rdx
movq 24(%r10), %rbx
movq 32(%r10), %rbp
movq 40(%r10), %r8
movq 48(%r10), %r9
movq 56(%r10), %r12
movq 64(%r10), %r13
movq 72(%r10), %r15
SNAPSHOT 0
pushfq
popq %r10
movq %r10, 176(%r14)
.globl shift_one_\name\()_instruction
shift_one_\name\()_instruction:
/* The assembler independently produces D1 /5 mod3. Low-bank 32-bit operand
 * spellings prevent an extra REX; the explicit REX.W/B determines the actual
 * 64-bit destination. In particular 49 + encoded ESP writes R12, never RSP.
 * probes.def is deliberately not included by this file. */
.byte \rex
shrl $1, \encoded_operand
.globl shift_one_\name\()_instruction_end
shift_one_\name\()_instruction_end:
pushfq
popq %r10
movq %r10, 184(%r14)
SNAPSHOT 88
popq %r15
popq %r14
popq %r13
popq %r12
popq %rbp
popq %rbx
ret
.size shift_one_\name, .-shift_one_\name
.endm

/* This safe owned negative changes an ignored prefix bit. The capture must
 * reject its live label bytes BEFORE any fixture window runs. */
#ifdef SHIFT_ONE_NEGATIVE_WINDOW
OBSERVE shr_rax_48, %eax, 0x4a
#else
OBSERVE shr_rax_48, %eax, 0x48
#endif
OBSERVE shr_rcx_48, %ecx, 0x48
OBSERVE shr_rdx_48, %edx, 0x48
OBSERVE shr_rbx_48, %ebx, 0x48
OBSERVE shr_rbp_48, %ebp, 0x48
OBSERVE shr_r8_49,  %eax, 0x49
OBSERVE shr_r9_49,  %ecx, 0x49
OBSERVE shr_r12_49, %esp, 0x49
OBSERVE shr_r13_49, %ebp, 0x49
OBSERVE shr_r15_49, %edi, 0x49
OBSERVE shr_rax_4a, %eax, 0x4a
OBSERVE shr_rcx_4a, %ecx, 0x4a
OBSERVE shr_rdx_4a, %edx, 0x4a
OBSERVE shr_rbx_4a, %ebx, 0x4a
OBSERVE shr_rbp_4a, %ebp, 0x4a
OBSERVE shr_r8_4b,  %eax, 0x4b
OBSERVE shr_r9_4b,  %ecx, 0x4b
OBSERVE shr_r12_4b, %esp, 0x4b
OBSERVE shr_r13_4b, %ebp, 0x4b
OBSERVE shr_r15_4b, %edi, 0x4b
OBSERVE shr_rax_4c, %eax, 0x4c
OBSERVE shr_rcx_4c, %ecx, 0x4c
OBSERVE shr_rdx_4c, %edx, 0x4c
OBSERVE shr_rbx_4c, %ebx, 0x4c
OBSERVE shr_rbp_4c, %ebp, 0x4c
OBSERVE shr_r8_4d,  %eax, 0x4d
OBSERVE shr_r9_4d,  %ecx, 0x4d
OBSERVE shr_r12_4d, %esp, 0x4d
OBSERVE shr_r13_4d, %ebp, 0x4d
OBSERVE shr_r15_4d, %edi, 0x4d
OBSERVE shr_rax_4e, %eax, 0x4e
OBSERVE shr_rcx_4e, %ecx, 0x4e
OBSERVE shr_rdx_4e, %edx, 0x4e
OBSERVE shr_rbx_4e, %ebx, 0x4e
OBSERVE shr_rbp_4e, %ebp, 0x4e
OBSERVE shr_r8_4f,  %eax, 0x4f
OBSERVE shr_r9_4f,  %ecx, 0x4f
OBSERVE shr_r12_4f, %esp, 0x4f
OBSERVE shr_r13_4f, %ebp, 0x4f
OBSERVE shr_r15_4f, %edi, 0x4f
.section .note.GNU-stack,"",@progbits
