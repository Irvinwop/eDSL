/* SysV run(input[10], seed<4, Snapshot*), project-owned ordinary RAM.
 * Selected GPR order: RAX RCX RDX RBX RSP RBP R8 R9 R12 R13 R15.
 * Callee-saved registers are restored. RSP is read, never overwritten by a
 * tested instruction. R14 is the capture pointer, R10 scratch. Only MOV and
 * balanced PUSHFQ/POP-to-GPR occur between the flag snapshots and the window.
 * No POPFQ; ADD outside the window establishes four arithmetic flag seeds.
 */
.section .rodata.counter_seeds,"a",@progbits
.p2align 2
counter_seeds:
.long 0,0
.long 0xffffffff,1
.long 0x7fffffff,1
.long 0x80000000,0x80000000

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

.macro OBSERVE name, opcode:vararg
.section .text.counter_\name,"ax",@progbits
.p2align 4
.globl counter_\name
.type counter_\name,@function
counter_\name:
pushq %rbx
pushq %rbp
pushq %r12
pushq %r13
pushq %r14
pushq %r15
movq %rdx, %r14
movq %rdi, %r10
leaq counter_seeds(%rip), %rdi
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
.globl counter_\name\()_instruction
counter_\name\()_instruction:
.byte \opcode
.globl counter_\name\()_instruction_end
counter_\name\()_instruction_end:
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
.size counter_\name, .-counter_\name
.endm

#define P(name,kind,dst,base,index,scale,imm,pref,form,...) OBSERVE name, __VA_ARGS__
#include "probes.def"
#undef P
.section .note.GNU-stack,"",@progbits
