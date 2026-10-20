/* Owned, valid x86-64 register fixtures; no corpus ELF is executed.
 * SysV: RDI=input, ESI=seed index in [0,8), RDX=80-byte Snapshot*.
 * Only caller-saved GPRs and the normal private stack scratch are used.
 * PUSHFQ reads flags; POP targets a GPR, never RFLAGS.
 */

.section .rodata.fixture_add_seeds,"a",@progbits
.p2align 2
fixture_add_seeds:
    .long 0x00000000, 0x00000000
    .long 0xffffffff, 0x00000001
    .long 0x7fffffff, 0x00000001
    .long 0x80000000, 0x80000000
    .long 0x0000000f, 0x00000001
    .long 0x7ffffffe, 0x00000001
    .long 0x00000000, 0x00000001
    .long 0xfffffffe, 0x00000001

.macro OBSERVE name, target, opcode:vararg
.section .text.\name,"ax",@progbits
.p2align 4
.globl \name
.type \name,@function
\name:
    movq %rdx, %r11
    movl %esi, %esi
    movabsq $0x1122334455667788, %rax
    movabsq $0x8877665544332211, %rcx
    movabsq $0x0123456789abcdef, %r8
    movabsq $0xfedcba9876543210, %r9
    movq %rdi, \target
    movq %rax, 0(%r11)
    movq %rcx, 8(%r11)
    movq %r8, 16(%r11)
    movq %r9, 24(%r11)
    leaq fixture_add_seeds(%rip), %r10
    movl (%r10,%rsi,8), %edx
    addl 4(%r10,%rsi,8), %edx
    pushfq
    popq %r10
    movq %r10, 64(%r11)
.globl \name\()_instruction
\name\()_instruction:
    .byte \opcode
.globl \name\()_instruction_end
\name\()_instruction_end:
    pushfq
    popq %r10
    movq %r10, 72(%r11)
    movq %rax, 32(%r11)
    movq %rcx, 40(%r11)
    movq %r8, 48(%r11)
    movq %r9, 56(%r11)
    ret
.size \name, .-\name
.endm

OBSERVE fixture_neg32_eax, %rax, 0xf7, 0xd8
OBSERVE fixture_neg32_ecx, %rcx, 0xf7, 0xd9
OBSERVE fixture_neg32_r8d, %r8, 0x41, 0xf7, 0xd8
OBSERVE fixture_neg32_r9d, %r9, 0x41, 0xf7, 0xd9
OBSERVE fixture_bswap64_rax, %rax, 0x48, 0x0f, 0xc8
OBSERVE fixture_bswap64_rcx, %rcx, 0x48, 0x0f, 0xc9
OBSERVE fixture_bswap64_r8, %r8, 0x49, 0x0f, 0xc8
OBSERVE fixture_bswap64_r9, %r9, 0x49, 0x0f, 0xc9

.section .note.GNU-stack,"",@progbits
