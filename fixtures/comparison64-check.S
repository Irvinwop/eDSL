/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Single-threaded whole-call observer. All recovery state is RIP-relative, so
 * an owned callee may damage a saved register or return with RET $8 without
 * damaging the observer. No arbitrary modeled stack pointer is installed. */
.text
.globl edsl_comparison64_probe
.type edsl_comparison64_probe,@function
edsl_comparison64_probe:
    pushfq
    popq edsl_comparison64_host_flags(%rip)
    pushq %rbx
    pushq %rbp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    subq $8, %rsp
    movq %rsp, edsl_comparison64_host_rsp(%rip)
    movq %rdi, edsl_comparison64_function(%rip)

    /* Vary only arithmetic flags and user-writable ID. DF is clear at the
     * actual SysV call. Preserve other host flags and capture what POPFQ did. */
    movq edsl_comparison64_host_flags(%rip), %rax
    andq $-2100438, %rax /* ~(0x8d5 | 0x200000 | 0x400) */
    orq edsl_comparison64_input+64(%rip), %rax
    pushq %rax
    popfq
    pushfq
    popq edsl_comparison64_output+72(%rip)
    movq edsl_comparison64_input+16(%rip), %rbx
    movq edsl_comparison64_input+24(%rip), %rbp
    movq edsl_comparison64_input+32(%rip), %r12
    movq edsl_comparison64_input+40(%rip), %r13
    movq edsl_comparison64_input+48(%rip), %r14
    movq edsl_comparison64_input+56(%rip), %r15
    movq edsl_comparison64_input+0(%rip), %rdi
    movq edsl_comparison64_input+8(%rip), %rsi
    movabsq $0xd0e1f20314253647, %rdx
    movq %rsp, edsl_comparison64_output+56(%rip)
    call *edsl_comparison64_function(%rip)

    /* MOVs preserve the callee's flags. Restore the actual host stack before
     * PUSHFQ, including when the safe stack-imbalance mutant used RET $8. */
    movq %rax, edsl_comparison64_output+0(%rip)
    movq %rbx, edsl_comparison64_output+8(%rip)
    movq %rbp, edsl_comparison64_output+16(%rip)
    movq %r12, edsl_comparison64_output+24(%rip)
    movq %r13, edsl_comparison64_output+32(%rip)
    movq %r14, edsl_comparison64_output+40(%rip)
    movq %r15, edsl_comparison64_output+48(%rip)
    movq %rsp, edsl_comparison64_output+64(%rip)
    movq edsl_comparison64_host_rsp(%rip), %rsp
    pushfq
    popq edsl_comparison64_output+80(%rip)
    pushq edsl_comparison64_host_flags(%rip)
    popfq
    leaq 8(%rsp), %rsp
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbp
    popq %rbx
    ret
.size edsl_comparison64_probe,.-edsl_comparison64_probe

.bss
.balign 8
edsl_comparison64_host_flags: .zero 8
edsl_comparison64_host_rsp: .zero 8
edsl_comparison64_function: .zero 8

/* The build runs the assembler in the evidence directory. These are complete
 * extracted final ELF .text sections, not handwritten copies of instructions.
 * The final-byte profile is position independent and contains no relocations. */
.section .edsl_comparison64,"ax",@progbits
.macro FINAL name, file
.balign 16
.globl edsl_comparison64_\name
.globl edsl_comparison64_\name\()_end
.type edsl_comparison64_\name,@function
edsl_comparison64_\name:
.incbin "\file"
edsl_comparison64_\name\()_end:
.size edsl_comparison64_\name,.-edsl_comparison64_\name
.endm
FINAL gcc_maximum64,gcc/maximum64/function.bin
FINAL gcc_minimum64,gcc/minimum64/function.bin
FINAL gcc_signed_maximum64,gcc/signed_maximum64/function.bin
FINAL clang_maximum64,clang/maximum64/function.bin
FINAL clang_minimum64,clang/minimum64/function.bin
FINAL clang_signed_maximum64,clang/signed_maximum64/function.bin

/* Safe owned synthetic defects, separate from positive compiler artifacts.
 * The C oracle requests operations independently of these implementations. */
.text
.macro BEGIN name
.globl edsl_comparison64_\name
.type edsl_comparison64_\name,@function
edsl_comparison64_\name:
.endm
.macro END name
.size edsl_comparison64_\name,.-edsl_comparison64_\name
.endm
.macro UNSIGNED_MAXIMUM
    movq %rdi, %rax
    cmpq %rsi, %rdi
    cmovbq %rsi, %rax
.endm

BEGIN bad_maximum_direction
    movq %rdi, %rax
    cmpq %rsi, %rdi
    cmovaq %rsi, %rax
    ret
END bad_maximum_direction
BEGIN bad_minimum_direction
    UNSIGNED_MAXIMUM
    ret
END bad_minimum_direction
BEGIN bad_signed_direction
    movq %rdi, %rax
    cmpq %rsi, %rdi
    cmovgq %rsi, %rax
    ret
END bad_signed_direction
BEGIN bad_maximum_signedness
    movq %rdi, %rax
    cmpq %rsi, %rdi
    cmovlq %rsi, %rax
    ret
END bad_maximum_signedness
BEGIN bad_minimum_signedness
    movq %rdi, %rax
    cmpq %rsi, %rdi
    cmovgq %rsi, %rax
    ret
END bad_minimum_signedness
BEGIN bad_signed_signedness
    UNSIGNED_MAXIMUM
    ret
END bad_signed_signedness
BEGIN bad_signed_overflow
    movq %rdi, %rax
    cmpq %rsi, %rdi
    cmovsq %rsi, %rax
    ret
END bad_signed_overflow
BEGIN bad_operand
    movq %rdi, %rax
    cmpq %rsi, %rdi
    cmovbq %rdx, %rax
    ret
END bad_operand
BEGIN bad_narrowing
    movl %edi, %eax
    cmpl %esi, %edi
    cmovbl %esi, %eax
    ret
END bad_narrowing
.macro BAD_SAVED name, register
BEGIN \name
    UNSIGNED_MAXIMUM
    xorq \register, \register
    ret
END \name
.endm
BAD_SAVED bad_rbx,%rbx
BAD_SAVED bad_rbp,%rbp
BAD_SAVED bad_r12,%r12
BAD_SAVED bad_r13,%r13
BAD_SAVED bad_r14,%r14
BAD_SAVED bad_r15,%r15
BEGIN bad_rsp
    UNSIGNED_MAXIMUM
    ret $8
END bad_rsp
BEGIN bad_df
    UNSIGNED_MAXIMUM
    std
    ret
END bad_df
BEGIN bad_id
    UNSIGNED_MAXIMUM
    pushfq
    xorq $0x200000, (%rsp)
    popfq
    ret
END bad_id
.section .note.GNU-stack,"",@progbits
