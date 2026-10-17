/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Adapted from comparison64's single-threaded whole-call observer. Recovery
 * state is RIP-relative, so safe owned saved-GPR/RET $8 mutants cannot damage
 * the observer. RSP always starts as a real aligned host stack pointer. */
.text
.globl edsl_logical64_probe
.type edsl_logical64_probe,@function
edsl_logical64_probe:
    pushfq
    popq edsl_logical64_host_flags(%rip)
    pushq %rbx
    pushq %rbp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    subq $8, %rsp
    movq %rsp, edsl_logical64_host_rsp(%rip)
    movq %rdi, edsl_logical64_function(%rip)

    /* Install all 128 arithmetic/ID profiles, keeping DF clear for SysV.
     * Capture the actual effective flags; POPFQ is not assumed unrestricted. */
    movq edsl_logical64_host_flags(%rip), %rax
    andq $-2100438, %rax /* ~(0x8d5 | 0x200000 | 0x400) */
    orq edsl_logical64_input+64(%rip), %rax
    pushq %rax
    popfq
    pushfq
    popq edsl_logical64_output+72(%rip)
    movq edsl_logical64_input+16(%rip), %rbx
    movq edsl_logical64_input+24(%rip), %rbp
    movq edsl_logical64_input+32(%rip), %r12
    movq edsl_logical64_input+40(%rip), %r13
    movq edsl_logical64_input+48(%rip), %r14
    movq edsl_logical64_input+56(%rip), %r15
    movq edsl_logical64_input+0(%rip), %rdi
    movq edsl_logical64_input+8(%rip), %rsi
    movabsq $0xd0e1f20314253647, %rdx
    movabsq $0x91b2c3d4e5f60718, %rax
    movq %rsp, edsl_logical64_output+56(%rip)
    call *edsl_logical64_function(%rip)

    /* Only MOVs precede the final flags capture. Restore the real stack
     * before PUSHFQ, including after the owned RET $8 imbalance mutant. */
    movq %rax, edsl_logical64_output+0(%rip)
    movq %rbx, edsl_logical64_output+8(%rip)
    movq %rbp, edsl_logical64_output+16(%rip)
    movq %r12, edsl_logical64_output+24(%rip)
    movq %r13, edsl_logical64_output+32(%rip)
    movq %r14, edsl_logical64_output+40(%rip)
    movq %r15, edsl_logical64_output+48(%rip)
    movq %rsp, edsl_logical64_output+64(%rip)
    movq edsl_logical64_host_rsp(%rip), %rsp
    pushfq
    popq edsl_logical64_output+80(%rip)
    pushq edsl_logical64_host_flags(%rip)
    popfq
    leaq 8(%rsp), %rsp
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbp
    popq %rbx
    ret
.size edsl_logical64_probe,.-edsl_logical64_probe

.bss
.balign 8
edsl_logical64_host_flags: .zero 8
edsl_logical64_host_rsp: .zero 8
edsl_logical64_function: .zero 8

/* Complete fresh final ELF sections, embedded without decoding or rewriting.
 * The assembler runs in the evidence directory. These seven-byte profiles
 * have no address-dependent instruction or relocation. */
.section .edsl_logical64,"ax",@progbits
.macro FINAL name, file
.balign 16
.globl edsl_logical64_\name
.globl edsl_logical64_\name\()_end
.type edsl_logical64_\name,@function
edsl_logical64_\name:
.incbin "\file"
edsl_logical64_\name\()_end:
.size edsl_logical64_\name,.-edsl_logical64_\name
.endm
FINAL gcc_intersection64,gcc/intersection64/function.bin
FINAL gcc_union64,gcc/union64/function.bin
FINAL gcc_symmetric_difference64,gcc/symmetric_difference64/function.bin
FINAL clang_intersection64,clang/intersection64/function.bin
FINAL clang_union64,clang/union64/function.bin
FINAL clang_symmetric_difference64,clang/symmetric_difference64/function.bin

.text
.macro BEGIN name
.globl edsl_logical64_\name
.type edsl_logical64_\name,@function
edsl_logical64_\name:
.endm
.macro END name
.globl edsl_logical64_\name\()_end
edsl_logical64_\name\()_end:
.size edsl_logical64_\name,.-edsl_logical64_\name
.endm
.macro INTERSECTION
    movq %rdi, %rax
    andq %rsi, %rax
.endm
.macro UNION
    movq %rdi, %rax
    orq %rsi, %rax
.endm
.macro DIFFERENCE
    movq %rdi, %rax
    xorq %rsi, %rax
.endm

/* Independent scalar contracts permit these arithmetic flag assignments. */
.macro ALLOWED_FLAGS name, operation
BEGIN \name
    \operation
    pushfq
    orq $0x8d5, (%rsp)
    popfq
    ret
END \name
.endm
ALLOWED_FLAGS allowed_intersection_flags,INTERSECTION
ALLOWED_FLAGS allowed_union_flags,UNION
ALLOWED_FLAGS allowed_difference_flags,DIFFERENCE

/* Owned safe defects, never compiler outputs or untrusted input programs. */
.macro WRONG_OPERATION name, operation
BEGIN \name
    \operation
    ret
END \name
.endm
WRONG_OPERATION bad_intersection_union,UNION
WRONG_OPERATION bad_intersection_difference,DIFFERENCE
WRONG_OPERATION bad_union_intersection,INTERSECTION
WRONG_OPERATION bad_union_difference,DIFFERENCE
WRONG_OPERATION bad_difference_intersection,INTERSECTION
WRONG_OPERATION bad_difference_union,UNION
.macro WRONG_WIDTH name, operation
BEGIN \name
    movl %edi, %eax
    \operation %esi, %eax
    ret
END \name
.endm
WRONG_WIDTH bad_intersection_width,andl
WRONG_WIDTH bad_union_width,orl
WRONG_WIDTH bad_difference_width,xorl
.macro WRONG_OPERAND name, operation
BEGIN \name
    movq %rdi, %rax
    \operation %rdx, %rax
    ret
END \name
.endm
WRONG_OPERAND bad_intersection_operand,andq
WRONG_OPERAND bad_union_operand,orq
WRONG_OPERAND bad_difference_operand,xorq
.macro BAD_SAVED name, register
BEGIN \name
    INTERSECTION
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
    INTERSECTION
    ret $8
END bad_rsp
BEGIN bad_df
    INTERSECTION
    std
    ret
END bad_df
BEGIN bad_id
    INTERSECTION
    pushfq
    xorq $0x200000, (%rsp)
    popfq
    ret
END bad_id
.section .note.GNU-stack,"",@progbits
