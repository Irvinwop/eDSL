/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Single-threaded machine-context observer. Only MOVs occur between flag
 * installation and CALL, or between return and final flag capture. Globals
 * recover the real host context after the safe owned register/RET mutants.
 * Pthread workers call the embedded functions directly, never this observer. */
.text
.globl edsl_atomic64_probe
.type edsl_atomic64_probe,@function
edsl_atomic64_probe:
    pushfq
    popq edsl_atomic64_host_flags(%rip)
    pushq %rbx
    pushq %rbp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    subq $40, %rsp
    movq %rsp, edsl_atomic64_host_rsp(%rip)
    movq %rdi, edsl_atomic64_function(%rip)
    movabsq $0x6d3a8271f0b459ce, %rax
    movq %rax, 0(%rsp)
    movabsq $0xa159c7302edb864f, %rax
    movq %rax, 8(%rsp)
    movabsq $0x38b64fa20dc195e7, %rax
    movq %rax, 16(%rsp)
    movabsq $0xf4719dce620ba358, %rax
    movq %rax, 24(%rsp)

    /* All 256 CF/PF/AF/ZF/SF/OF/DF/ID profiles. DF is restored before C;
     * DF=1 exercises the raw machine contract outside an ordinary SysV call.
     * Other user-mode flags retain their actual effective host values. */
    movq edsl_atomic64_host_flags(%rip), %rax
    andq $-2100438, %rax /* ~(0x8d5 | 0x400 | 0x200000) */
    orq edsl_atomic64_input+120(%rip), %rax
    pushq %rax
    popfq
    pushfq
    popq edsl_atomic64_output+136(%rip)
    movq edsl_atomic64_input+0(%rip), %rax
    movq edsl_atomic64_input+8(%rip), %rbx
    movq edsl_atomic64_input+16(%rip), %rcx
    movq edsl_atomic64_input+24(%rip), %rdx
    movq edsl_atomic64_input+32(%rip), %rsi
    movq edsl_atomic64_input+40(%rip), %rdi
    movq edsl_atomic64_input+48(%rip), %rbp
    movq edsl_atomic64_input+56(%rip), %r8
    movq edsl_atomic64_input+64(%rip), %r9
    movq edsl_atomic64_input+72(%rip), %r10
    movq edsl_atomic64_input+80(%rip), %r11
    movq edsl_atomic64_input+88(%rip), %r12
    movq edsl_atomic64_input+96(%rip), %r13
    movq edsl_atomic64_input+104(%rip), %r14
    movq edsl_atomic64_input+112(%rip), %r15
    movq %rsp, edsl_atomic64_output+120(%rip)
    call *edsl_atomic64_function(%rip)
.globl edsl_atomic64_return
edsl_atomic64_return:
    movq %rax, edsl_atomic64_output+0(%rip)
    movq %rbx, edsl_atomic64_output+8(%rip)
    movq %rcx, edsl_atomic64_output+16(%rip)
    movq %rdx, edsl_atomic64_output+24(%rip)
    movq %rsi, edsl_atomic64_output+32(%rip)
    movq %rdi, edsl_atomic64_output+40(%rip)
    movq %rbp, edsl_atomic64_output+48(%rip)
    movq %r8, edsl_atomic64_output+56(%rip)
    movq %r9, edsl_atomic64_output+64(%rip)
    movq %r10, edsl_atomic64_output+72(%rip)
    movq %r11, edsl_atomic64_output+80(%rip)
    movq %r12, edsl_atomic64_output+88(%rip)
    movq %r13, edsl_atomic64_output+96(%rip)
    movq %r14, edsl_atomic64_output+104(%rip)
    movq %r15, edsl_atomic64_output+112(%rip)
    movq %rsp, edsl_atomic64_output+128(%rip)
    movq edsl_atomic64_host_rsp(%rip), %rsp
    movq -8(%rsp), %rax
    movq %rax, edsl_atomic64_output+152(%rip)
    pushfq
    popq edsl_atomic64_output+144(%rip)
    movq 0(%rsp), %rax
    movq %rax, edsl_atomic64_output+160(%rip)
    movq 8(%rsp), %rax
    movq %rax, edsl_atomic64_output+168(%rip)
    movq 16(%rsp), %rax
    movq %rax, edsl_atomic64_output+176(%rip)
    movq 24(%rsp), %rax
    movq %rax, edsl_atomic64_output+184(%rip)
    pushq edsl_atomic64_host_flags(%rip)
    popfq
    leaq 40(%rsp), %rsp
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbp
    popq %rbx
    ret
.size edsl_atomic64_probe,.-edsl_atomic64_probe

.bss
.balign 8
edsl_atomic64_host_flags: .zero 8
edsl_atomic64_host_rsp: .zero 8
edsl_atomic64_function: .zero 8

/* The assembler runs in the fresh evidence directory. These are COMPLETE
 * final-linked .text extractions, with no instruction rewriting/relocation. */
.section .edsl_atomic64,"ax",@progbits
.macro FINAL name, file
.balign 16
.globl edsl_atomic64_\name
.globl edsl_atomic64_\name\()_start
.globl edsl_atomic64_\name\()_end
.type edsl_atomic64_\name,@function
edsl_atomic64_\name:
edsl_atomic64_\name\()_start:
.incbin "\file"
edsl_atomic64_\name\()_end:
.size edsl_atomic64_\name,.-edsl_atomic64_\name
.endm
FINAL gcc_or64,gcc/function.bin
FINAL clang_or64,clang/function.bin

.text
.macro BEGIN name
.globl edsl_atomic64_\name
.globl edsl_atomic64_\name\()_start
.type edsl_atomic64_\name,@function
edsl_atomic64_\name:
edsl_atomic64_\name\()_start:
.endm
.macro END name
.globl edsl_atomic64_\name\()_end
edsl_atomic64_\name\()_end:
.size edsl_atomic64_\name,.-edsl_atomic64_\name
.endm

/* AF is undefined. BOTH forced AF values must be accepted by the oracle. */
BEGIN allowed_af_clear
    lock orq %rsi, (%rdi)
    pushfq
    andq $-17, (%rsp)
    popfq
    ret
END allowed_af_clear
BEGIN allowed_af_set
    lock orq %rsi, (%rdi)
    pushfq
    orq $16, (%rsp)
    popfq
    ret
END allowed_af_set

/* Intentionally passes single-thread value/ABI/flags checks. Those checks
 * cannot establish LOCK atomicity. This control is never run concurrently. */
BEGIN unlocked_control
    orq %rsi, (%rdi)
    ret
END unlocked_control

/* Safe, synthetic project-owned semantic negatives. None are compiler output. */
BEGIN bad_width32
    lock orl %esi, (%rdi)
    ret
END bad_width32
BEGIN bad_width16
    lock orw %si, (%rdi)
    ret
END bad_width16
BEGIN bad_source
    lock orq %rdx, (%rdi)
    ret
END bad_source
BEGIN bad_mask
    lock orq $1, (%rdi)
    ret
END bad_mask
BEGIN bad_and
    lock andq %rsi, (%rdi)
    ret
END bad_and
BEGIN bad_xor
    lock xorq %rsi, (%rdi)
    ret
END bad_xor
BEGIN bad_fetched_rax
    movq (%rdi), %rax
    lock orq %rsi, (%rdi)
    ret
END bad_fetched_rax
.macro BAD_GPR name, reg
BEGIN \name
    lock orq %rsi, (%rdi)
    notq \reg
    ret
END \name
.endm
BAD_GPR bad_rax,%rax
BAD_GPR bad_rbx,%rbx
BAD_GPR bad_rcx,%rcx
BAD_GPR bad_rdx,%rdx
BAD_GPR bad_rsi,%rsi
BAD_GPR bad_rdi,%rdi
BAD_GPR bad_rbp,%rbp
BAD_GPR bad_r8,%r8
BAD_GPR bad_r9,%r9
BAD_GPR bad_r10,%r10
BAD_GPR bad_r11,%r11
BAD_GPR bad_r12,%r12
BAD_GPR bad_r13,%r13
BAD_GPR bad_r14,%r14
BAD_GPR bad_r15,%r15
BEGIN bad_rsp
    lock orq %rsi, (%rdi)
    ret $8
END bad_rsp
BEGIN bad_guard_before
    lock orq %rsi, (%rdi)
    notb -1(%rdi)
    ret
END bad_guard_before
BEGIN bad_guard_after
    lock orq %rsi, (%rdi)
    notb 8(%rdi)
    ret
END bad_guard_after
.macro BAD_FLAG name, mask
BEGIN \name
    lock orq %rsi, (%rdi)
    pushfq
    xorq $\mask, (%rsp)
    popfq
    ret
END \name
.endm
BAD_FLAG bad_cf,0x1
BAD_FLAG bad_pf,0x4
BAD_FLAG bad_zf,0x40
BAD_FLAG bad_sf,0x80
BAD_FLAG bad_of,0x800
BAD_FLAG bad_df,0x400
BAD_FLAG bad_id,0x200000
BEGIN bad_flags_unchanged
    pushfq
    lock orq %rsi, (%rdi)
    popfq
    ret
END bad_flags_unchanged
.section .note.GNU-stack,"",@progbits
