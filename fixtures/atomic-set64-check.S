/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Single-threaded machine-context observer. Only MOVs occur between flag
 * installation and CALL, or between return and final flag capture. Globals
 * recover the real host context after the safe owned register/RET mutants.
 * Pthread workers call the embedded functions directly, never this observer. */
.text
.globl edsl_set64_probe
.type edsl_set64_probe,@function
edsl_set64_probe:
    pushfq
    popq edsl_set64_host_flags(%rip)
    pushq %rbx
    pushq %rbp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    subq $40, %rsp
    movq %rsp, edsl_set64_host_rsp(%rip)
    movq %rdi, edsl_set64_function(%rip)
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
    movq edsl_set64_host_flags(%rip), %rax
    andq $-2100438, %rax /* ~(0x8d5 | 0x400 | 0x200000) */
    orq edsl_set64_input+120(%rip), %rax
    pushq %rax
    popfq
    pushfq
    popq edsl_set64_output+136(%rip)
    movq edsl_set64_input+0(%rip), %rax
    movq edsl_set64_input+8(%rip), %rbx
    movq edsl_set64_input+16(%rip), %rcx
    movq edsl_set64_input+24(%rip), %rdx
    movq edsl_set64_input+32(%rip), %rsi
    movq edsl_set64_input+40(%rip), %rdi
    movq edsl_set64_input+48(%rip), %rbp
    movq edsl_set64_input+56(%rip), %r8
    movq edsl_set64_input+64(%rip), %r9
    movq edsl_set64_input+72(%rip), %r10
    movq edsl_set64_input+80(%rip), %r11
    movq edsl_set64_input+88(%rip), %r12
    movq edsl_set64_input+96(%rip), %r13
    movq edsl_set64_input+104(%rip), %r14
    movq edsl_set64_input+112(%rip), %r15
    movq %rsp, edsl_set64_output+120(%rip)
    call *edsl_set64_function(%rip)
.globl edsl_set64_return
edsl_set64_return:
    movq %rax, edsl_set64_output+0(%rip)
    movq %rbx, edsl_set64_output+8(%rip)
    movq %rcx, edsl_set64_output+16(%rip)
    movq %rdx, edsl_set64_output+24(%rip)
    movq %rsi, edsl_set64_output+32(%rip)
    movq %rdi, edsl_set64_output+40(%rip)
    movq %rbp, edsl_set64_output+48(%rip)
    movq %r8, edsl_set64_output+56(%rip)
    movq %r9, edsl_set64_output+64(%rip)
    movq %r10, edsl_set64_output+72(%rip)
    movq %r11, edsl_set64_output+80(%rip)
    movq %r12, edsl_set64_output+88(%rip)
    movq %r13, edsl_set64_output+96(%rip)
    movq %r14, edsl_set64_output+104(%rip)
    movq %r15, edsl_set64_output+112(%rip)
    movq %rsp, edsl_set64_output+128(%rip)
    movq edsl_set64_host_rsp(%rip), %rsp
    movq -8(%rsp), %rax
    movq %rax, edsl_set64_output+152(%rip)
    pushfq
    popq edsl_set64_output+144(%rip)
    movq 0(%rsp), %rax
    movq %rax, edsl_set64_output+160(%rip)
    movq 8(%rsp), %rax
    movq %rax, edsl_set64_output+168(%rip)
    movq 16(%rsp), %rax
    movq %rax, edsl_set64_output+176(%rip)
    movq 24(%rsp), %rax
    movq %rax, edsl_set64_output+184(%rip)
    pushq edsl_set64_host_flags(%rip)
    popfq
    leaq 40(%rsp), %rsp
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbp
    popq %rbx
    ret
.size edsl_set64_probe,.-edsl_set64_probe

.bss
.balign 8
edsl_set64_host_flags: .zero 8
edsl_set64_host_rsp: .zero 8
edsl_set64_function: .zero 8

/* The assembler runs in the fresh evidence directory. These are COMPLETE
 * final-linked .text extractions, with no instruction rewriting/relocation. */
.section .edsl_set64,"ax",@progbits
.macro FINAL name, file
.balign 16
.globl edsl_set64_\name
.globl edsl_set64_\name\()_start
.globl edsl_set64_\name\()_end
.type edsl_set64_\name,@function
edsl_set64_\name:
edsl_set64_\name\()_start:
.incbin "\file"
edsl_set64_\name\()_end:
.size edsl_set64_\name,.-edsl_set64_\name
.endm
FINAL gcc_c_and64,gcc_c/and/function.bin
FINAL gcc_c_or64,gcc_c/or/function.bin
FINAL gcc_c_xor64,gcc_c/xor/function.bin
FINAL clang_c_and64,clang_c/and/function.bin
FINAL clang_c_or64,clang_c/or/function.bin
FINAL clang_c_xor64,clang_c/xor/function.bin
FINAL clang_cpp_and64,clang_cpp/and/function.bin
FINAL clang_cpp_or64,clang_cpp/or/function.bin
FINAL clang_cpp_xor64,clang_cpp/xor/function.bin

.text
.macro BEGIN name
.globl edsl_set64_\name
.globl edsl_set64_\name\()_start
.type edsl_set64_\name,@function
edsl_set64_\name:
edsl_set64_\name\()_start:
.endm
.macro END name
.globl edsl_set64_\name\()_end
edsl_set64_\name\()_end:
.size edsl_set64_\name,.-edsl_set64_\name
.endm
/* AF is undefined; both forced values must pass. Unlocked controls are
 * single-thread only, and must pass; observations do not establish LOCK. */
BEGIN and_af_clear
    lock andq %rsi, (%rdi)
    pushfq
    andq $-17, (%rsp)
    popfq
    ret
END and_af_clear
BEGIN and_af_set
    lock andq %rsi, (%rdi)
    pushfq
    orq $16, (%rsp)
    popfq
    ret
END and_af_set
BEGIN and_unlocked
    andq %rsi, (%rdi)
    ret
END and_unlocked
BEGIN and_bad_width32
    lock andl %esi, (%rdi)
    ret
END and_bad_width32
BEGIN and_bad_width16
    lock andw %si, (%rdi)
    ret
END and_bad_width16
BEGIN and_bad_source
    lock andq %rdx, (%rdi)
    ret
END and_bad_source
BEGIN and_bad_mask
    lock andq $1, (%rdi)
    ret
END and_bad_mask
BEGIN and_bad_operation
    lock xorq %rsi, (%rdi)
    ret
END and_bad_operation
BEGIN and_bad_fetched_rax
    movq (%rdi), %rax
    lock andq %rsi, (%rdi)
    ret
END and_bad_fetched_rax
BEGIN and_bad_rax
    lock andq %rsi, (%rdi)
    notq %rax
    ret
END and_bad_rax
BEGIN and_bad_rbx
    lock andq %rsi, (%rdi)
    notq %rbx
    ret
END and_bad_rbx
BEGIN and_bad_rcx
    lock andq %rsi, (%rdi)
    notq %rcx
    ret
END and_bad_rcx
BEGIN and_bad_rdx
    lock andq %rsi, (%rdi)
    notq %rdx
    ret
END and_bad_rdx
BEGIN and_bad_rsi
    lock andq %rsi, (%rdi)
    notq %rsi
    ret
END and_bad_rsi
BEGIN and_bad_rdi
    lock andq %rsi, (%rdi)
    notq %rdi
    ret
END and_bad_rdi
BEGIN and_bad_rbp
    lock andq %rsi, (%rdi)
    notq %rbp
    ret
END and_bad_rbp
BEGIN and_bad_r8
    lock andq %rsi, (%rdi)
    notq %r8
    ret
END and_bad_r8
BEGIN and_bad_r9
    lock andq %rsi, (%rdi)
    notq %r9
    ret
END and_bad_r9
BEGIN and_bad_r10
    lock andq %rsi, (%rdi)
    notq %r10
    ret
END and_bad_r10
BEGIN and_bad_r11
    lock andq %rsi, (%rdi)
    notq %r11
    ret
END and_bad_r11
BEGIN and_bad_r12
    lock andq %rsi, (%rdi)
    notq %r12
    ret
END and_bad_r12
BEGIN and_bad_r13
    lock andq %rsi, (%rdi)
    notq %r13
    ret
END and_bad_r13
BEGIN and_bad_r14
    lock andq %rsi, (%rdi)
    notq %r14
    ret
END and_bad_r14
BEGIN and_bad_r15
    lock andq %rsi, (%rdi)
    notq %r15
    ret
END and_bad_r15
BEGIN and_bad_rsp
    lock andq %rsi, (%rdi)
    ret $8
END and_bad_rsp
BEGIN and_bad_guard_before
    lock andq %rsi, (%rdi)
    notb -1(%rdi)
    ret
END and_bad_guard_before
BEGIN and_bad_guard_after
    lock andq %rsi, (%rdi)
    notb 8(%rdi)
    ret
END and_bad_guard_after
BEGIN and_bad_cf
    lock andq %rsi, (%rdi)
    pushfq
    xorq $0x1, (%rsp)
    popfq
    ret
END and_bad_cf
BEGIN and_bad_pf
    lock andq %rsi, (%rdi)
    pushfq
    xorq $0x4, (%rsp)
    popfq
    ret
END and_bad_pf
BEGIN and_bad_zf
    lock andq %rsi, (%rdi)
    pushfq
    xorq $0x40, (%rsp)
    popfq
    ret
END and_bad_zf
BEGIN and_bad_sf
    lock andq %rsi, (%rdi)
    pushfq
    xorq $0x80, (%rsp)
    popfq
    ret
END and_bad_sf
BEGIN and_bad_of
    lock andq %rsi, (%rdi)
    pushfq
    xorq $0x800, (%rsp)
    popfq
    ret
END and_bad_of
BEGIN and_bad_df
    lock andq %rsi, (%rdi)
    pushfq
    xorq $0x400, (%rsp)
    popfq
    ret
END and_bad_df
BEGIN and_bad_id
    lock andq %rsi, (%rdi)
    pushfq
    xorq $0x200000, (%rsp)
    popfq
    ret
END and_bad_id
BEGIN and_bad_flags_unchanged
    pushfq
    lock andq %rsi, (%rdi)
    popfq
    ret
END and_bad_flags_unchanged
BEGIN or_af_clear
    lock orq %rsi, (%rdi)
    pushfq
    andq $-17, (%rsp)
    popfq
    ret
END or_af_clear
BEGIN or_af_set
    lock orq %rsi, (%rdi)
    pushfq
    orq $16, (%rsp)
    popfq
    ret
END or_af_set
BEGIN or_unlocked
    orq %rsi, (%rdi)
    ret
END or_unlocked
BEGIN or_bad_width32
    lock orl %esi, (%rdi)
    ret
END or_bad_width32
BEGIN or_bad_width16
    lock orw %si, (%rdi)
    ret
END or_bad_width16
BEGIN or_bad_source
    lock orq %rdx, (%rdi)
    ret
END or_bad_source
BEGIN or_bad_mask
    lock orq $1, (%rdi)
    ret
END or_bad_mask
BEGIN or_bad_operation
    lock andq %rsi, (%rdi)
    ret
END or_bad_operation
BEGIN or_bad_fetched_rax
    movq (%rdi), %rax
    lock orq %rsi, (%rdi)
    ret
END or_bad_fetched_rax
BEGIN or_bad_rax
    lock orq %rsi, (%rdi)
    notq %rax
    ret
END or_bad_rax
BEGIN or_bad_rbx
    lock orq %rsi, (%rdi)
    notq %rbx
    ret
END or_bad_rbx
BEGIN or_bad_rcx
    lock orq %rsi, (%rdi)
    notq %rcx
    ret
END or_bad_rcx
BEGIN or_bad_rdx
    lock orq %rsi, (%rdi)
    notq %rdx
    ret
END or_bad_rdx
BEGIN or_bad_rsi
    lock orq %rsi, (%rdi)
    notq %rsi
    ret
END or_bad_rsi
BEGIN or_bad_rdi
    lock orq %rsi, (%rdi)
    notq %rdi
    ret
END or_bad_rdi
BEGIN or_bad_rbp
    lock orq %rsi, (%rdi)
    notq %rbp
    ret
END or_bad_rbp
BEGIN or_bad_r8
    lock orq %rsi, (%rdi)
    notq %r8
    ret
END or_bad_r8
BEGIN or_bad_r9
    lock orq %rsi, (%rdi)
    notq %r9
    ret
END or_bad_r9
BEGIN or_bad_r10
    lock orq %rsi, (%rdi)
    notq %r10
    ret
END or_bad_r10
BEGIN or_bad_r11
    lock orq %rsi, (%rdi)
    notq %r11
    ret
END or_bad_r11
BEGIN or_bad_r12
    lock orq %rsi, (%rdi)
    notq %r12
    ret
END or_bad_r12
BEGIN or_bad_r13
    lock orq %rsi, (%rdi)
    notq %r13
    ret
END or_bad_r13
BEGIN or_bad_r14
    lock orq %rsi, (%rdi)
    notq %r14
    ret
END or_bad_r14
BEGIN or_bad_r15
    lock orq %rsi, (%rdi)
    notq %r15
    ret
END or_bad_r15
BEGIN or_bad_rsp
    lock orq %rsi, (%rdi)
    ret $8
END or_bad_rsp
BEGIN or_bad_guard_before
    lock orq %rsi, (%rdi)
    notb -1(%rdi)
    ret
END or_bad_guard_before
BEGIN or_bad_guard_after
    lock orq %rsi, (%rdi)
    notb 8(%rdi)
    ret
END or_bad_guard_after
BEGIN or_bad_cf
    lock orq %rsi, (%rdi)
    pushfq
    xorq $0x1, (%rsp)
    popfq
    ret
END or_bad_cf
BEGIN or_bad_pf
    lock orq %rsi, (%rdi)
    pushfq
    xorq $0x4, (%rsp)
    popfq
    ret
END or_bad_pf
BEGIN or_bad_zf
    lock orq %rsi, (%rdi)
    pushfq
    xorq $0x40, (%rsp)
    popfq
    ret
END or_bad_zf
BEGIN or_bad_sf
    lock orq %rsi, (%rdi)
    pushfq
    xorq $0x80, (%rsp)
    popfq
    ret
END or_bad_sf
BEGIN or_bad_of
    lock orq %rsi, (%rdi)
    pushfq
    xorq $0x800, (%rsp)
    popfq
    ret
END or_bad_of
BEGIN or_bad_df
    lock orq %rsi, (%rdi)
    pushfq
    xorq $0x400, (%rsp)
    popfq
    ret
END or_bad_df
BEGIN or_bad_id
    lock orq %rsi, (%rdi)
    pushfq
    xorq $0x200000, (%rsp)
    popfq
    ret
END or_bad_id
BEGIN or_bad_flags_unchanged
    pushfq
    lock orq %rsi, (%rdi)
    popfq
    ret
END or_bad_flags_unchanged
BEGIN xor_af_clear
    lock xorq %rsi, (%rdi)
    pushfq
    andq $-17, (%rsp)
    popfq
    ret
END xor_af_clear
BEGIN xor_af_set
    lock xorq %rsi, (%rdi)
    pushfq
    orq $16, (%rsp)
    popfq
    ret
END xor_af_set
BEGIN xor_unlocked
    xorq %rsi, (%rdi)
    ret
END xor_unlocked
BEGIN xor_bad_width32
    lock xorl %esi, (%rdi)
    ret
END xor_bad_width32
BEGIN xor_bad_width16
    lock xorw %si, (%rdi)
    ret
END xor_bad_width16
BEGIN xor_bad_source
    lock xorq %rdx, (%rdi)
    ret
END xor_bad_source
BEGIN xor_bad_mask
    lock xorq $1, (%rdi)
    ret
END xor_bad_mask
BEGIN xor_bad_operation
    lock andq %rsi, (%rdi)
    ret
END xor_bad_operation
BEGIN xor_bad_fetched_rax
    movq (%rdi), %rax
    lock xorq %rsi, (%rdi)
    ret
END xor_bad_fetched_rax
BEGIN xor_bad_rax
    lock xorq %rsi, (%rdi)
    notq %rax
    ret
END xor_bad_rax
BEGIN xor_bad_rbx
    lock xorq %rsi, (%rdi)
    notq %rbx
    ret
END xor_bad_rbx
BEGIN xor_bad_rcx
    lock xorq %rsi, (%rdi)
    notq %rcx
    ret
END xor_bad_rcx
BEGIN xor_bad_rdx
    lock xorq %rsi, (%rdi)
    notq %rdx
    ret
END xor_bad_rdx
BEGIN xor_bad_rsi
    lock xorq %rsi, (%rdi)
    notq %rsi
    ret
END xor_bad_rsi
BEGIN xor_bad_rdi
    lock xorq %rsi, (%rdi)
    notq %rdi
    ret
END xor_bad_rdi
BEGIN xor_bad_rbp
    lock xorq %rsi, (%rdi)
    notq %rbp
    ret
END xor_bad_rbp
BEGIN xor_bad_r8
    lock xorq %rsi, (%rdi)
    notq %r8
    ret
END xor_bad_r8
BEGIN xor_bad_r9
    lock xorq %rsi, (%rdi)
    notq %r9
    ret
END xor_bad_r9
BEGIN xor_bad_r10
    lock xorq %rsi, (%rdi)
    notq %r10
    ret
END xor_bad_r10
BEGIN xor_bad_r11
    lock xorq %rsi, (%rdi)
    notq %r11
    ret
END xor_bad_r11
BEGIN xor_bad_r12
    lock xorq %rsi, (%rdi)
    notq %r12
    ret
END xor_bad_r12
BEGIN xor_bad_r13
    lock xorq %rsi, (%rdi)
    notq %r13
    ret
END xor_bad_r13
BEGIN xor_bad_r14
    lock xorq %rsi, (%rdi)
    notq %r14
    ret
END xor_bad_r14
BEGIN xor_bad_r15
    lock xorq %rsi, (%rdi)
    notq %r15
    ret
END xor_bad_r15
BEGIN xor_bad_rsp
    lock xorq %rsi, (%rdi)
    ret $8
END xor_bad_rsp
BEGIN xor_bad_guard_before
    lock xorq %rsi, (%rdi)
    notb -1(%rdi)
    ret
END xor_bad_guard_before
BEGIN xor_bad_guard_after
    lock xorq %rsi, (%rdi)
    notb 8(%rdi)
    ret
END xor_bad_guard_after
BEGIN xor_bad_cf
    lock xorq %rsi, (%rdi)
    pushfq
    xorq $0x1, (%rsp)
    popfq
    ret
END xor_bad_cf
BEGIN xor_bad_pf
    lock xorq %rsi, (%rdi)
    pushfq
    xorq $0x4, (%rsp)
    popfq
    ret
END xor_bad_pf
BEGIN xor_bad_zf
    lock xorq %rsi, (%rdi)
    pushfq
    xorq $0x40, (%rsp)
    popfq
    ret
END xor_bad_zf
BEGIN xor_bad_sf
    lock xorq %rsi, (%rdi)
    pushfq
    xorq $0x80, (%rsp)
    popfq
    ret
END xor_bad_sf
BEGIN xor_bad_of
    lock xorq %rsi, (%rdi)
    pushfq
    xorq $0x800, (%rsp)
    popfq
    ret
END xor_bad_of
BEGIN xor_bad_df
    lock xorq %rsi, (%rdi)
    pushfq
    xorq $0x400, (%rsp)
    popfq
    ret
END xor_bad_df
BEGIN xor_bad_id
    lock xorq %rsi, (%rdi)
    pushfq
    xorq $0x200000, (%rsp)
    popfq
    ret
END xor_bad_id
BEGIN xor_bad_flags_unchanged
    pushfq
    lock xorq %rsi, (%rdi)
    popfq
    ret
END xor_bad_flags_unchanged
.section .note.GNU-stack,"",@progbits
