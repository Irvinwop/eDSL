/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Single-threaded observer. No recovery pointer is hidden in a test GPR. */
.text
.globl cs_run
.type cs_run,@function
cs_run:
    movq %rsp, cs_host_rsp(%rip)
    movq %rbx, cs_host_saved+0(%rip)
    movq %rbp, cs_host_saved+8(%rip)
    movq %r12, cs_host_saved+16(%rip)
    movq %r13, cs_host_saved+24(%rip)
    movq %r14, cs_host_saved+32(%rip)
    movq %r15, cs_host_saved+40(%rip)
    pushfq
    popq cs_host_flags(%rip)
    pushq cs_requested_flags(%rip)
    popfq
    pushfq
    popq cs_before_flags(%rip)
    movq cs_requested+0(%rip), %rax
    movq cs_requested+8(%rip), %rcx
    movq cs_requested+16(%rip), %rdx
    movq cs_requested+24(%rip), %rbx
    movq cs_requested+40(%rip), %rbp
    movq cs_requested+48(%rip), %rsi
    movq cs_requested+56(%rip), %rdi
    movq cs_requested+64(%rip), %r8
    movq cs_requested+72(%rip), %r9
    movq cs_requested+80(%rip), %r10
    movq cs_requested+88(%rip), %r11
    movq cs_requested+96(%rip), %r12
    movq cs_requested+104(%rip), %r13
    movq cs_requested+112(%rip), %r14
    movq cs_requested+120(%rip), %r15
    movq cs_requested+32(%rip), %rsp
.macro SNAPSHOT name
    movq %rax, \name+0(%rip)
    movq %rcx, \name+8(%rip)
    movq %rdx, \name+16(%rip)
    movq %rbx, \name+24(%rip)
    movq %rsp, \name+32(%rip)
    movq %rbp, \name+40(%rip)
    movq %rsi, \name+48(%rip)
    movq %rdi, \name+56(%rip)
    movq %r8, \name+64(%rip)
    movq %r9, \name+72(%rip)
    movq %r10, \name+80(%rip)
    movq %r11, \name+88(%rip)
    movq %r12, \name+96(%rip)
    movq %r13, \name+104(%rip)
    movq %r14, \name+112(%rip)
    movq %r15, \name+120(%rip)
.endm
    SNAPSHOT cs_before
    jmp *cs_target(%rip)
.globl cs_root_capture
.type cs_root_capture,@function
cs_root_capture:
    /* RET $8 is safe: no stack access until the host RSP is restored. */
    SNAPSHOT cs_after
    movq $1, cs_reached(%rip)
    movq cs_host_rsp(%rip), %rsp
    /* All instructions since RET were MOV; these are the actual post flags. */
    pushfq
    popq cs_after_flags(%rip)
    pushq cs_host_flags(%rip)
    popfq
    movq cs_host_saved+0(%rip), %rbx
    movq cs_host_saved+8(%rip), %rbp
    movq cs_host_saved+16(%rip), %r12
    movq cs_host_saved+24(%rip), %r13
    movq cs_host_saved+32(%rip), %r14
    movq cs_host_saved+40(%rip), %r15
    ret
.size cs_root_capture, .-cs_root_capture
.size cs_run, .-cs_run

/* Whole final texts from the cold probe. Internal PC-relative CALLs need no
 * relocation. End labels, rather than a first-RET search, bound every slot. */
.section .edsl_calls,"ax",@progbits
.macro EXPORT name
    .globl \name
\name:
.endm
EXPORT cs_gcc_same
EXPORT cs_gcc_same_helper
    .byte 0x48,0x8d,0x47,0x01,0xc3
EXPORT cs_gcc_same_entry
    .byte 0xe8,0xf6,0xff,0xff,0xff
EXPORT cs_gcc_same_cont
    .byte 0x48,0xff,0xc0,0xc3
EXPORT cs_gcc_same_end

EXPORT cs_gcc_separate
EXPORT cs_gcc_separate_entry
    .byte 0x50,0xe8,0x05,0x00,0x00,0x00
EXPORT cs_gcc_separate_cont
    .byte 0x5a,0x48,0xff,0xc0,0xc3
EXPORT cs_gcc_separate_helper
    .byte 0x48,0x8d,0x47,0x01,0xc3
EXPORT cs_gcc_separate_end

EXPORT cs_clang_same
EXPORT cs_clang_same_helper
    .byte 0x48,0x8d,0x47,0x01,0xc3
EXPORT cs_clang_same_entry
    .byte 0x50,0xe8,0xf5,0xff,0xff,0xff
EXPORT cs_clang_same_cont
    .byte 0x48,0xff,0xc0,0x59,0xc3
EXPORT cs_clang_same_end

EXPORT cs_clang_separate
EXPORT cs_clang_separate_entry
    .byte 0x50,0xe8,0x05,0x00,0x00,0x00
EXPORT cs_clang_separate_cont
    .byte 0x48,0xff,0xc0,0x59,0xc3
EXPORT cs_clang_separate_helper
    .byte 0x48,0x8d,0x47,0x01,0xc3
EXPORT cs_clang_separate_end

/* Synthetic owned mutations. All memory accesses stay in the owned page.
 * Mutations are judged by the common contract, not positive slot RA patterns. */
.section .edsl_call_mutants,"ax",@progbits
EXPORT cs_mutants_begin
.macro NESTED name, helper=.Lgood_helper
    EXPORT \name
    .type \name,@function
    pushq %rax
    call \helper
    incq %rax
    popq %rcx
.endm
.macro END_MUTANT name
    .size \name, .-\name
    EXPORT \name\()_end
.endm
NESTED cs_bad_missing_helper,.Lzero_helper
    ret
END_MUTANT cs_bad_missing_helper
NESTED cs_bad_plus_three
    incq %rax
    ret
END_MUTANT cs_bad_plus_three
NESTED cs_bad_narrow
    movl %eax, %eax
    ret
END_MUTANT cs_bad_narrow
NESTED cs_bad_rbx
    xorq $1, %rbx
    ret
END_MUTANT cs_bad_rbx
NESTED cs_bad_r12
    xorq $1, %r12
    ret
END_MUTANT cs_bad_r12
NESTED cs_bad_outside
    xorb $1, -24(%rsp)
    ret
END_MUTANT cs_bad_outside
NESTED cs_bad_rsp
    ret $8
END_MUTANT cs_bad_rsp
NESTED cs_bad_df
    std
    ret
END_MUTANT cs_bad_df
NESTED cs_bad_id
    pushfq
    xorq $0x200000, (%rsp)
    popfq
    ret
END_MUTANT cs_bad_id
EXPORT cs_mutant_good_helper
.Lgood_helper:
    leaq 1(%rdi), %rax
    ret
EXPORT cs_mutant_zero_helper
.Lzero_helper:
    movq %rdi, %rax
    ret
EXPORT cs_mutants_end
.section .note.GNU-stack,"",@progbits
