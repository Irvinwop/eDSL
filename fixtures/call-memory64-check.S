/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Single-threaded capture; every recovery address is RIP-relative. */
.text
.globl cm_run
.type cm_run,@function
cm_run:
    movq %rsp, cm_host_rsp(%rip)
    movq %rbx, cm_host_saved+0(%rip)
    movq %rbp, cm_host_saved+8(%rip)
    movq %r12, cm_host_saved+16(%rip)
    movq %r13, cm_host_saved+24(%rip)
    movq %r14, cm_host_saved+32(%rip)
    movq %r15, cm_host_saved+40(%rip)
    pushfq
    popq cm_host_flags(%rip)
    pushq cm_requested_flags(%rip)
    popfq
    pushfq
    popq cm_before_flags(%rip)
    movq cm_requested+0(%rip), %rax
    movq cm_requested+8(%rip), %rcx
    movq cm_requested+16(%rip), %rdx
    movq cm_requested+24(%rip), %rbx
    movq cm_requested+40(%rip), %rbp
    movq cm_requested+48(%rip), %rsi
    movq cm_requested+56(%rip), %rdi
    movq cm_requested+64(%rip), %r8
    movq cm_requested+72(%rip), %r9
    movq cm_requested+80(%rip), %r10
    movq cm_requested+88(%rip), %r11
    movq cm_requested+96(%rip), %r12
    movq cm_requested+104(%rip), %r13
    movq cm_requested+112(%rip), %r14
    movq cm_requested+120(%rip), %r15
    movq cm_requested+32(%rip), %rsp
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
    SNAPSHOT cm_before
    jmp *cm_target(%rip)
.globl cm_root_capture
.type cm_root_capture,@function
cm_root_capture:
    SNAPSHOT cm_after
    movq $1, cm_reached(%rip)
    movq cm_host_rsp(%rip), %rsp
    /* MOV preserves the flags being observed. Restore host DF before C. */
    pushfq
    popq cm_after_flags(%rip)
    pushq cm_host_flags(%rip)
    popfq
    movq cm_host_saved+0(%rip), %rbx
    movq cm_host_saved+8(%rip), %rbp
    movq cm_host_saved+16(%rip), %r12
    movq cm_host_saved+24(%rip), %r13
    movq cm_host_saved+32(%rip), %r14
    movq cm_host_saved+40(%rip), %r15
    ret
.size cm_root_capture, .-cm_root_capture
.size cm_run, .-cm_run

/* Exact complete texts from the separately compiled, linked cold probe. */
.section .edsl_call_memory,"ax",@progbits
.macro EXPORT name
    .globl \name
\name:
.endm
EXPORT cm_gcc
    .byte 0x50,0xe8,0x05,0x00,0x00,0x00,0x5a,0x48,0xff,0xc0,0xc3
    .byte 0x48,0x89,0x37,0x48,0x8b,0x07,0xc3
EXPORT cm_gcc_end
EXPORT cm_clang
    .byte 0x50,0xe8,0x05,0x00,0x00,0x00,0x48,0xff,0xc0,0x59,0xc3
    .byte 0x48,0x89,0x37,0x48,0x8b,0x07,0xc3
EXPORT cm_clang_end

/* Owned safe negatives. Every DATA access stays in the mapped DATA page. */
.section .edsl_call_memory_mutants,"ax",@progbits
.macro MUTANT name, helper
    EXPORT \name
    pushq %rax
    call \helper
    incq %rax
    popq %rcx
    ret
    EXPORT \name\()_end
.endm
MUTANT cm_bad_no_store, .Lload_only
MUTANT cm_bad_stale, .Lstale
MUTANT cm_bad_outside, .Loutside
EXPORT cm_bad_rbx
    pushq %rax
    call .Lgood
    incq %rax
    popq %rcx
    xorq $1, %rbx
    ret
EXPORT cm_bad_rbx_end
.Lgood:
    movq %rsi, (%rdi)
    movq (%rdi), %rax
    ret
.Lload_only:
    movq (%rdi), %rax
    ret
.Lstale:
    movq (%rdi), %rax
    movq %rsi, (%rdi)
    ret
.Loutside:
    movq %rsi, 8(%rdi)
    movq (%rdi), %rax
    ret
.section .note.GNU-stack,"",@progbits
