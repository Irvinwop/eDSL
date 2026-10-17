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
.globl cm_root_capture_end
cm_root_capture_end:
.size cm_root_capture, .-cm_root_capture
.size cm_run, .-cm_run

/* Exact complete texts from the separately compiled, linked cold probe. */
.section .edsl_call_memory_loop64,"ax",@progbits
.macro EXPORT name
    .globl \name
\name:
.endm
EXPORT cm_gcc
    .byte 0x55,0x48,0x89,0xfd,0x53,0x48,0x89,0xd3,0x51,0x48,0x85,0xdb,0x74,0x11
    .byte 0x48,0x89,0xef,0x48,0xff,0xcb,0xe8,0x0d,0,0,0,0x48,0x8d,0x70,1,0xeb,0xea
    .byte 0x5a,0x48,0x89,0xf0,0x5b,0x5d,0xc3
    .byte 0x48,0x89,0x37,0x48,0x8b,0x07,0xc3
EXPORT cm_gcc_end
EXPORT cm_clang
    .byte 0x48,0x89,0xf0,0x48,0x85,0xd2,0x74,0x24,0x41,0x56,0x53,0x50,0x48,0x89
    .byte 0xd3,0x49,0x89,0xfe,0x4c,0x89,0xf7,0x48,0x89,0xc6,0xe8,0x10,0,0,0,0x48
    .byte 0xff,0xc0,0x48,0xff,0xcb,0x75,0xed,0x48,0x83,0xc4,8,0x5b,0x41,0x5e,0xc3
    .byte 0x48,0x89,0x37,0x48,0x8b,0x07,0xc3
EXPORT cm_clang_end

/* Owned safe negatives. Every DATA access stays in the mapped DATA page. */
.section .edsl_call_memory_loop64_mutants,"ax",@progbits
/* The nonzero test counts are bounded; every access remains in owned RAM.
 * These have the same S-32 high-water mark as the actual compiler callers. */
.macro MUTANT name, variant
    EXPORT \name
    pushq %rbp
    movq %rdi, %rbp
    pushq %rbx
    movq %rdx, %rbx
    pushq %rcx
.if \variant == 0
    decq %rbx                 /* skip exactly one iteration, tested with n=3 */
.endif
.Ltest\@:
    testq %rbx, %rbx
    jz .Ldone\@
    movq %rbp, %rdi
    decq %rbx
    call \name\()_helper
    leaq 1(%rax), %rsi
    jmp .Ltest\@
.Ldone\@:
    popq %rdx
    movq %rsi, %rax
    popq %rbx
    popq %rbp
.if \variant == 4
    xorq $1, %rbx
.endif
    ret
    EXPORT \name\()_helper
.if \variant == 1
    movq %rsi, %rax           /* no store, but retain the correct return value */
.elseif \variant == 2
    movq (%rdi), %rax         /* read the stale word, tested with n=1 */
    movq %rsi, (%rdi)
.else
    movq %rsi, (%rdi)
    movq (%rdi), %rax
.if \variant == 3
    notb 8(%rdi)              /* n=3: changes the neighbor, inside the DATA page */
.endif
.endif
    ret
    EXPORT \name\()_end
.endm
MUTANT cm_bad_skip, 0
MUTANT cm_bad_no_store, 1
MUTANT cm_bad_stale, 2
MUTANT cm_bad_outside, 3
MUTANT cm_bad_rbx, 4
.section .note.GNU-stack,"",@progbits
