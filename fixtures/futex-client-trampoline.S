/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl edsl_futex_client_publish
.type edsl_futex_client_publish,@function
edsl_futex_client_publish:
    /* External SysV shim: preserve the caller's callee-saved registers, then
       establish RDI=W, RSI=P and zero every other general register except RSP.
       The CALL installs the real protected-return analogue for the exact stub. */
    pushq %rbx
    pushq %rbp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    subq $8, %rsp
    xorl %ebx, %ebx
    xorl %ebp, %ebp
    xorl %r12d, %r12d
    xorl %r13d, %r13d
    xorl %r14d, %r14d
    xorl %r15d, %r15d
    xorl %ecx, %ecx
    xorl %edx, %edx
    xorl %r8d, %r8d
    xorl %r9d, %r9d
    xorl %r10d, %r10d
    xorl %r11d, %r11d
    xorl %eax, %eax
    call edsl_futex_publish_stub
    addq $8, %rsp
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbp
    popq %rbx
    ret
.size edsl_futex_client_publish,.-edsl_futex_client_publish

/* Native observation helper only; this is outside the publication certificate.
   Use the raw full RAX result rather than libc's errno translation. */
.globl edsl_futex_client_wait0
.type edsl_futex_client_wait0,@function
edsl_futex_client_wait0:
    movl $202, %eax
    movl $128, %esi
    xorl %edx, %edx
    xorl %r10d, %r10d
    xorl %r8d, %r8d
    xorl %r9d, %r9d
    syscall
    ret
.size edsl_futex_client_wait0,.-edsl_futex_client_wait0
.section .note.GNU-stack,"",@progbits
