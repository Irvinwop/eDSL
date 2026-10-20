/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl edsl_cfg_call
.type edsl_cfg_call,@function
edsl_cfg_call:
    /* Harness arguments: code, a, na, b, nb, violations.
       The loaded bytes receive a, na, b, nb in SysV argument registers. */
    pushq %rbx
    pushq %rbp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    subq $40, %rsp
    movq %rdi, %r11
    movq %r9, 0(%rsp)
    movq %rsi, %rdi
    movq %rdx, %rsi
    movq %rcx, %rdx
    movq %r8, %rcx
    movabsq $0x0123456789abcdef, %rbx
    movabsq $0xfedcba9876543210, %rbp
    movabsq $0x13579bdf2468ace0, %r12
    movabsq $0xeca86420fdb97531, %r13
    movabsq $0xa55a5aa50ff0f00f, %r14
    movabsq $0x5aa5a55af00f0ff0, %r15
    movabsq $0xc01dcafefeedbeef, %rax
    movq %rax, 8(%rsp)
    movq %rsp, 16(%rsp)
    cld
    call *%r11
    /* Observe full RAX, rather than a C uint32_t return conversion. */
    xorl %r10d, %r10d
    movabsq $0x0123456789abcdef, %rdx
    cmpq %rdx, %rbx
    je 1f
    orq $1, %r10
1:  movabsq $0xfedcba9876543210, %rdx
    cmpq %rdx, %rbp
    je 2f
    orq $2, %r10
2:  movabsq $0x13579bdf2468ace0, %rdx
    cmpq %rdx, %r12
    je 3f
    orq $4, %r10
3:  movabsq $0xeca86420fdb97531, %rdx
    cmpq %rdx, %r13
    je 4f
    orq $8, %r10
4:  movabsq $0xa55a5aa50ff0f00f, %rdx
    cmpq %rdx, %r14
    je 5f
    orq $16, %r10
5:  movabsq $0x5aa5a55af00f0ff0, %rdx
    cmpq %rdx, %r15
    je 6f
    orq $32, %r10
6:  pushfq
    popq %rdx
    testq $0x400, %rdx
    je 7f
    orq $64, %r10
7:  cld
    movabsq $0xc01dcafefeedbeef, %rdx
    cmpq %rdx, 8(%rsp)
    jne 8f
    cmpq %rsp, 16(%rsp)
    je 9f
8:  orq $128, %r10
9:  movq 0(%rsp), %rdx
    movq %r10, (%rdx)
    addq $40, %rsp
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbp
    popq %rbx
    ret
.size edsl_cfg_call,.-edsl_cfg_call

/* Owned defects check that the observer sees these ABI failures. */
.globl edsl_cfg_bad_high
.type edsl_cfg_bad_high,@function
edsl_cfg_bad_high:
    movabsq $0x100000000, %rax
    ret
.size edsl_cfg_bad_high,.-edsl_cfg_bad_high
.globl edsl_cfg_bad_saved
.type edsl_cfg_bad_saved,@function
edsl_cfg_bad_saved:
    xorl %eax, %eax
    xorl %r12d, %r12d
    ret
.size edsl_cfg_bad_saved,.-edsl_cfg_bad_saved
.section .note.GNU-stack,"",@progbits
