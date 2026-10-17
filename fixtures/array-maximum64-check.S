/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Single-threaded observer on the real aligned SysV stack. Recovery state is
 * RIP-relative: none of the tested GPRs carries a recovery pointer. Even the
 * owned RET $8 mutant can return safely before the host RSP is restored. */
.text
.globl edsl_array_maximum64_probe
.type edsl_array_maximum64_probe,@function
edsl_array_maximum64_probe:
    pushfq
    popq edsl_array_maximum64_host_flags(%rip)
    pushq %rbx
    pushq %rbp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    subq $8, %rsp
    movq %rsp, edsl_array_maximum64_host_rsp(%rip)
    movq %rdi, edsl_array_maximum64_function(%rip)

    /* Request all CF/PF/AF/ZF/SF/OF profiles and both ID values; leave other
     * flags at effective host values. DF must be clear at every SysV call. */
    movq edsl_array_maximum64_host_flags(%rip), %rax
    andq $-2100438, %rax /* ~(0x8d5 | 0x200000 | 0x400) */
    orq edsl_array_maximum64_input+104(%rip), %rax
    pushq %rax
    popfq
    pushfq
    popq edsl_array_maximum64_output+120(%rip)
    movq edsl_array_maximum64_input+24(%rip), %rbx
    movq edsl_array_maximum64_input+32(%rip), %rbp
    movq edsl_array_maximum64_input+40(%rip), %r12
    movq edsl_array_maximum64_input+48(%rip), %r13
    movq edsl_array_maximum64_input+56(%rip), %r14
    movq edsl_array_maximum64_input+64(%rip), %r15
    movq edsl_array_maximum64_input+72(%rip), %r8
    movq edsl_array_maximum64_input+80(%rip), %r9
    movq edsl_array_maximum64_input+88(%rip), %r10
    movq edsl_array_maximum64_input+96(%rip), %r11
    movq edsl_array_maximum64_input+0(%rip), %rdi
    movq edsl_array_maximum64_input+8(%rip), %rsi
    movq edsl_array_maximum64_input+16(%rip), %rdx
    movq edsl_array_maximum64_input+24(%rip), %rcx
    movq edsl_array_maximum64_input+16(%rip), %rax
    movq %rsp, edsl_array_maximum64_output+104(%rip)
    call *edsl_array_maximum64_function(%rip)

    /* Only MOVs until PUSHFQ: capture the real returned state and recover the
     * host stack even if RET changed its adjustment. No C runs with mutant DF. */
    movq %rax, edsl_array_maximum64_output+0(%rip)
    movq %rbx, edsl_array_maximum64_output+8(%rip)
    movq %rbp, edsl_array_maximum64_output+16(%rip)
    movq %r12, edsl_array_maximum64_output+24(%rip)
    movq %r13, edsl_array_maximum64_output+32(%rip)
    movq %r14, edsl_array_maximum64_output+40(%rip)
    movq %r15, edsl_array_maximum64_output+48(%rip)
    movq %rdi, edsl_array_maximum64_output+56(%rip)
    movq %rsi, edsl_array_maximum64_output+64(%rip)
    movq %r8, edsl_array_maximum64_output+72(%rip)
    movq %r9, edsl_array_maximum64_output+80(%rip)
    movq %r10, edsl_array_maximum64_output+88(%rip)
    movq %r11, edsl_array_maximum64_output+96(%rip)
    movq %rsp, edsl_array_maximum64_output+112(%rip)
    movq edsl_array_maximum64_host_rsp(%rip), %rsp
    pushfq
    popq edsl_array_maximum64_output+128(%rip)
    pushq edsl_array_maximum64_host_flags(%rip)
    popfq
    leaq 8(%rsp), %rsp
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbp
    popq %rbx
    ret
.size edsl_array_maximum64_probe,.-edsl_array_maximum64_probe

.bss
.balign 8
edsl_array_maximum64_host_flags: .zero 8
edsl_array_maximum64_host_rsp: .zero 8
edsl_array_maximum64_function: .zero 8

/* Assemble in the evidence directory. Each slot is the complete extracted
 * final ELF .text, already gated against the recorded compiler byte profile.
 * C checks every extraction against its slot AND that profile before probes. */
.section .edsl_array_maximum64,"ax",@progbits
.macro FINAL name, file
.balign 16
.globl edsl_array_maximum64_\name
.globl edsl_array_maximum64_\name\()_end
.type edsl_array_maximum64_\name,@function
edsl_array_maximum64_\name:
.incbin "\file"
edsl_array_maximum64_\name\()_end:
.size edsl_array_maximum64_\name,.-edsl_array_maximum64_\name
.endm
FINAL gcc,gcc/function.bin
FINAL clang,clang/function.bin

/* Owned synthetic defects only. These receive owned, writable, padded arrays,
 * or a null base with count zero. No mutant intentionally faults or overreads.
 * The correct loop below isolates frame/flag defects; C uses a separate oracle. */
.text
.macro BEGIN name
.globl edsl_array_maximum64_\name
.type edsl_array_maximum64_\name,@function
edsl_array_maximum64_\name:
.endm
.macro END name
.size edsl_array_maximum64_\name,.-edsl_array_maximum64_\name
.endm
.macro MAXIMUM
    xorl %edx, %edx
    xorl %eax, %eax
.Ltest\@:
    cmpq %rsi, %rdx
    jae .Ldone\@
    movq (%rdi,%rdx,8), %rcx
    cmpq %rcx, %rax
    cmovbq %rcx, %rax
    incq %rdx
    jmp .Ltest\@
.Ldone\@:
.endm
BEGIN bad_direction
    xorl %eax, %eax
    testq %rsi, %rsi
    jz .Ldirection_done
    movq (%rdi), %rax
    movl $1, %edx
.Ldirection_loop:
    cmpq %rsi, %rdx
    jae .Ldirection_done
    movq (%rdi,%rdx,8), %rcx
    cmpq %rcx, %rax
    cmovaq %rcx, %rax
    incq %rdx
    jmp .Ldirection_loop
.Ldirection_done:
    ret
END bad_direction
BEGIN bad_signedness
    xorl %edx, %edx
    xorl %eax, %eax
.Lsigned_loop:
    cmpq %rsi, %rdx
    jae .Lsigned_done
    movq (%rdi,%rdx,8), %rcx
    cmpq %rcx, %rax
    cmovlq %rcx, %rax
    incq %rdx
    jmp .Lsigned_loop
.Lsigned_done:
    ret
END bad_signedness
BEGIN bad_narrowing
    xorl %edx, %edx
    xorl %eax, %eax
.Lnarrow_loop:
    cmpq %rsi, %rdx
    jae .Lnarrow_done
    movl (%rdi,%rdx,8), %ecx
    cmpl %ecx, %eax
    cmovbl %ecx, %eax
    incq %rdx
    jmp .Lnarrow_loop
.Lnarrow_done:
    ret
END bad_narrowing
BEGIN bad_skip_last
    xorl %eax, %eax
    testq %rsi, %rsi
    jz .Lskip_done
    pushq %rsi
    decq %rsi
    MAXIMUM
    popq %rsi
.Lskip_done:
    ret
END bad_skip_last
BEGIN bad_zero
    xorl %eax, %eax
    ret
END bad_zero
BEGIN bad_membership
    movq $-1, %rax
    ret
END bad_membership
BEGIN bad_empty
    testq %rsi, %rsi
    jnz .Lempty_nonempty
    movl $1, %eax
    ret
.Lempty_nonempty:
    MAXIMUM
    ret
END bad_empty
BEGIN bad_data
    MAXIMUM
    xorq $1, (%rdi)
    ret
END bad_data
.macro BAD_GPR name, register
BEGIN \name
    MAXIMUM
    xorq \register, \register
    ret
END \name
.endm
BAD_GPR bad_rbx,%rbx
BAD_GPR bad_rbp,%rbp
BAD_GPR bad_r12,%r12
BAD_GPR bad_r13,%r13
BAD_GPR bad_r14,%r14
BAD_GPR bad_r15,%r15
BAD_GPR bad_rdi,%rdi
BAD_GPR bad_rsi,%rsi
BAD_GPR bad_r8,%r8
BAD_GPR bad_r9,%r9
BAD_GPR bad_r10,%r10
BAD_GPR bad_r11,%r11
BEGIN bad_rsp
    MAXIMUM
    ret $8
END bad_rsp
BEGIN bad_df
    MAXIMUM
    std
    ret
END bad_df
BEGIN bad_id
    MAXIMUM
    pushfq
    xorq $0x200000, (%rsp)
    popfq
    ret
END bad_id
.section .note.GNU-stack,"",@progbits
