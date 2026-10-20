/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Single-threaded RIP-relative instrumentation. No stack access between
 * installing modeled RSP and restoring host RSP. Every GPR is captured before
 * ANY scratch use. MOV/LEA/JMP preserve the as-yet-uncaptured ADD flags. */
.macro STORE_RF target
    movq %rax, \target+0(%rip)
    movq %rcx, \target+8(%rip)
    movq %rdx, \target+16(%rip)
    movq %rbx, \target+24(%rip)
    movq %rsp, \target+32(%rip)
    movq %rbp, \target+40(%rip)
    movq %rsi, \target+48(%rip)
    movq %rdi, \target+56(%rip)
    movq %r8, \target+64(%rip)
    movq %r9, \target+72(%rip)
    movq %r10, \target+80(%rip)
    movq %r11, \target+88(%rip)
    movq %r12, \target+96(%rip)
    movq %r13, \target+104(%rip)
    movq %r14, \target+112(%rip)
    movq %r15, \target+120(%rip)
.endm
.macro LOAD_RF source
    movq \source+0(%rip), %rax
    movq \source+8(%rip), %rcx
    movq \source+16(%rip), %rdx
    movq \source+24(%rip), %rbx
    movq \source+32(%rip), %rsp
    movq \source+40(%rip), %rbp
    movq \source+48(%rip), %rsi
    movq \source+56(%rip), %rdi
    movq \source+64(%rip), %r8
    movq \source+72(%rip), %r9
    movq \source+80(%rip), %r10
    movq \source+88(%rip), %r11
    movq \source+96(%rip), %r12
    movq \source+104(%rip), %r13
    movq \source+112(%rip), %r14
    movq \source+120(%rip), %r15
.endm
.text
.globl edsl_ladd_probe
.type edsl_ladd_probe,@function
edsl_ladd_probe:
    STORE_RF edsl_ladd_host
    movq %rdi, edsl_ladd_target(%rip)
    movq %rdi, edsl_ladd_before+136(%rip)
    pushfq
    popq edsl_ladd_host+128(%rip)
    /* Seed and capture effective user RFLAGS while host SP is still valid. */
    pushq edsl_ladd_input+128(%rip)
    popfq
    pushfq
    popq edsl_ladd_before+128(%rip)
    LOAD_RF edsl_ladd_input
    STORE_RF edsl_ladd_before
    jmp *edsl_ladd_target(%rip)
.size edsl_ladd_probe,.-edsl_ladd_probe

.type edsl_ladd_recover,@function
edsl_ladd_recover:
    /* All RF and RIP have already been captured by the window. */
    movq edsl_ladd_host+32(%rip), %rsp
    pushfq
    popq edsl_ladd_after+128(%rip)
    pushq edsl_ladd_host+128(%rip)
    popfq
    LOAD_RF edsl_ladd_host
    ret
.size edsl_ladd_recover,.-edsl_ladd_recover

/* Independently exercise System V nonvolatile registers and exact stack
 * restoration on every call. These checks run AFTER the CPU capture. */
.globl edsl_ladd_checked_call
.type edsl_ladd_checked_call,@function
edsl_ladd_checked_call:
    pushq %rbx
    pushq %rbp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    pushq %rdi
    movq %rsp, edsl_ladd_driver_sp(%rip)
    movabsq $0x89abcdef01234567, %rbx
    movabsq $0x76543210fedcba98, %rbp
    movabsq $0x8000000000000001, %r12
    movabsq $0xfedcba9876543210, %r13
    movabsq $0x0123456789abcdef, %r14
    movabsq $0xffff00000000ffff, %r15
    call edsl_ladd_probe
    cmpq edsl_ladd_driver_sp(%rip), %rsp
    jne .Labi_bad
.macro CHECK_NV register, value
    movabsq $\value, %rax
    cmpq %rax, %\register
    jne .Labi_bad
.endm
    CHECK_NV rbx, 0x89abcdef01234567
    CHECK_NV rbp, 0x76543210fedcba98
    CHECK_NV r12, 0x8000000000000001
    CHECK_NV r13, 0xfedcba9876543210
    CHECK_NV r14, 0x0123456789abcdef
    CHECK_NV r15, 0xffff00000000ffff
    movl $1, %eax
    jmp .Labi_return
.Labi_bad:
    movl $0, %eax
.Labi_return:
    movq edsl_ladd_driver_sp(%rip), %rsp
    popq %rdi
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbp
    popq %rbx
    ret
.size edsl_ladd_checked_call,.-edsl_ladd_checked_call

.bss
.balign 8
edsl_ladd_host: .zero 144
edsl_ladd_target: .zero 8
edsl_ladd_driver_sp: .zero 8

/* The entire executable section, including recovery jumps, is extracted
 * and compared with these linked bytes before any owned probe executes. */
.section .edsl_locked_add64,"ax",@progbits
.globl edsl_ladd_section_begin
edsl_ladd_section_begin:
.macro WINDOW source, base, ignored_x
.Lprobe_\source\()_\base\()_\ignored_x:
    .byte 0xf0, (0x48 | ((\source >> 3) << 2) | (\ignored_x << 1) | (\base >> 3))
    .byte 0x0f, 0xc1, (((\source & 7) << 3) | (\base & 7))
.Lpost_\source\()_\base\()_\ignored_x:
    STORE_RF edsl_ladd_after
    /* Hardware RIP-relative address of the actual five-byte continuation;
     * no expected pre-PC+5 value is assigned by the C++ harness. */
    leaq .Lpost_\source\()_\base\()_\ignored_x(%rip), %rax
    movq %rax, edsl_ladd_after+136(%rip)
    jmp edsl_ladd_recover
    .pushsection .data.rel.ro,"aw",@progbits
    .quad .Lprobe_\source\()_\base\()_\ignored_x
    .quad .Lpost_\source\()_\base\()_\ignored_x
    .quad \source, \base, \ignored_x
    .popsection
.endm

.pushsection .data.rel.ro,"aw",@progbits
.balign 8
.globl edsl_ladd_windows
edsl_ladd_windows:
.popsection
.irp source,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
    .irp base,0,1,2,3,6,7,8,9,10,11,14,15
        .irp ignored_x,0,1
            WINDOW \source, \base, \ignored_x
        .endr
    .endr
.endr
.globl edsl_ladd_section_end
edsl_ladd_section_end:
.pushsection .data.rel.ro,"aw",@progbits
.globl edsl_ladd_windows_end
edsl_ladd_windows_end:
.popsection
.section .note.GNU-stack,"",@progbits
