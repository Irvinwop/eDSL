/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* No stack access while arbitrary modeled RSP is installed; every owned
 * register-only window jumps directly to RIP-relative snapshot capture. */
.text
.globl edsl_compare32_probe
.type edsl_compare32_probe,@function
edsl_compare32_probe:
    movq %rsp, edsl_compare32_host_rsp(%rip)
    movq %rbx, edsl_compare32_host_saved(%rip)
    movq %rbp, edsl_compare32_host_saved+8(%rip)
    movq %r12, edsl_compare32_host_saved+16(%rip)
    movq %r13, edsl_compare32_host_saved+24(%rip)
    movq %r14, edsl_compare32_host_saved+32(%rip)
    movq %r15, edsl_compare32_host_saved+40(%rip)
    movq %rdi, edsl_compare32_function(%rip)
    pushq edsl_compare32_input+128(%rip)
    popfq
    pushfq
    popq edsl_compare32_effective_flags(%rip)
    movq edsl_compare32_input+0(%rip), %rax
    movq edsl_compare32_input+8(%rip), %rcx
    movq edsl_compare32_input+16(%rip), %rdx
    movq edsl_compare32_input+24(%rip), %rbx
    movq edsl_compare32_input+32(%rip), %rsp
    movq edsl_compare32_input+40(%rip), %rbp
    movq edsl_compare32_input+48(%rip), %rsi
    movq edsl_compare32_input+56(%rip), %rdi
    movq edsl_compare32_input+64(%rip), %r8
    movq edsl_compare32_input+72(%rip), %r9
    movq edsl_compare32_input+80(%rip), %r10
    movq edsl_compare32_input+88(%rip), %r11
    movq edsl_compare32_input+96(%rip), %r12
    movq edsl_compare32_input+104(%rip), %r13
    movq edsl_compare32_input+112(%rip), %r14
    movq edsl_compare32_input+120(%rip), %r15
    jmp *edsl_compare32_function(%rip)
.size edsl_compare32_probe,.-edsl_compare32_probe

.type edsl_compare32_capture,@function
edsl_compare32_capture:
    movq %rax, edsl_compare32_output+0(%rip)
    movq %rcx, edsl_compare32_output+8(%rip)
    movq %rdx, edsl_compare32_output+16(%rip)
    movq %rbx, edsl_compare32_output+24(%rip)
    movq %rsp, edsl_compare32_output+32(%rip)
    movq %rbp, edsl_compare32_output+40(%rip)
    movq %rsi, edsl_compare32_output+48(%rip)
    movq %rdi, edsl_compare32_output+56(%rip)
    movq %r8, edsl_compare32_output+64(%rip)
    movq %r9, edsl_compare32_output+72(%rip)
    movq %r10, edsl_compare32_output+80(%rip)
    movq %r11, edsl_compare32_output+88(%rip)
    movq %r12, edsl_compare32_output+96(%rip)
    movq %r13, edsl_compare32_output+104(%rip)
    movq %r14, edsl_compare32_output+112(%rip)
    movq %r15, edsl_compare32_output+120(%rip)
    movq edsl_compare32_host_rsp(%rip), %rsp
    pushfq
    popq edsl_compare32_output+128(%rip)
    cld
    movq edsl_compare32_host_saved(%rip), %rbx
    movq edsl_compare32_host_saved+8(%rip), %rbp
    movq edsl_compare32_host_saved+16(%rip), %r12
    movq edsl_compare32_host_saved+24(%rip), %r13
    movq edsl_compare32_host_saved+32(%rip), %r14
    movq edsl_compare32_host_saved+40(%rip), %r15
    ret
.size edsl_compare32_capture,.-edsl_compare32_capture

.bss
.balign 8
edsl_compare32_host_rsp: .zero 8
edsl_compare32_host_saved: .zero 48
edsl_compare32_function: .zero 8

.section .edsl_compare32,"ax",@progbits
.globl edsl_compare32_section_start
edsl_compare32_section_start:
.macro PROBE name, bytes:vararg
.globl edsl_compare32_\name
.globl edsl_compare32_\name\()_end
.type edsl_compare32_\name,@function
edsl_compare32_\name:
.byte \bytes
edsl_compare32_\name\()_end:
    jmp edsl_compare32_capture
.size edsl_compare32_\name,.-edsl_compare32_\name
.endm
/* Non-W REX extends R/B; X is intentionally ignored for mod=3. The C
 * contracts below are specified independently of these encoding macros. */
.macro PAIR name,opcode,left,right,reverse=0
.if \reverse
    PROBE \name,(0x40 | ((\left >> 3) << 2) | (\right >> 3)),\opcode,(0xc0 | ((\left & 7) << 3) | (\right & 7))
.else
    PROBE \name,(0x40 | ((\right >> 3) << 2) | (\left >> 3)),\opcode,(0xc0 | ((\right & 7) << 3) | (\left & 7))
.endif
.endm
.macro OPERATION name,opcode,reverse=0
    .irp reg,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
        PAIR \name\()_pair\reg,\opcode,\reg,((\reg + 1) % 16),\reverse
        PAIR \name\()_self\reg,\opcode,\reg,\reg,\reverse
    .endr
    .irp rex,0,1,2,3,4,5,6,7
        PROBE \name\()_rex\rex,(0x40 + \rex),\opcode,0xd8
    .endr
    .irp reg,0,1,2,3,4,5,6,7
.if \reverse
        PROBE \name\()_plain\reg,\opcode,(0xc0 | (\reg << 3) | ((\reg + 1) % 8))
.else
        PROBE \name\()_plain\reg,\opcode,(0xc0 | (((\reg + 1) % 8) << 3) | \reg)
.endif
    .endr
.endm
OPERATION cmp39,0x39
OPERATION cmp3b,0x3b,1
OPERATION test85,0x85
PROBE endbr,0xf3,0x0f,0x1e,0xfa
PROBE nop1,0x90
PROBE nop2,0x66,0x90
PROBE nop3,0x0f,0x1f,0x00
PROBE nop4,0x0f,0x1f,0x40,0x00
PROBE nop5,0x0f,0x1f,0x44,0x00,0x00
/* Owned safe synthetic mutations; none accesses the modeled stack or RAM. */
PROBE mutant_cmp_width,0x48,0x39,0xc8
PROBE mutant_cmp_direction,0x3b,0xc8
PROBE mutant_cmp_register,0x39,0xd0
PROBE mutant_cmp_write,0x29,0xc8
PROBE mutant_cmp_flags,0x39,0xc8,0xf8
PROBE mutant_test_width,0x48,0x85,0xc8
PROBE mutant_test_register,0x85,0xd0
PROBE mutant_test_write,0x21,0xc8
PROBE mutant_test_flags,0x85,0xc8,0xf9
PROBE mutant_nop_write,0x89,0xc0
PROBE mutant_nop_flags,0xf9
.globl edsl_compare32_section_end
edsl_compare32_section_end:
.section .note.GNU-stack,"",@progbits
