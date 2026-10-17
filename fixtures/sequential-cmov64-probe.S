/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* No stack access while arbitrary modeled RSP is installed; every owned
 * register-only window jumps directly to RIP-relative snapshot capture. */
.text
.globl edsl_cmov_probe
.type edsl_cmov_probe,@function
edsl_cmov_probe:
    movq %rsp, edsl_cmov_host_rsp(%rip)
    movq %rbx, edsl_cmov_host_saved(%rip)
    movq %rbp, edsl_cmov_host_saved+8(%rip)
    movq %r12, edsl_cmov_host_saved+16(%rip)
    movq %r13, edsl_cmov_host_saved+24(%rip)
    movq %r14, edsl_cmov_host_saved+32(%rip)
    movq %r15, edsl_cmov_host_saved+40(%rip)
    movq %rdi, edsl_cmov_function(%rip)
    pushq edsl_cmov_input+128(%rip)
    popfq
    pushfq
    popq edsl_cmov_effective_flags(%rip)
    movq edsl_cmov_input+0(%rip), %rax
    movq edsl_cmov_input+8(%rip), %rcx
    movq edsl_cmov_input+16(%rip), %rdx
    movq edsl_cmov_input+24(%rip), %rbx
    movq edsl_cmov_input+32(%rip), %rsp
    movq edsl_cmov_input+40(%rip), %rbp
    movq edsl_cmov_input+48(%rip), %rsi
    movq edsl_cmov_input+56(%rip), %rdi
    movq edsl_cmov_input+64(%rip), %r8
    movq edsl_cmov_input+72(%rip), %r9
    movq edsl_cmov_input+80(%rip), %r10
    movq edsl_cmov_input+88(%rip), %r11
    movq edsl_cmov_input+96(%rip), %r12
    movq edsl_cmov_input+104(%rip), %r13
    movq edsl_cmov_input+112(%rip), %r14
    movq edsl_cmov_input+120(%rip), %r15
    jmp *edsl_cmov_function(%rip)
.size edsl_cmov_probe,.-edsl_cmov_probe

.type edsl_cmov_capture,@function
edsl_cmov_capture:
    movq %rax, edsl_cmov_output+0(%rip)
    movq %rcx, edsl_cmov_output+8(%rip)
    movq %rdx, edsl_cmov_output+16(%rip)
    movq %rbx, edsl_cmov_output+24(%rip)
    movq %rsp, edsl_cmov_output+32(%rip)
    movq %rbp, edsl_cmov_output+40(%rip)
    movq %rsi, edsl_cmov_output+48(%rip)
    movq %rdi, edsl_cmov_output+56(%rip)
    movq %r8, edsl_cmov_output+64(%rip)
    movq %r9, edsl_cmov_output+72(%rip)
    movq %r10, edsl_cmov_output+80(%rip)
    movq %r11, edsl_cmov_output+88(%rip)
    movq %r12, edsl_cmov_output+96(%rip)
    movq %r13, edsl_cmov_output+104(%rip)
    movq %r14, edsl_cmov_output+112(%rip)
    movq %r15, edsl_cmov_output+120(%rip)
    movq edsl_cmov_host_rsp(%rip), %rsp
    pushfq
    popq edsl_cmov_output+128(%rip)
    cld
    movq edsl_cmov_host_saved(%rip), %rbx
    movq edsl_cmov_host_saved+8(%rip), %rbp
    movq edsl_cmov_host_saved+16(%rip), %r12
    movq edsl_cmov_host_saved+24(%rip), %r13
    movq edsl_cmov_host_saved+32(%rip), %r14
    movq edsl_cmov_host_saved+40(%rip), %r15
    ret
.size edsl_cmov_capture,.-edsl_cmov_capture

.bss
.balign 8
edsl_cmov_host_rsp: .zero 8
edsl_cmov_host_saved: .zero 48
edsl_cmov_function: .zero 8

.section .edsl_cmov64,"ax",@progbits
.globl edsl_cmov_section_start
edsl_cmov_section_start:
.macro PROBE name, bytes:vararg
.globl edsl_cmov_\name
.globl edsl_cmov_\name\()_end
.type edsl_cmov_\name,@function
edsl_cmov_\name:
.byte \bytes
edsl_cmov_\name\()_end:
    jmp edsl_cmov_capture
.size edsl_cmov_\name,.-edsl_cmov_\name
.endm
.macro CMOV name,condition,destination,source
    PROBE \name,(0x48 | ((\destination >> 3) << 2) | (\source >> 3)),0x0f,(0x40 | \condition),(0xc0 | ((\destination & 7) << 3) | (\source & 7))
.endm
/* All condition opcodes; independent C requests name the semantic condition. */
CMOV c_o,0,0,9
CMOV c_no,1,0,9
CMOV c_b,2,0,9
CMOV c_ae,3,0,9
CMOV c_e,4,0,9
CMOV c_ne,5,0,9
CMOV c_be,6,0,9
CMOV c_a,7,0,9
CMOV c_s,8,0,9
CMOV c_ns,9,0,9
CMOV c_p,10,0,9
CMOV c_np,11,0,9
CMOV c_l,12,0,9
CMOV c_ge,13,0,9
CMOV c_le,14,0,9
CMOV c_g,15,0,9
/* Every destination/source, both R/B banks, and RSP on either side. */
CMOV b0,0,0,1
CMOV b1,1,1,10
CMOV b2,2,2,3
CMOV b3,3,3,12
CMOV b4,4,4,5
CMOV b5,5,5,14
CMOV b6,6,6,7
CMOV b7,7,7,8
CMOV b8,8,8,9
CMOV b9,9,9,2
CMOV b10,10,10,11
CMOV b11,11,11,4
CMOV b12,12,12,13
CMOV b13,13,13,6
CMOV b14,14,14,15
CMOV b15,15,15,0
/* All self aliases, including arbitrary modeled RSP. */
.irp register,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
    CMOV s\register,\register,\register,\register
.endr
/* Ignored X for each R/B combination, bringing coverage to every REX.W byte. */
PROBE x0,0x4a,0x0f,0x44,0xcb
PROBE x1,0x4b,0x0f,0x44,0xcb
PROBE x2,0x4e,0x0f,0x44,0xcb
PROBE x3,0x4f,0x0f,0x44,0xcb

/* Safe owned register-only mutations. No instruction dereferences arbitrary
 * data addresses or uses the arbitrary modeled stack before capture. */
PROBE mutant_condition,0x49,0x0f,0x45,0xc1
PROBE mutant_direction,0x4c,0x0f,0x44,0xc8
PROBE mutant_width,0x41,0x0f,0x44,0xc1
PROBE mutant_flags,0x49,0x0f,0x44,0xc1,0xf9
PROBE mutant_false_rsp,0x4c,0x89,0xcc
PROBE mutant_source,0x49,0x0f,0x44,0xc2
.globl edsl_cmov_section_end
edsl_cmov_section_end:
.section .note.GNU-stack,"",@progbits
