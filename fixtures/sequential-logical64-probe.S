/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* No stack access while arbitrary modeled RSP is installed; every owned
 * register-only window jumps directly to RIP-relative snapshot capture. */
.text
.globl edsl_logical_probe
.type edsl_logical_probe,@function
edsl_logical_probe:
    movq %rsp, edsl_logical_host_rsp(%rip)
    movq %rbx, edsl_logical_host_saved(%rip)
    movq %rbp, edsl_logical_host_saved+8(%rip)
    movq %r12, edsl_logical_host_saved+16(%rip)
    movq %r13, edsl_logical_host_saved+24(%rip)
    movq %r14, edsl_logical_host_saved+32(%rip)
    movq %r15, edsl_logical_host_saved+40(%rip)
    movq %rdi, edsl_logical_function(%rip)
    pushq edsl_logical_input+128(%rip)
    popfq
    pushfq
    popq edsl_logical_effective_flags(%rip)
    movq edsl_logical_input+0(%rip), %rax
    movq edsl_logical_input+8(%rip), %rcx
    movq edsl_logical_input+16(%rip), %rdx
    movq edsl_logical_input+24(%rip), %rbx
    movq edsl_logical_input+32(%rip), %rsp
    movq edsl_logical_input+40(%rip), %rbp
    movq edsl_logical_input+48(%rip), %rsi
    movq edsl_logical_input+56(%rip), %rdi
    movq edsl_logical_input+64(%rip), %r8
    movq edsl_logical_input+72(%rip), %r9
    movq edsl_logical_input+80(%rip), %r10
    movq edsl_logical_input+88(%rip), %r11
    movq edsl_logical_input+96(%rip), %r12
    movq edsl_logical_input+104(%rip), %r13
    movq edsl_logical_input+112(%rip), %r14
    movq edsl_logical_input+120(%rip), %r15
    jmp *edsl_logical_function(%rip)
.size edsl_logical_probe,.-edsl_logical_probe

.type edsl_logical_capture,@function
edsl_logical_capture:
    movq %rax, edsl_logical_output+0(%rip)
    movq %rcx, edsl_logical_output+8(%rip)
    movq %rdx, edsl_logical_output+16(%rip)
    movq %rbx, edsl_logical_output+24(%rip)
    movq %rsp, edsl_logical_output+32(%rip)
    movq %rbp, edsl_logical_output+40(%rip)
    movq %rsi, edsl_logical_output+48(%rip)
    movq %rdi, edsl_logical_output+56(%rip)
    movq %r8, edsl_logical_output+64(%rip)
    movq %r9, edsl_logical_output+72(%rip)
    movq %r10, edsl_logical_output+80(%rip)
    movq %r11, edsl_logical_output+88(%rip)
    movq %r12, edsl_logical_output+96(%rip)
    movq %r13, edsl_logical_output+104(%rip)
    movq %r14, edsl_logical_output+112(%rip)
    movq %r15, edsl_logical_output+120(%rip)
    movq edsl_logical_host_rsp(%rip), %rsp
    pushfq
    popq edsl_logical_output+128(%rip)
    cld
    movq edsl_logical_host_saved(%rip), %rbx
    movq edsl_logical_host_saved+8(%rip), %rbp
    movq edsl_logical_host_saved+16(%rip), %r12
    movq edsl_logical_host_saved+24(%rip), %r13
    movq edsl_logical_host_saved+32(%rip), %r14
    movq edsl_logical_host_saved+40(%rip), %r15
    ret
.size edsl_logical_capture,.-edsl_logical_capture

.bss
.balign 8
edsl_logical_host_rsp: .zero 8
edsl_logical_host_saved: .zero 48
edsl_logical_function: .zero 8

.section .edsl_logical64,"ax",@progbits
.globl edsl_logical_section_start
edsl_logical_section_start:
.macro PROBE name, bytes:vararg
.globl edsl_logical_\name
.globl edsl_logical_\name\()_end
.type edsl_logical_\name,@function
edsl_logical_\name:
.byte \bytes
edsl_logical_\name\()_end:
    jmp edsl_logical_capture
.size edsl_logical_\name,.-edsl_logical_\name
.endm
/* Intel SDM revision 093, AND 3-60/61, OR 4-163/164, XOR 6-40/41.
 * REX.W promotes to 64 bits; REX.R/B select banks, X is unused for mod=3.
 * These encodings are deliberately separate from the requested-op C oracle. */
.macro MR name,opcode,destination,source
    PROBE \name,(0x48 | ((\source >> 3) << 2) | (\destination >> 3)),\opcode,(0xc0 | ((\source & 7) << 3) | (\destination & 7))
.endm
.macro RM name,opcode,destination,source
    PROBE \name,(0x48 | ((\destination >> 3) << 2) | (\source >> 3)),\opcode,(0xc0 | ((\destination & 7) << 3) | (\source & 7))
.endm
.macro OPERATION name,mr,rm
    MR \name\()_mr0,\mr,0,1
    MR \name\()_mr1,\mr,1,10
    MR \name\()_mr2,\mr,2,3
    MR \name\()_mr3,\mr,3,12
    MR \name\()_mr4,\mr,4,5
    MR \name\()_mr5,\mr,5,14
    MR \name\()_mr6,\mr,6,7
    MR \name\()_mr7,\mr,7,8
    MR \name\()_mr8,\mr,8,9
    MR \name\()_mr9,\mr,9,2
    MR \name\()_mr10,\mr,10,11
    MR \name\()_mr11,\mr,11,4
    MR \name\()_mr12,\mr,12,13
    MR \name\()_mr13,\mr,13,6
    MR \name\()_mr14,\mr,14,15
    MR \name\()_mr15,\mr,15,0
    RM \name\()_rm0,\rm,0,15
    RM \name\()_rm1,\rm,1,0
    RM \name\()_rm2,\rm,2,9
    RM \name\()_rm3,\rm,3,2
    RM \name\()_rm4,\rm,4,11
    RM \name\()_rm5,\rm,5,4
    RM \name\()_rm6,\rm,6,13
    RM \name\()_rm7,\rm,7,6
    RM \name\()_rm8,\rm,8,7
    RM \name\()_rm9,\rm,9,8
    RM \name\()_rm10,\rm,10,1
    RM \name\()_rm11,\rm,11,10
    RM \name\()_rm12,\rm,12,3
    RM \name\()_rm13,\rm,13,12
    RM \name\()_rm14,\rm,14,5
    RM \name\()_rm15,\rm,15,14
    .irp reg,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
        MR \name\()_selfmr\reg,\mr,\reg,\reg
        RM \name\()_selfrm\reg,\rm,\reg,\reg
    .endr
    /* Ignored X with every R/B combination, for both opcode directions. */
    PROBE \name\()_xmr0,0x4a,\mr,0xd8
    PROBE \name\()_xmr1,0x4b,\mr,0xd8
    PROBE \name\()_xmr2,0x4e,\mr,0xd8
    PROBE \name\()_xmr3,0x4f,\mr,0xd8
    PROBE \name\()_xrm0,0x4a,\rm,0xd8
    PROBE \name\()_xrm1,0x4b,\rm,0xd8
    PROBE \name\()_xrm2,0x4e,\rm,0xd8
    PROBE \name\()_xrm3,0x4f,\rm,0xd8
.endm
OPERATION band,0x21,0x23
OPERATION bor,0x09,0x0b
OPERATION bxor,0x31,0x33

/* Owned safe register-only mutations. All contracts request destination RAX,
 * source RCX. Narrowing changes upper halves; direction changes the written
 * register; STC breaks a defined output flag. None touches the installed RSP. */
PROBE mutant_band_operation,0x48,0x09,0xc8
PROBE mutant_band_direction,0x48,0x23,0xc8
PROBE mutant_band_source,0x48,0x21,0xd0
PROBE mutant_band_width,0x21,0xc8
PROBE mutant_band_flags,0x48,0x21,0xc8,0xf9
PROBE mutant_bor_operation,0x48,0x31,0xc8
PROBE mutant_bor_direction,0x48,0x0b,0xc8
PROBE mutant_bor_source,0x48,0x09,0xd0
PROBE mutant_bor_width,0x09,0xc8
PROBE mutant_bor_flags,0x48,0x09,0xc8,0xf9
PROBE mutant_bxor_operation,0x48,0x21,0xc8
PROBE mutant_bxor_direction,0x48,0x33,0xc8
PROBE mutant_bxor_source,0x48,0x31,0xd0
PROBE mutant_bxor_width,0x31,0xc8
PROBE mutant_bxor_flags,0x48,0x31,0xc8,0xf9
.globl edsl_logical_section_end
edsl_logical_section_end:
.section .note.GNU-stack,"",@progbits
