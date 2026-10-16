/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* No stack access occurs while the modeled RSP is installed. The single
 * owned instruction is followed only by a direct jump to the RIP-relative
 * capture sequence. This fixture is deliberately single-threaded. */
.text
.globl edsl_moves_probe
.type edsl_moves_probe,@function
edsl_moves_probe:
    movq %rsp, edsl_moves_host_rsp(%rip)
    movq %rbx, edsl_moves_host_saved(%rip)
    movq %rbp, edsl_moves_host_saved+8(%rip)
    movq %r12, edsl_moves_host_saved+16(%rip)
    movq %r13, edsl_moves_host_saved+24(%rip)
    movq %r14, edsl_moves_host_saved+32(%rip)
    movq %r15, edsl_moves_host_saved+40(%rip)
    movq %rdi, edsl_moves_function(%rip)
    pushq edsl_moves_input+128(%rip)
    popfq
    pushfq
    popq edsl_moves_effective_flags(%rip)
    movq edsl_moves_input+0(%rip), %rax
    movq edsl_moves_input+8(%rip), %rcx
    movq edsl_moves_input+16(%rip), %rdx
    movq edsl_moves_input+24(%rip), %rbx
    movq edsl_moves_input+32(%rip), %rsp
    movq edsl_moves_input+40(%rip), %rbp
    movq edsl_moves_input+48(%rip), %rsi
    movq edsl_moves_input+56(%rip), %rdi
    movq edsl_moves_input+64(%rip), %r8
    movq edsl_moves_input+72(%rip), %r9
    movq edsl_moves_input+80(%rip), %r10
    movq edsl_moves_input+88(%rip), %r11
    movq edsl_moves_input+96(%rip), %r12
    movq edsl_moves_input+104(%rip), %r13
    movq edsl_moves_input+112(%rip), %r14
    movq edsl_moves_input+120(%rip), %r15
    jmp *edsl_moves_function(%rip)
.size edsl_moves_probe,.-edsl_moves_probe

.type edsl_moves_capture,@function
edsl_moves_capture:
    movq %rax, edsl_moves_output+0(%rip)
    movq %rcx, edsl_moves_output+8(%rip)
    movq %rdx, edsl_moves_output+16(%rip)
    movq %rbx, edsl_moves_output+24(%rip)
    movq %rsp, edsl_moves_output+32(%rip)
    movq %rbp, edsl_moves_output+40(%rip)
    movq %rsi, edsl_moves_output+48(%rip)
    movq %rdi, edsl_moves_output+56(%rip)
    movq %r8, edsl_moves_output+64(%rip)
    movq %r9, edsl_moves_output+72(%rip)
    movq %r10, edsl_moves_output+80(%rip)
    movq %r11, edsl_moves_output+88(%rip)
    movq %r12, edsl_moves_output+96(%rip)
    movq %r13, edsl_moves_output+104(%rip)
    movq %r14, edsl_moves_output+112(%rip)
    movq %r15, edsl_moves_output+120(%rip)
    movq edsl_moves_host_rsp(%rip), %rsp
    pushfq
    popq edsl_moves_output+128(%rip)
    cld
    movq edsl_moves_host_saved(%rip), %rbx
    movq edsl_moves_host_saved+8(%rip), %rbp
    movq edsl_moves_host_saved+16(%rip), %r12
    movq edsl_moves_host_saved+24(%rip), %r13
    movq edsl_moves_host_saved+32(%rip), %r14
    movq edsl_moves_host_saved+40(%rip), %r15
    ret
.size edsl_moves_capture,.-edsl_moves_capture

.bss
.balign 8
edsl_moves_host_rsp: .zero 8
edsl_moves_host_saved: .zero 48
edsl_moves_function: .zero 8

/* Keep this separate from .text so objcopy can extract precisely these final
 * linked bytes, including each capture jump, for an identity check at runtime. */
.section .edsl_moves,"ax",@progbits
.globl edsl_moves_section_start
edsl_moves_section_start:
.macro PROBE name, bytes:vararg
.globl edsl_move_\name
.globl edsl_move_\name\()_end
.type edsl_move_\name,@function
edsl_move_\name:
.byte \bytes
edsl_move_\name\()_end:
    jmp edsl_moves_capture
.size edsl_move_\name,.-edsl_move_\name
.endm

/* 89 /r: each low register occurs as both destination and source. */
PROBE r89_0, 0x89,0xc8
PROBE r89_1, 0x89,0xd1
PROBE r89_2, 0x89,0xda
PROBE r89_3, 0x89,0xe3
PROBE r89_4, 0x89,0xec
PROBE r89_5, 0x89,0xf5
PROBE r89_6, 0x89,0xfe
PROBE r89_7, 0x89,0xc7
/* 8b /r reverses the ModRM roles. */
PROBE r8b_0, 0x8b,0xc7
PROBE r8b_1, 0x8b,0xc8
PROBE r8b_2, 0x8b,0xd1
PROBE r8b_3, 0x8b,0xda
PROBE r8b_4, 0x8b,0xe3
PROBE r8b_5, 0x8b,0xec
PROBE r8b_6, 0x8b,0xf5
PROBE r8b_7, 0x8b,0xfe
PROBE self_0, 0x89,0xc0
PROBE self_1, 0x8b,0xc9
PROBE self_2, 0x89,0xd2
PROBE self_3, 0x8b,0xdb
PROBE self_4, 0x89,0xe4
PROBE self_5, 0x8b,0xed
PROBE self_6, 0x89,0xf6
PROBE self_7, 0x8b,0xff

/* Base/destination and base/source aliasing, for every plain admitted base. */
PROBE load_0, 0x8b,0x00
PROBE load_1, 0x8b,0x09
PROBE load_2, 0x8b,0x12
PROBE load_3, 0x8b,0x1b
PROBE load_6, 0x8b,0x36
PROBE load_7, 0x8b,0x3f
PROBE store_0, 0x89,0x00
PROBE store_1, 0x89,0x09
PROBE store_2, 0x89,0x12
PROBE store_3, 0x89,0x1b
PROBE store_6, 0x89,0x36
PROBE store_7, 0x89,0x3f
/* Include the old load/store successes which the legacy decoder owns first. */
PROBE legacy_load, 0x8b,0x07
PROBE legacy_store, 0x89,0x37

/* Full-width base+index at all four SIB scales. Loads alias destination/index;
 * stores alias source/base. Neither addressing register is truncated. */
PROBE sibload_0, 0x8b,0x0c,0x0f
PROBE sibload_1, 0x8b,0x0c,0x4f
PROBE sibload_2, 0x8b,0x0c,0x8f
PROBE sibload_3, 0x8b,0x0c,0xcf
PROBE sibstore_0, 0x89,0x3c,0x0f
PROBE sibstore_1, 0x89,0x3c,0x4f
PROBE sibstore_2, 0x89,0x3c,0x8f
PROBE sibstore_3, 0x89,0x3c,0xcf
/* RSP base, RBP index, destination/base and source/index aliases. */
PROBE sib_rsp_load, 0x8b,0x24,0x6c
PROBE sib_rsp_store, 0x89,0x2c,0x6c
PROBE sib_same_load, 0x8b,0x0c,0x09
PROBE sib_same_store, 0x89,0x0c,0x09

/* Safe project-owned mutations. The independent contract observer must reject
 * all of these; none is claimed supported or passed to the Lean replay. */
PROBE mutant_width, 0x48,0x89,0xd8
PROBE mutant_direction, 0x89,0xc3
PROBE mutant_omitted, 0x90,0x90
PROBE mutant_neighbor, 0x48,0x89,0x37
.globl edsl_moves_section_end
edsl_moves_section_end:
.section .note.GNU-stack,"",@progbits
