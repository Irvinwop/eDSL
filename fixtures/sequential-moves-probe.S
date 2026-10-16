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

/* Assembler-selected 89 register copies: every destination and source, with
 * low/high bank combinations exercising REX.R and REX.B independently. */
.macro QWORD_PROBE name, source, destination
.globl edsl_move_\name
.globl edsl_move_\name\()_end
.type edsl_move_\name,@function
edsl_move_\name:
    movq \source, \destination
edsl_move_\name\()_end:
    jmp edsl_moves_capture
.size edsl_move_\name,.-edsl_move_\name
.endm
QWORD_PROBE q89_0, %rcx, %rax
QWORD_PROBE q89_1, %r10, %rcx
QWORD_PROBE q89_2, %rbx, %rdx
QWORD_PROBE q89_3, %r12, %rbx
QWORD_PROBE q89_4, %rbp, %rsp
QWORD_PROBE q89_5, %r14, %rbp
QWORD_PROBE q89_6, %rdi, %rsi
QWORD_PROBE q89_7, %r8, %rdi
QWORD_PROBE q89_8, %r9, %r8
QWORD_PROBE q89_9, %rdx, %r9
QWORD_PROBE q89_10, %r11, %r10
QWORD_PROBE q89_11, %rsp, %r11
QWORD_PROBE q89_12, %r13, %r12
QWORD_PROBE q89_13, %rsi, %r13
QWORD_PROBE q89_14, %r15, %r14
QWORD_PROBE q89_15, %rax, %r15

/* Alternate 8B encodings with explicit requested operands in the C contracts.
 * The same ModRM fields reverse direction compared with the 89 windows. */
PROBE q8b_0, 0x49,0x8b,0xc7 /* rax <- r15 */
PROBE q8b_1, 0x48,0x8b,0xc8 /* rcx <- rax */
PROBE q8b_2, 0x49,0x8b,0xd1 /* rdx <- r9 */
PROBE q8b_3, 0x48,0x8b,0xda /* rbx <- rdx */
PROBE q8b_4, 0x49,0x8b,0xe3 /* rsp <- r11 */
PROBE q8b_5, 0x48,0x8b,0xec /* rbp <- rsp */
PROBE q8b_6, 0x49,0x8b,0xf5 /* rsi <- r13 */
PROBE q8b_7, 0x48,0x8b,0xfe /* rdi <- rsi */
PROBE q8b_8, 0x4c,0x8b,0xc7 /* r8 <- rdi */
PROBE q8b_9, 0x4d,0x8b,0xc8 /* r9 <- r8 */
PROBE q8b_10, 0x4c,0x8b,0xd1 /* r10 <- rcx */
PROBE q8b_11, 0x4d,0x8b,0xda /* r11 <- r10 */
PROBE q8b_12, 0x4c,0x8b,0xe3 /* r12 <- rbx */
PROBE q8b_13, 0x4d,0x8b,0xec /* r13 <- r12 */
PROBE q8b_14, 0x4c,0x8b,0xf5 /* r14 <- rbp */
PROBE q8b_15, 0x4d,0x8b,0xfe /* r15 <- r14 */

/* Full64 self-copies preserve high halves, including arbitrary RSP. */
QWORD_PROBE qself_0, %rax, %rax
QWORD_PROBE qself_1, %rcx, %rcx
QWORD_PROBE qself_2, %rdx, %rdx
QWORD_PROBE qself_3, %rbx, %rbx
QWORD_PROBE qself_4, %rsp, %rsp
QWORD_PROBE qself_5, %rbp, %rbp
QWORD_PROBE qself_6, %rsi, %rsi
QWORD_PROBE qself_7, %rdi, %rdi
QWORD_PROBE qself_8, %r8, %r8
QWORD_PROBE qself_9, %r9, %r9
QWORD_PROBE qself_10, %r10, %r10
QWORD_PROBE qself_11, %r11, %r11
QWORD_PROBE qself_12, %r12, %r12
QWORD_PROBE qself_13, %r13, %r13
QWORD_PROBE qself_14, %r14, %r14
QWORD_PROBE qself_15, %r15, %r15

/* REX.X is ignored in register mode for each R/B combination and direction.
 * Together with the assembler windows, all prefix bytes 48..4F execute. */
PROBE qx89_low, 0x4a,0x89,0xd8 /* rax <- rbx */
PROBE qx89_b, 0x4b,0x89,0xd8 /* r8 <- rbx */
PROBE qx89_r, 0x4e,0x89,0xd8 /* rax <- r11 */
PROBE qx89_rb, 0x4f,0x89,0xd8 /* r8 <- r11 */
PROBE qx8b_low, 0x4a,0x8b,0xd8 /* rbx <- rax */
PROBE qx8b_b, 0x4b,0x8b,0xd8 /* rbx <- r8 */
PROBE qx8b_r, 0x4e,0x8b,0xd8 /* r11 <- rax */
PROBE qx8b_rb, 0x4f,0x8b,0xd8 /* r11 <- r8 */

/* Safe project-owned mutations. The independent contract observer must reject
 * all of these and none is passed to the positive Lean replay. Some bytes now
 * decode successfully but violate their independently requested width. */
PROBE mutant_width, 0x48,0x89,0xd8
PROBE mutant_direction, 0x89,0xc3
PROBE mutant_omitted, 0x90,0x90
PROBE mutant_neighbor, 0x48,0x89,0x37
PROBE mutant_narrow, 0x89,0xd8 /* requested rax <- full64 rbx, executed eax <- ebx */
.globl edsl_moves_section_end
edsl_moves_section_end:
.section .note.GNU-stack,"",@progbits
