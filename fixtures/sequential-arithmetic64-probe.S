/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* No stack access while arbitrary modeled RSP is installed; every owned
 * register-only window jumps directly to RIP-relative snapshot capture. */
.text
.globl edsl_arithmetic_probe
.type edsl_arithmetic_probe,@function
edsl_arithmetic_probe:
    movq %rsp, edsl_arithmetic_host_rsp(%rip)
    movq %rbx, edsl_arithmetic_host_saved(%rip)
    movq %rbp, edsl_arithmetic_host_saved+8(%rip)
    movq %r12, edsl_arithmetic_host_saved+16(%rip)
    movq %r13, edsl_arithmetic_host_saved+24(%rip)
    movq %r14, edsl_arithmetic_host_saved+32(%rip)
    movq %r15, edsl_arithmetic_host_saved+40(%rip)
    movq %rdi, edsl_arithmetic_function(%rip)
    pushq edsl_arithmetic_input+128(%rip)
    popfq
    pushfq
    popq edsl_arithmetic_effective_flags(%rip)
    movq edsl_arithmetic_input+0(%rip), %rax
    movq edsl_arithmetic_input+8(%rip), %rcx
    movq edsl_arithmetic_input+16(%rip), %rdx
    movq edsl_arithmetic_input+24(%rip), %rbx
    movq edsl_arithmetic_input+32(%rip), %rsp
    movq edsl_arithmetic_input+40(%rip), %rbp
    movq edsl_arithmetic_input+48(%rip), %rsi
    movq edsl_arithmetic_input+56(%rip), %rdi
    movq edsl_arithmetic_input+64(%rip), %r8
    movq edsl_arithmetic_input+72(%rip), %r9
    movq edsl_arithmetic_input+80(%rip), %r10
    movq edsl_arithmetic_input+88(%rip), %r11
    movq edsl_arithmetic_input+96(%rip), %r12
    movq edsl_arithmetic_input+104(%rip), %r13
    movq edsl_arithmetic_input+112(%rip), %r14
    movq edsl_arithmetic_input+120(%rip), %r15
    jmp *edsl_arithmetic_function(%rip)
.size edsl_arithmetic_probe,.-edsl_arithmetic_probe

.type edsl_arithmetic_capture,@function
edsl_arithmetic_capture:
    movq %rax, edsl_arithmetic_output+0(%rip)
    movq %rcx, edsl_arithmetic_output+8(%rip)
    movq %rdx, edsl_arithmetic_output+16(%rip)
    movq %rbx, edsl_arithmetic_output+24(%rip)
    movq %rsp, edsl_arithmetic_output+32(%rip)
    movq %rbp, edsl_arithmetic_output+40(%rip)
    movq %rsi, edsl_arithmetic_output+48(%rip)
    movq %rdi, edsl_arithmetic_output+56(%rip)
    movq %r8, edsl_arithmetic_output+64(%rip)
    movq %r9, edsl_arithmetic_output+72(%rip)
    movq %r10, edsl_arithmetic_output+80(%rip)
    movq %r11, edsl_arithmetic_output+88(%rip)
    movq %r12, edsl_arithmetic_output+96(%rip)
    movq %r13, edsl_arithmetic_output+104(%rip)
    movq %r14, edsl_arithmetic_output+112(%rip)
    movq %r15, edsl_arithmetic_output+120(%rip)
    movq edsl_arithmetic_host_rsp(%rip), %rsp
    pushfq
    popq edsl_arithmetic_output+128(%rip)
    cld
    movq edsl_arithmetic_host_saved(%rip), %rbx
    movq edsl_arithmetic_host_saved+8(%rip), %rbp
    movq edsl_arithmetic_host_saved+16(%rip), %r12
    movq edsl_arithmetic_host_saved+24(%rip), %r13
    movq edsl_arithmetic_host_saved+32(%rip), %r14
    movq edsl_arithmetic_host_saved+40(%rip), %r15
    ret
.size edsl_arithmetic_capture,.-edsl_arithmetic_capture

.bss
.balign 8
edsl_arithmetic_host_rsp: .zero 8
edsl_arithmetic_host_saved: .zero 48
edsl_arithmetic_function: .zero 8

.section .edsl_arithmetic64,"ax",@progbits
.globl edsl_arithmetic_section_start
edsl_arithmetic_section_start:
.macro PROBE name, bytes:vararg
.globl edsl_arithmetic_\name
.globl edsl_arithmetic_\name\()_end
.type edsl_arithmetic_\name,@function
edsl_arithmetic_\name:
.byte \bytes
edsl_arithmetic_\name\()_end:
    jmp edsl_arithmetic_capture
.size edsl_arithmetic_\name,.-edsl_arithmetic_\name
.endm
.macro LEA_BASE name,destination,base
    PROBE \name,(0x48 | ((\destination >> 3) << 2) | (\base >> 3)),0x8d,(((\destination & 7) << 3) | (\base & 7))
.endm
.macro LEA_INDEX name,destination,base,index,scale
    PROBE \name,(0x48 | ((\destination >> 3) << 2) | ((\index >> 3) << 1) | (\base >> 3)),0x8d,(((\destination & 7) << 3) | 4),((\scale << 6) | ((\index & 7) << 3) | (\base & 7))
.endm
LEA_BASE lp0,0,1
LEA_BASE lp1,1,2
LEA_BASE lp2,2,3
LEA_BASE lp3,3,6
LEA_BASE lp4,4,7
LEA_BASE lp5,5,8
LEA_BASE lp6,6,9
LEA_BASE lp7,7,10
LEA_BASE lp8,8,11
LEA_BASE lp9,9,14
LEA_BASE lp10,10,15
LEA_BASE lp11,11,0
LEA_BASE lp12,12,1
LEA_BASE lp13,13,2
LEA_BASE lp14,14,3
LEA_BASE lp15,15,6
/* X is ignored without SIB, with every R/B combination. */
PROBE lx0,0x4a,0x8d,0x03
PROBE lx1,0x4b,0x8d,0x03
PROBE lx2,0x4e,0x8d,0x03
PROBE lx3,0x4f,0x8d,0x03
/* Every scale and every REX.R/X/B combination. */
.macro SCALE scale
    LEA_INDEX ls\scale\()_0,2,0,1,\scale
    LEA_INDEX ls\scale\()_1,2,8,1,\scale
    LEA_INDEX ls\scale\()_2,2,0,9,\scale
    LEA_INDEX ls\scale\()_3,2,8,9,\scale
    LEA_INDEX ls\scale\()_4,10,0,1,\scale
    LEA_INDEX ls\scale\()_5,10,8,1,\scale
    LEA_INDEX ls\scale\()_6,10,0,9,\scale
    LEA_INDEX ls\scale\()_7,10,8,9,\scale
.endm
SCALE 0
SCALE 1
SCALE 2
SCALE 3
LEA_INDEX lbase,8,8,9,1
LEA_INDEX lindex,9,8,9,1
LEA_INDEX lsame,10,9,9,2
LEA_INDEX lall,9,9,9,3
LEA_INDEX lrspbase,4,4,5,1
LEA_INDEX lr12base,4,12,5,1
LEA_INDEX lr12index,12,4,12,2
LEA_INDEX lr12all,12,12,12,0

.macro ADD01 name,destination,source
    PROBE \name,(0x48 | ((\source >> 3) << 2) | (\destination >> 3)),0x01,(0xc0 | ((\source & 7) << 3) | (\destination & 7))
.endm
.macro ADD03 name,destination,source
    PROBE \name,(0x48 | ((\destination >> 3) << 2) | (\source >> 3)),0x03,(0xc0 | ((\destination & 7) << 3) | (\source & 7))
.endm
ADD01 a01_0,0,1
ADD01 a01_1,1,10
ADD01 a01_2,2,3
ADD01 a01_3,3,12
ADD01 a01_4,4,5
ADD01 a01_5,5,14
ADD01 a01_6,6,7
ADD01 a01_7,7,8
ADD01 a01_8,8,9
ADD01 a01_9,9,2
ADD01 a01_10,10,11
ADD01 a01_11,11,4
ADD01 a01_12,12,13
ADD01 a01_13,13,6
ADD01 a01_14,14,15
ADD01 a01_15,15,0
ADD03 a03_0,0,15
ADD03 a03_1,1,0
ADD03 a03_2,2,9
ADD03 a03_3,3,2
ADD03 a03_4,4,11
ADD03 a03_5,5,4
ADD03 a03_6,6,13
ADD03 a03_7,7,6
ADD03 a03_8,8,7
ADD03 a03_9,9,8
ADD03 a03_10,10,1
ADD03 a03_11,11,10
ADD03 a03_12,12,3
ADD03 a03_13,13,12
ADD03 a03_14,14,5
ADD03 a03_15,15,14
.irp register,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
    ADD01 aself\register,\register,\register
.endr
/* Ignored X with every R/B combination and both opcode directions. */
PROBE ax01_0,0x4a,0x01,0xd8
PROBE ax01_1,0x4b,0x01,0xd8
PROBE ax01_2,0x4e,0x01,0xd8
PROBE ax01_3,0x4f,0x01,0xd8
PROBE ax03_0,0x4a,0x03,0xd8
PROBE ax03_1,0x4b,0x03,0xd8
PROBE ax03_2,0x4e,0x03,0xd8
PROBE ax03_3,0x4f,0x03,0xd8

/* Safe owned register-only semantic mutations; never dereference arbitrary
 * effective addresses or use the arbitrary modeled stack. */
PROBE mutant_lea_scale,0x48,0x8d,0x04,0x8b
PROBE mutant_lea_base,0x48,0x8d,0x04,0x4a
PROBE mutant_lea_width,0x8d,0x04,0x4b
PROBE mutant_lea_flags,0x48,0x8d,0x04,0x4b,0xf9
PROBE mutant_add_source,0x48,0x01,0xd0
PROBE mutant_add_width,0x01,0xc8
PROBE mutant_add_flags,0x48,0x8d,0x04,0x08
PROBE mutant_add_carry,0x48,0x01,0xc8,0xf8
PROBE mutant_add_direction,0x48,0x03,0xc8
.globl edsl_arithmetic_section_end
edsl_arithmetic_section_end:
.section .note.GNU-stack,"",@progbits
