/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Single-threaded owned windows. Recovery uses only RIP-relative storage, so
 * no GPR hides a recovery pointer and RSP may be an arbitrary input or result.
 * The entire executable section, including harness and jumps, is authenticated
 * against the supplied final-ELF extraction before the first probe. */
.section .edsl_add_memory64,"ax",@progbits
.globl edsl_add_memory64_section_start
edsl_add_memory64_section_start:

.macro SNAPSHOT name
    movq %rax, \name+0(%rip)
    movq %rcx, \name+8(%rip)
    movq %rdx, \name+16(%rip)
    movq %rbx, \name+24(%rip)
    movq %rsp, \name+32(%rip)
    movq %rbp, \name+40(%rip)
    movq %rsi, \name+48(%rip)
    movq %rdi, \name+56(%rip)
    movq %r8, \name+64(%rip)
    movq %r9, \name+72(%rip)
    movq %r10, \name+80(%rip)
    movq %r11, \name+88(%rip)
    movq %r12, \name+96(%rip)
    movq %r13, \name+104(%rip)
    movq %r14, \name+112(%rip)
    movq %r15, \name+120(%rip)
.endm
.globl edsl_add_memory64_probe
.type edsl_add_memory64_probe,@function
edsl_add_memory64_probe:
    movq %rsp, host_rsp(%rip)
    movq %rbx, host_saved(%rip)
    movq %rbp, host_saved+8(%rip)
    movq %r12, host_saved+16(%rip)
    movq %r13, host_saved+24(%rip)
    movq %r14, host_saved+32(%rip)
    movq %r15, host_saved+40(%rip)
    movq %rdi, window(%rip)
    pushfq
    popq host_flags(%rip)
    pushq edsl_add_memory64_input+128(%rip)
    popfq
    pushfq
    popq edsl_add_memory64_initial+128(%rip)
    movq edsl_add_memory64_input+0(%rip), %rax
    movq edsl_add_memory64_input+8(%rip), %rcx
    movq edsl_add_memory64_input+16(%rip), %rdx
    movq edsl_add_memory64_input+24(%rip), %rbx
    movq edsl_add_memory64_input+32(%rip), %rsp
    movq edsl_add_memory64_input+40(%rip), %rbp
    movq edsl_add_memory64_input+48(%rip), %rsi
    movq edsl_add_memory64_input+56(%rip), %rdi
    movq edsl_add_memory64_input+64(%rip), %r8
    movq edsl_add_memory64_input+72(%rip), %r9
    movq edsl_add_memory64_input+80(%rip), %r10
    movq edsl_add_memory64_input+88(%rip), %r11
    movq edsl_add_memory64_input+96(%rip), %r12
    movq edsl_add_memory64_input+104(%rip), %r13
    movq edsl_add_memory64_input+112(%rip), %r14
    movq edsl_add_memory64_input+120(%rip), %r15
    SNAPSHOT edsl_add_memory64_initial
    jmp *window(%rip)
.size edsl_add_memory64_probe,.-edsl_add_memory64_probe

.type capture,@function
capture:
    SNAPSHOT edsl_add_memory64_output
    /* MOV restores the real CALL stack before PUSHFQ. No stack access has
     * occurred since installing the arbitrary RSP, even for ADD RSP,[...]. */
    movq host_rsp(%rip), %rsp
    pushfq
    popq edsl_add_memory64_output+128(%rip)
    pushq host_flags(%rip)
    popfq
    movq host_saved(%rip), %rbx
    movq host_saved+8(%rip), %rbp
    movq host_saved+16(%rip), %r12
    movq host_saved+24(%rip), %r13
    movq host_saved+32(%rip), %r14
    movq host_saved+40(%rip), %r15
    ret
.size capture,.-capture

.macro BEGIN name
.globl edsl_add_memory64_\name
.globl edsl_add_memory64_\name\()_end
.type edsl_add_memory64_\name,@function
edsl_add_memory64_\name:
.endm
.macro END name
edsl_add_memory64_\name\()_end:
    jmp capture
.size edsl_add_memory64_\name,.-edsl_add_memory64_\name
.endm
.macro PROBE name, bytes:vararg
    BEGIN \name
    .byte \bytes
    END \name
.endm
.macro BASE name,destination,base
    PROBE \name,(0x48 | ((\destination >> 3) << 2) | (\base >> 3)),0x03,(((\destination & 7) << 3) | (\base & 7))
.endm
.macro INDEX name,destination,base,index,scale
    PROBE \name,(0x48 | ((\destination >> 3) << 2) | ((\index >> 3) << 1) | (\base >> 3)),0x03,(((\destination & 7) << 3) | 4),((\scale << 6) | ((\index & 7) << 3) | (\base & 7))
.endm
/* All destinations, all twelve admitted plain bases. */
BASE plain0,0,1
BASE plain1,1,2
BASE plain2,2,3
BASE plain3,3,6
BASE plain4,4,7
BASE plain5,5,8
BASE plain6,6,9
BASE plain7,7,10
BASE plain8,8,11
BASE plain9,9,14
BASE plain10,10,15
BASE plain11,11,0
BASE plain12,12,1
BASE plain13,13,2
BASE plain14,14,3
BASE plain15,15,6
/* X is ignored without SIB, with all R/B combinations. */
PROBE ignored_x0,0x4a,0x03,0x03
PROBE ignored_x1,0x4b,0x03,0x03
PROBE ignored_x2,0x4e,0x03,0x03
PROBE ignored_x3,0x4f,0x03,0x03
.macro SCALE scale
    INDEX scale\scale\()_0,2,0,1,\scale
    INDEX scale\scale\()_1,2,8,1,\scale
    INDEX scale\scale\()_2,2,0,9,\scale
    INDEX scale\scale\()_3,2,8,9,\scale
    INDEX scale\scale\()_4,10,0,1,\scale
    INDEX scale\scale\()_5,10,8,1,\scale
    INDEX scale\scale\()_6,10,0,9,\scale
    INDEX scale\scale\()_7,10,8,9,\scale
.endm
SCALE 0
SCALE 1
SCALE 2
SCALE 3
INDEX alias_base,8,8,9,1
INDEX alias_index,9,8,9,1
INDEX same_address,10,9,9,2
INDEX alias_all,9,9,9,3
INDEX rsp_base,4,4,5,1
INDEX r12_base,4,12,13,1
INDEX r12_index,12,4,12,2
INDEX r12_all,12,12,12,0
INDEX plain_alias,0,0,1,0
BASE plain_self,15,15
/* Exact scalar sum64 instruction windows selected by GCC and Clang. */
PROBE gcc_sum,0x48,0x03,0x14,0xc7
PROBE clang_sum,0x48,0x03,0x04,0xcf

/* Safe owned semantic mutants. All data accesses remain within the padded
 * read-only page. Multi-instruction mutations preserve their scratch GPR via
 * RIP-relative storage; they are excluded from positive model replay. */
PROBE narrow32_sum_load,0x03,0x07
BEGIN narrow32_load
    movq %rcx, scratch(%rip)
    movl (%rdi), %ecx
    addq %rcx, %rax
    movq scratch(%rip), %rcx
END narrow32_load
PROBE wrong_operation,0x48,0x33,0x07
PROBE wrong_destination,0x48,0x03,0x0f
PROBE wrong_scale,0x48,0x03,0x04,0x8f
PROBE wrong_ea,0x48,0x03,0x06
BEGIN omitted_flags
    movq %rcx, scratch(%rip)
    movq (%rdi), %rcx
    leaq (%rax,%rcx), %rax
    movq scratch(%rip), %rcx
END omitted_flags
PROBE cleared_carry,0x48,0x03,0x07,0xf8
PROBE changed_nonarith,0x48,0x03,0x07,0xfd
.globl edsl_add_memory64_section_end
edsl_add_memory64_section_end:

.bss
.balign 8
host_rsp: .zero 8
host_flags: .zero 8
host_saved: .zero 48
window: .zero 8
scratch: .zero 8
.section .note.GNU-stack,"",@progbits
