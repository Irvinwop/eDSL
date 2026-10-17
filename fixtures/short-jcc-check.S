/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Single-threaded observer. No arbitrary stack, function or bytes are accepted
 * from the command line: the C caller selects only these owned static stubs. */
.text
.globl edsl_short_jcc_probe
.type edsl_short_jcc_probe,@function
edsl_short_jcc_probe:
    pushfq
    popq edsl_short_jcc_host_flags(%rip)
    subq $8, %rsp
    movq %rdi, edsl_short_jcc_function(%rip)
    movq edsl_short_jcc_host_flags(%rip), %rax
    andq $~(0x8d5 | 0x400 | 0x200000), %rax
    orq %rsi, %rax
    pushq %rax
    popfq
    pushfq
    popq edsl_short_jcc_observation+8(%rip)
    call *edsl_short_jcc_function(%rip)
    movq %rax, edsl_short_jcc_observation(%rip)
    pushfq
    popq edsl_short_jcc_observation+16(%rip)
    pushq edsl_short_jcc_host_flags(%rip)
    popfq
    leaq 8(%rsp), %rsp
    ret
.size edsl_short_jcc_probe,.-edsl_short_jcc_probe
.bss
.balign 8
edsl_short_jcc_host_flags: .zero 8
edsl_short_jcc_function: .zero 8

.section .edsl_short_jcc,"ax",@progbits
.globl edsl_short_jcc_images_begin
edsl_short_jcc_images_begin:
/* Every path uses only LEA and RET after the tested branch. RAX records the
 * address actually reached, rather than an assigned Boolean answer. */
.macro LABEL name, suffix
.globl edsl_short_jcc_\name\()_\suffix
edsl_short_jcc_\name\()_\suffix:
.endm
.macro PATH name, suffix
LABEL \name,\suffix
.L\name\()_\suffix:
    leaq edsl_short_jcc_\name\()_\suffix(%rip), %rax
    ret
.endm
.macro FORWARD name, mnemonic
.balign 16
LABEL \name,begin
LABEL \name,entry
LABEL \name,branch
    \mnemonic .L\name\()_taken
PATH \name,fallthrough
    .fill 119,1,0x90
LABEL \name,physical_taken
PATH \name,taken
LABEL \name,end
.endm
.macro BACKWARD name, mnemonic
.balign 16
LABEL \name,begin
LABEL \name,physical_taken
PATH \name,taken
    .fill 118,1,0x90
LABEL \name,entry
LABEL \name,branch
    \mnemonic .L\name\()_taken
PATH \name,fallthrough
LABEL \name,end
.endm
.macro BOTH name, mnemonic
FORWARD \name\()_forward,\mnemonic
BACKWARD \name\()_backward,\mnemonic
.endm
/* Named assembly mnemonics are intentionally separate from the C Boolean
 * condition oracle. The runner inspects the actual linked rel8 encodings. */
BOTH overflow,jo
BOTH not_overflow,jno
BOTH below,jb
BOTH above_equal,jae
BOTH equal,je
BOTH not_equal,jne
BOTH below_equal,jbe
BOTH above,ja
BOTH sign,js
BOTH not_sign,jns
BOTH parity,jp
BOTH not_parity,jnp
BOTH less,jl
BOTH greater_equal,jge
BOTH less_equal,jle
BOTH greater,jg

/* Owned synthetic defects. Their encoded destinations are always safe paths,
 * and their contracts still request the original JO +127 behavior. */
FORWARD bad_inverse,jno
.balign 16
LABEL bad_displacement,begin
LABEL bad_displacement,entry
LABEL bad_displacement,branch
    jo .Lbad_displacement_wrong
PATH bad_displacement,fallthrough
    .fill 111,1,0x90
LABEL bad_displacement,physical_taken
PATH bad_displacement,wrong
PATH bad_displacement,taken
LABEL bad_displacement,end
.balign 16
LABEL bad_flags,begin
LABEL bad_flags,entry
    cmc /* JO ignores CF, so this changes only the requested frame. */
LABEL bad_flags,branch
    jo .Lbad_flags_taken
PATH bad_flags,fallthrough
    .fill 119,1,0x90
LABEL bad_flags,physical_taken
PATH bad_flags,taken
LABEL bad_flags,end
.globl edsl_short_jcc_images_end
edsl_short_jcc_images_end:
.section .note.GNU-stack,"",@progbits
