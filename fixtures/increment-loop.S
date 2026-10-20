/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#ifndef EDSL_LOOP_INCREMENT
#define EDSL_LOOP_INCREMENT 1
#endif
.text
.globl edsl_increment_loop
.type edsl_increment_loop, @function
/* System V input RDI=value and RCX=count (fourth integer argument).
   RSI/RDX are unused. This is an owned assembly fixture, not a C lowering. */
edsl_increment_loop:
    movl %edi, %eax
    jrcxz .Ldone
.Lbody:
    leal EDSL_LOOP_INCREMENT(%rax), %eax
    loop .Lbody
.Ldone:
    ret
.size edsl_increment_loop, .-edsl_increment_loop
.section .note.GNU-stack,"",@progbits
