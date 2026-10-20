/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Client-only full-pointer path; the direct shape checker does not admit it. */
.text
.globl edsl_store_return_rcx
.type edsl_store_return_rcx,@function
edsl_store_return_rcx:
    movq %rdi, %rcx
    movl %esi, (%rcx)
    movq %rcx, %rax
    ret
.size edsl_store_return_rcx,.-edsl_store_return_rcx
.section .note.GNU-stack,"",@progbits
