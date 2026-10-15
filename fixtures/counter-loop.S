/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl edsl_counter_loop
.type edsl_counter_loop,@function
/* Register interface: RDI = shared word, RCX = unsigned 64-bit count.
 * counter-call.S adapts ordinary System V calls to this interface. */
edsl_counter_loop:
    jrcxz .Lcounter_done
.Lcounter_body:
    mov $1, %eax
    lock xadd %eax, (%rdi)
    loop .Lcounter_body
.Lcounter_done:
    mov $0, %eax
    ret
.size edsl_counter_loop, .-edsl_counter_loop
.section .note.GNU-stack,"",@progbits
