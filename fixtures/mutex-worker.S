/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl edsl_mutex_worker
.type edsl_mutex_worker,@function
/* System V interface: RDI = aligned lock word, RSI = protected payload.
 * A successful call acquires the lock, performs two protected +1 stores,
 * releases the lock, and returns zero.  The intermediate odd value is private
 * to the critical section; the closed invariant is an even payload. */
edsl_mutex_worker:
.Lmutex_retry:
    mov $1, %eax
    xchg %eax, (%rdi)
    cmp $0, %eax
    jne .Lmutex_retry
    mov (%rsi), %eax
    lea 1(%rax), %eax
    mov %eax, (%rsi)
    lea 1(%rax), %eax
    mov %eax, (%rsi)
    mov $0, %eax
    xchg %eax, (%rdi)
    mov $0, %eax
    ret
.size edsl_mutex_worker, .-edsl_mutex_worker
.section .note.GNU-stack,"",@progbits
