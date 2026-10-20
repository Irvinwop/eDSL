/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdatomic.h>
#include <stdint.h>

/* Owned GNU23 input, compiled independently for each selected implementation.
 * These are uninterrupted callable observations; multiple atomic source
 * operations retain their individual events. No compound-call atomicity or
 * source memory-order preservation is asserted. */
#ifndef EDSL_IMPLEMENTATION
#error EDSL_IMPLEMENTATION must select one owned implementation
#endif

void atomic_set64_grading(_Atomic uint64_t *target, uint64_t mask)
{
#if EDSL_IMPLEMENTATION == 0
    (void)atomic_fetch_and_explicit(target, mask, memory_order_seq_cst);
#elif EDSL_IMPLEMENTATION == 1
    (void)atomic_fetch_or_explicit(target, mask, memory_order_seq_cst);
#elif EDSL_IMPLEMENTATION == 2
    (void)atomic_fetch_xor_explicit(target, mask, memory_order_seq_cst);
#elif EDSL_IMPLEMENTATION == 3
    (void)atomic_fetch_and_explicit(target, mask, memory_order_seq_cst);
    (void)atomic_fetch_and_explicit(target, mask, memory_order_seq_cst);
#elif EDSL_IMPLEMENTATION == 4
    (void)atomic_fetch_or_explicit(target, mask, memory_order_seq_cst);
    (void)atomic_fetch_or_explicit(target, mask, memory_order_seq_cst);
#elif EDSL_IMPLEMENTATION == 5
    (void)atomic_fetch_xor_explicit(target, mask, memory_order_seq_cst);
    (void)atomic_fetch_xor_explicit(target, mask, memory_order_seq_cst);
    (void)atomic_fetch_xor_explicit(target, mask, memory_order_seq_cst);
#elif EDSL_IMPLEMENTATION == 6
    (void)atomic_fetch_xor_explicit(target, mask, memory_order_seq_cst);
    (void)atomic_fetch_xor_explicit(target, mask, memory_order_seq_cst);
    (void)atomic_fetch_or_explicit(target, mask, memory_order_seq_cst);
#else
#error unsupported EDSL_IMPLEMENTATION
#endif
}
