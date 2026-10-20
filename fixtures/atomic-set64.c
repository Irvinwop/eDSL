/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdatomic.h>
#include <stdint.h>

/* Owned GNU23 compiler inputs; native observations do not prove that the
 * compiler preserves the C memory model. The old value is discarded. */
void atomic_and64_discard(_Atomic uint64_t *target, uint64_t mask)
{
    (void)atomic_fetch_and_explicit(target, mask, memory_order_seq_cst);
}
void atomic_or64_discard(_Atomic uint64_t *target, uint64_t mask)
{
    (void)atomic_fetch_or_explicit(target, mask, memory_order_seq_cst);
}
void atomic_xor64_discard(_Atomic uint64_t *target, uint64_t mask)
{
    (void)atomic_fetch_xor_explicit(target, mask, memory_order_seq_cst);
}
