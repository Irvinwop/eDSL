/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdatomic.h>
#include <stdint.h>

/* Owned independent implementation for the callable union task. Both RMWs
 * remain real events in the model. This fixture makes no C memory-order or
 * concurrent linearizability refinement claim. */
void atomic_or64_discard_twice(_Atomic uint64_t *target, uint64_t mask)
{
    (void)atomic_fetch_or_explicit(target, mask, memory_order_seq_cst);
    (void)atomic_fetch_or_explicit(target, mask, memory_order_seq_cst);
}
