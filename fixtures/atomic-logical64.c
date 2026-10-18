/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdatomic.h>
#include <stdint.h>

/* Owned GNU23 input. The caller supplies a live, initialized, naturally
 * aligned atomic object. The native harness supplies that actual object.
 * The old value is discarded: this void ABI makes no RAX/old64 promise.
 * Matching compiler bytes are observations, not C seq_cst preservation. */
void atomic_or64_discard(_Atomic uint64_t *target, uint64_t mask)
{
    (void)atomic_fetch_or_explicit(target, mask, memory_order_seq_cst);
}
