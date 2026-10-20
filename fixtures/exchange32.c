/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>
#include <stdatomic.h>

uint32_t edsl_exchange32(_Atomic uint32_t *address, uint32_t value)
{
    return atomic_exchange_explicit(address, value, memory_order_seq_cst);
}
