/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>
/* Volatile keeps the load in this owned compiler fixture. Verification targets
 * the final bytes; no C volatile, atomicity or source-preservation claim follows. */
uint64_t store_load64(volatile uint64_t *pointer, uint64_t value)
{
    *pointer = value;
    return *pointer;
}
