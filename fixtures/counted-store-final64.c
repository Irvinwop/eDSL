/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>

/* Owned compiler fixture with a single final positive-count store. The empty
 * GNU asm count-register barrier keeps the selected compiler loop shapes.
 * Verification concerns final bytes, not C/volatile/asm source preservation. */
uint64_t publish_final(volatile uint64_t *target, uint64_t value, uint64_t count)
{
    if (count == 0) return value;
    do {
        __asm__ volatile ("" : "+r" (count));
        ++value;
        --count;
    } while (count != 0);
    *target = value;
    return value;
}
