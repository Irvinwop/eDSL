/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>

/* Owned GNU C compiler fixture. The empty GNU asm count-register barrier keeps
 * the selected GCC13 -Os loop shape. It emits no instruction, but deliberately
 * prevents the compiler from deriving the loop count across that point.
 * Verification concerns the selected final bytes, not C volatile semantics,
 * source preservation, physical atomicity, or arbitrary compiler versions. */
uint64_t publish_counted(volatile uint64_t *target, uint64_t value, uint64_t count)
{
    while (count != 0) {
        __asm__ volatile ("" : "+r" (count));
        ++value;
        *target = value;
        --count;
    }
    return value;
}
