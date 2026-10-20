/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>
extern uint64_t helper(volatile uint64_t *, uint64_t);
uint64_t caller(volatile uint64_t *target, uint64_t value, uint64_t count)
{
    while (count != 0) {
        value = helper(target, value) + UINT64_C(1);
        --count;
    }
    return value;
}
