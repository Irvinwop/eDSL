/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>

uint64_t caller(volatile uint64_t *target, uint64_t value, uint64_t count)
{
    uint64_t result = value + count;
    if (count != 0)
        *target = result - UINT64_C(1);
    return result;
}
