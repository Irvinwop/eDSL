/* Copyright 2026 Irvinwop
 * SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>

__attribute__((noinline))
uint64_t helper(volatile uint64_t *p, uint64_t x)
{
    *p = x;
    return *p;
}
