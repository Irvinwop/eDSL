/* Copyright 2026 Irvinwop
 * SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>

extern uint64_t helper(volatile uint64_t *p, uint64_t x);

__attribute__((noinline))
uint64_t caller(volatile uint64_t *p, uint64_t x)
{
    return helper(p, x) + UINT64_C(1);
}
