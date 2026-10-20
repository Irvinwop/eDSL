/* Copyright 2026 Irvinwop
 * SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>

uint64_t caller(uint64_t *p, uint64_t x)
{
    *p = x;
    return x + UINT64_C(1);
}
