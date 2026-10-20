/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stddef.h>
#include <stdint.h>

/* The alternate stride is an owned negative input for the independent oracle. */
#ifndef EDSL_CFG_STRIDE
#define EDSL_CFG_STRIDE 2
#endif

__attribute__((noinline)) uint32_t sum_stride(const uint32_t *p, size_t n)
{
    uint32_t result = 0;
    while (n != 0) {
        result += *p;
        p += EDSL_CFG_STRIDE;
        --n;
    }
    return result;
}
