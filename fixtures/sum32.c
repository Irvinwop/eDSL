/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stddef.h>
#include <stdint.h>

/* Project-owned negative variants, compiled only by verify-sum32.sh. */
#ifndef EDSL_SUM32_STRIDE
#define EDSL_SUM32_STRIDE 1
#endif
#ifndef EDSL_SUM32_BIAS
#define EDSL_SUM32_BIAS 0
#endif
#ifndef EDSL_SUM32_OVERREAD
#define EDSL_SUM32_OVERREAD 0
#endif

__attribute__((noinline)) uint32_t sum32_ptr(const uint32_t *p, size_t n)
{
    uint32_t sum = 0;
#if EDSL_SUM32_OVERREAD
    const size_t original_n = n;
#endif
    while (n != 0) {
        sum += *p;
        p += EDSL_SUM32_STRIDE;
        --n;
    }
#if EDSL_SUM32_OVERREAD
    if (original_n != 0)
        sum += *(const volatile uint32_t *)p;
#endif
    return sum + EDSL_SUM32_BIAS;
}

__attribute__((noinline)) uint32_t sum32_index(const uint32_t *p, size_t n)
{
    uint32_t sum = 0;
    for (size_t i = 0; i < n; ++i)
        sum += p[EDSL_SUM32_STRIDE * i];
#if EDSL_SUM32_OVERREAD
    if (n != 0)
        sum += *(const volatile uint32_t *)(p + n);
#endif
    return sum + EDSL_SUM32_BIAS;
}
