/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stddef.h>
#include <stdint.h>

__attribute__((noinline)) uint32_t sum_pair(const uint32_t *a, size_t na,
                                          const uint32_t *b, size_t nb)
{
    uint32_t result = 0;
    while (na != 0) {
        result += *a++;
        --na;
    }
    while (nb != 0) {
        result += *b++;
        --nb;
    }
    return result;
}
