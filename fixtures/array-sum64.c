/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>

uint64_t sum64_array(const uint64_t *data, uint64_t count)
{
    uint64_t result = 0;
    for (uint64_t i = 0; i < count; ++i)
        result += data[i];
    return result;
}
