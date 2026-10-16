/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>

uint32_t *store_return32(uint32_t *pointer, uint32_t value)
{
    *pointer = value;
    return pointer;
}
