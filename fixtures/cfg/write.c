/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>

void write_word(uint32_t *target, uint64_t argument)
{
    *target = (uint32_t)argument;
}
