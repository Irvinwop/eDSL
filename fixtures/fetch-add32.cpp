/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <cstdint>

extern "C" std::uint32_t edsl_fetch_add32(std::uint32_t *cell, std::uint32_t delta)
{
    return __atomic_fetch_add(cell, delta, __ATOMIC_SEQ_CST);
}
