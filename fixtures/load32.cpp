// Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
#include <cstdint>

extern "C" std::uint32_t edsl_load32(const std::uint32_t *address)
{
    return *address;
}
