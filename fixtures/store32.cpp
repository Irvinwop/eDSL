// Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
#include <cstdint>

extern "C" void edsl_store32(std::uint32_t *address, std::uint32_t value)
{
    *address = value;
}
