// Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
#include <cstdint>
// Volatile retains the fixture's load; proofs concern the final machine bytes.
extern "C" std::uint64_t store_load64(volatile std::uint64_t *pointer, std::uint64_t value)
{
    *pointer = value;
    return *pointer;
}
