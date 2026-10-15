// Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
#include <atomic>
#include <cstdint>

extern "C" std::uint32_t edsl_exchange32(std::atomic<std::uint32_t> *address,
                                      std::uint32_t value)
{
    return address->exchange(value, std::memory_order_seq_cst);
}
