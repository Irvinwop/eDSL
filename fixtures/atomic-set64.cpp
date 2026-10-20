/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <atomic>
#include <cstdint>

/* Owned GNU++26 SUBSET input (-std=gnu++2c on Clang18). These functions have
 * ordinary C ABI names, but their source object type is std::atomic<uint64_t>.
 * The native observer executes extracted machine slots, not these functions
 * through casts between C and C++ atomic object types. No such cast is used.
 * No C++ object-model or source-to-machine preservation theorem is claimed. */
extern "C" void atomic_and64_discard(std::atomic<std::uint64_t> *target,
    std::uint64_t mask)
{
    (void)target->fetch_and(mask, std::memory_order_seq_cst);
}
extern "C" void atomic_or64_discard(std::atomic<std::uint64_t> *target,
    std::uint64_t mask)
{
    (void)target->fetch_or(mask, std::memory_order_seq_cst);
}
extern "C" void atomic_xor64_discard(std::atomic<std::uint64_t> *target,
    std::uint64_t mask)
{
    (void)target->fetch_xor(mask, std::memory_order_seq_cst);
}
