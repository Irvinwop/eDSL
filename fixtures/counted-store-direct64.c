/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>

/* Owned closed-form fixture. Proofs concern complete final compiler bytes;
 * no source-language or volatile-effect preservation claim is made. */
uint64_t publish_direct(volatile uint64_t *target, uint64_t value, uint64_t count)
{
    uint64_t result = value + count;
    if (count != 0) *target = result;
    return result;
}
