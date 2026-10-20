/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>

/* Owned GNU23 compiler inputs. Native evidence concerns each entire final
 * linked .text, and does not establish source-to-machine preservation. */
uint64_t intersection64(uint64_t left, uint64_t right)
{
    return left & right;
}

uint64_t union64(uint64_t left, uint64_t right)
{
    return left | right;
}

uint64_t symmetric_difference64(uint64_t left, uint64_t right)
{
    return left ^ right;
}
