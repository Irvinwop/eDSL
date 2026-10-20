/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>

/* Owned GNU23 compiler inputs. Native checks concern the entire final linked
 * .text of each function; they do not establish C-to-machine preservation. */
uint64_t maximum64(uint64_t left, uint64_t right)
{
    return left < right ? right : left;
}

uint64_t minimum64(uint64_t left, uint64_t right)
{
    return left < right ? left : right;
}

int64_t signed_maximum64(int64_t left, int64_t right)
{
    return left < right ? right : left;
}
