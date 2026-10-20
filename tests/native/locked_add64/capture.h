/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#ifndef EDSL_LOCKED_ADD64_CAPTURE_H
#define EDSL_LOCKED_ADD64_CAPTURE_H
#include <stddef.h>
#include <stdint.h>

/* Architectural encoding order, including RSP at index 4. */
struct edsl_ladd_snapshot {
    uint64_t registers[16];
    uint64_t flags;
    uint64_t rip;
};
struct edsl_ladd_window {
    const unsigned char *begin;
    const unsigned char *end;
    uint64_t source, base, ignored_x;
};
#ifdef __cplusplus
extern "C" {
#endif
extern struct edsl_ladd_snapshot edsl_ladd_input, edsl_ladd_before, edsl_ladd_after;
extern const struct edsl_ladd_window edsl_ladd_windows[], edsl_ladd_windows_end[];
extern const unsigned char edsl_ladd_section_begin[], edsl_ladd_section_end[];
int edsl_ladd_checked_call(const unsigned char *);
#ifdef __cplusplus
}
static_assert(offsetof(edsl_ladd_snapshot, flags) == 128);
static_assert(offsetof(edsl_ladd_snapshot, rip) == 136);
static_assert(sizeof(edsl_ladd_snapshot) == 144);
static_assert(sizeof(edsl_ladd_window) == 40);
#endif
#endif
