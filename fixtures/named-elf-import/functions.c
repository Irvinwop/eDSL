/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* An ordinary named non-entry function; no frozen compiler output or flags. */
__attribute__((noinline)) unsigned long twice(unsigned long value) {
    return value + value;
}
__attribute__((noreturn)) void _start(void) {
    for (;;) __asm__ volatile ("" ::: "memory");
}
