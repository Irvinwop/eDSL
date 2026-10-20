/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#ifndef CORPUS_V1_FUNCTIONS_H
#define CORPUS_V1_FUNCTIONS_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdatomic.h>

/* Native fixture API. Arithmetic on unsigned results is modular. Buffer
 * counts describe accessible elements; inputs are immutable unless declared
 * mutable. Empty buffers need no accessible elements. */

/* Requires lo <= hi. */
int32_t c_clamp_i32(int32_t x, int32_t lo, int32_t hi);
uint64_t c_min_u64(uint64_t a, uint64_t b);
uint64_t c_max_u64(uint64_t a, uint64_t b);
/* Requires x != INT32_MIN. */
int32_t c_abs_i32(int32_t x);
int32_t c_sign_i32(int32_t x);
uint64_t c_add_mod64(uint64_t a, uint64_t b);
uint64_t c_mul_mod64(uint64_t a, uint64_t b);
uint64_t c_average_u64(uint64_t a, uint64_t b);
/* The rotation count is reduced modulo 64, including zero. */
uint64_t c_rotl64(uint64_t x, uint32_t n);
uint64_t c_byteswap64(uint64_t x);
uint32_t c_popcount_loop(uint64_t x);
uint32_t c_parity_loop(uint64_t x);
/* gcd(0, 0) = 0. The empty product and zeroth power are 1. */
uint32_t c_gcd_u32(uint32_t a, uint32_t b);
uint64_t c_factorial_mod64(uint32_t n);
uint64_t c_triangular_mod64(uint32_t n);
uint64_t c_pow_mod64(uint64_t base, uint32_t exponent);

/* strlen requires a reachable NUL; strnlen reads at most n bytes. */
size_t c_strlen_bytes(const uint8_t *bytes);
size_t c_strnlen_bytes(const uint8_t *bytes, size_t n);
/* Comparison uses unsigned byte order; only the result's sign is specified. */
int32_t c_memcmp_bytes(const uint8_t *a, const uint8_t *b, size_t n);
bool c_bytes_equal(const uint8_t *a, const uint8_t *b, size_t n);
/* Index searches return SIZE_MAX if absent, and the first index if present. */
size_t c_memchr_index(const uint8_t *bytes, size_t n, uint8_t value);

uint32_t c_sum_u32(const uint32_t *a, size_t n);
/* Requires n > 0. */
uint32_t c_max_u32(const uint32_t *a, size_t n);
size_t c_count_zero_u32(const uint32_t *a, size_t n);
size_t c_linear_search_u32(const uint32_t *a, size_t n, uint32_t value);
void c_reverse_u32(uint32_t *a, size_t n);
void c_fill_u32(uint32_t *a, size_t n, uint32_t value);
/* The source and destination ranges must be disjoint. */
void c_copy_u32(uint32_t *restrict dst, const uint32_t *restrict src, size_t n);
uint64_t c_dot_mod64(const uint32_t *a, const uint32_t *b, size_t n);
void c_prefix_sum_u32(uint32_t *a, size_t n);

struct c_u64x4 {
    uint64_t a;
    uint64_t b;
    uint64_t c;
    uint64_t d;
};

/* Objects must be disjoint. */
void c_struct_copy(struct c_u64x4 *restrict dst,
                   const struct c_u64x4 *restrict src);
uint64_t c_struct_sum(const struct c_u64x4 *src);
/* Requires nondecreasing input; returns any matching index or SIZE_MAX. */
size_t c_binary_search_u32(const uint32_t *a, size_t n, uint32_t key);

uint64_t c_atomic_fetch_add64(_Atomic uint64_t *p, uint64_t delta);
uint64_t c_atomic_load_acquire64(_Atomic uint64_t *p);
void c_atomic_store_release64(_Atomic uint64_t *p, uint64_t value);
/* Lock words use 0 for unlocked and 1 for locked. Release requires ownership. */
void c_spinlock_acquire(_Atomic uint32_t *lock);
void c_spinlock_release(_Atomic uint32_t *lock);
/* Linux x86-64 only: p names a live, four-byte-aligned atomic uint32_t.
 * Acquire-load until *p differs, retrying EINTR/EAGAIN from WAIT_PRIVATE.
 * Return 0 on a differing value, or negative errno on another syscall error.
 * A producer must change the value and arrange a wake for blocked waiters;
 * no termination is promised without that environmental progress. */
int32_t c_futex_wait_loop(_Atomic uint32_t *p, uint32_t expected);
/* Each increment is a seq_cst fetch_add, as is atomic_fetch_add64 above. */
void c_counter_worker(_Atomic uint64_t *p, uint32_t iterations);

#endif
