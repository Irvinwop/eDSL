/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include "functions.h"

#include <errno.h>
#include <linux/futex.h>
#include <sys/syscall.h>
#include <unistd.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error "corpus-v1 native fixtures require Linux x86-64"
#endif

_Static_assert(sizeof(_Atomic uint32_t) == 4, "Linux futex word is four bytes");
_Static_assert(_Alignof(_Atomic uint32_t) == 4, "Linux futex word alignment");

__attribute__((noinline))
int32_t c_clamp_i32(int32_t x, int32_t lo, int32_t hi)
{
    if (x < lo)
        return lo;
    if (x > hi)
        return hi;
    return x;
}

__attribute__((noinline))
uint64_t c_min_u64(uint64_t a, uint64_t b)
{
    return a < b ? a : b;
}

__attribute__((noinline))
uint64_t c_max_u64(uint64_t a, uint64_t b)
{
    return a > b ? a : b;
}

__attribute__((noinline))
int32_t c_abs_i32(int32_t x)
{
    return x < 0 ? -x : x;
}

__attribute__((noinline))
int32_t c_sign_i32(int32_t x)
{
    return (x > 0) - (x < 0);
}

__attribute__((noinline))
uint64_t c_add_mod64(uint64_t a, uint64_t b)
{
    return a + b;
}

__attribute__((noinline))
uint64_t c_mul_mod64(uint64_t a, uint64_t b)
{
    return a * b;
}

__attribute__((noinline))
uint64_t c_average_u64(uint64_t a, uint64_t b)
{
    return (a & b) + ((a ^ b) >> 1);
}

__attribute__((noinline))
uint64_t c_rotl64(uint64_t x, uint32_t n)
{
    n &= 63;
    if (n == 0)
        return x;
    return (x << n) | (x >> (64 - n));
}

__attribute__((noinline))
uint64_t c_byteswap64(uint64_t x)
{
    return (x << 56)
        | ((x & UINT64_C(0x000000000000ff00)) << 40)
        | ((x & UINT64_C(0x0000000000ff0000)) << 24)
        | ((x & UINT64_C(0x00000000ff000000)) << 8)
        | ((x & UINT64_C(0x000000ff00000000)) >> 8)
        | ((x & UINT64_C(0x0000ff0000000000)) >> 24)
        | ((x & UINT64_C(0x00ff000000000000)) >> 40)
        | (x >> 56);
}

__attribute__((noinline))
uint32_t c_popcount_loop(uint64_t x)
{
    uint32_t count = 0;
    while (x != 0) {
        x &= x - 1;
        ++count;
    }
    return count;
}

__attribute__((noinline))
uint32_t c_parity_loop(uint64_t x)
{
    uint32_t parity = 0;
    while (x != 0) {
        parity ^= (uint32_t)(x & 1);
        x >>= 1;
    }
    return parity;
}

__attribute__((noinline))
uint32_t c_gcd_u32(uint32_t a, uint32_t b)
{
    while (b != 0) {
        uint32_t remainder = a % b;
        a = b;
        b = remainder;
    }
    return a;
}

__attribute__((noinline))
uint64_t c_factorial_mod64(uint32_t n)
{
    uint64_t product = 1;
    /* A zero modular product stays zero. Counting down also handles UINT32_MAX. */
    while (n > 1 && product != 0) {
        product *= n;
        --n;
    }
    return product;
}

__attribute__((noinline))
uint64_t c_triangular_mod64(uint32_t n)
{
    uint64_t sum = 0;
    while (n > 0) {
        sum += n;
        --n;
    }
    return sum;
}

__attribute__((noinline))
uint64_t c_pow_mod64(uint64_t base, uint32_t exponent)
{
    uint64_t product = 1;
    while (exponent != 0) {
        if ((exponent & 1) != 0)
            product *= base;
        base *= base;
        exponent >>= 1;
    }
    return product;
}

__attribute__((noinline))
size_t c_strlen_bytes(const uint8_t *bytes)
{
    size_t n = 0;
    while (bytes[n] != 0)
        ++n;
    return n;
}

__attribute__((noinline))
size_t c_strnlen_bytes(const uint8_t *bytes, size_t n)
{
    size_t i = 0;
    while (i < n && bytes[i] != 0)
        ++i;
    return i;
}

__attribute__((noinline))
int32_t c_memcmp_bytes(const uint8_t *a, const uint8_t *b, size_t n)
{
    for (size_t i = 0; i < n; ++i) {
        if (a[i] != b[i])
            return (int32_t)a[i] - (int32_t)b[i];
    }
    return 0;
}

__attribute__((noinline))
bool c_bytes_equal(const uint8_t *a, const uint8_t *b, size_t n)
{
    for (size_t i = 0; i < n; ++i) {
        if (a[i] != b[i])
            return false;
    }
    return true;
}

__attribute__((noinline))
size_t c_memchr_index(const uint8_t *bytes, size_t n, uint8_t value)
{
    for (size_t i = 0; i < n; ++i) {
        if (bytes[i] == value)
            return i;
    }
    return SIZE_MAX;
}

__attribute__((noinline))
uint32_t c_sum_u32(const uint32_t *a, size_t n)
{
    uint32_t sum = 0;
    for (size_t i = 0; i < n; ++i)
        sum += a[i];
    return sum;
}

__attribute__((noinline))
uint32_t c_max_u32(const uint32_t *a, size_t n)
{
    uint32_t maximum = a[0];
    for (size_t i = 1; i < n; ++i) {
        if (a[i] > maximum)
            maximum = a[i];
    }
    return maximum;
}

__attribute__((noinline))
size_t c_count_zero_u32(const uint32_t *a, size_t n)
{
    size_t count = 0;
    for (size_t i = 0; i < n; ++i)
        count += a[i] == 0;
    return count;
}

__attribute__((noinline))
size_t c_linear_search_u32(const uint32_t *a, size_t n, uint32_t value)
{
    for (size_t i = 0; i < n; ++i) {
        if (a[i] == value)
            return i;
    }
    return SIZE_MAX;
}

__attribute__((noinline))
void c_reverse_u32(uint32_t *a, size_t n)
{
    for (size_t i = 0; i < n / 2; ++i) {
        uint32_t saved = a[i];
        a[i] = a[n - 1 - i];
        a[n - 1 - i] = saved;
    }
}

__attribute__((noinline))
void c_fill_u32(uint32_t *a, size_t n, uint32_t value)
{
    for (size_t i = 0; i < n; ++i)
        a[i] = value;
}

__attribute__((noinline))
void c_copy_u32(uint32_t *restrict dst, const uint32_t *restrict src, size_t n)
{
    for (size_t i = 0; i < n; ++i)
        dst[i] = src[i];
}

__attribute__((noinline))
uint64_t c_dot_mod64(const uint32_t *a, const uint32_t *b, size_t n)
{
    uint64_t sum = 0;
    for (size_t i = 0; i < n; ++i)
        sum += (uint64_t)a[i] * b[i];
    return sum;
}

__attribute__((noinline))
void c_prefix_sum_u32(uint32_t *a, size_t n)
{
    uint32_t sum = 0;
    for (size_t i = 0; i < n; ++i) {
        sum += a[i];
        a[i] = sum;
    }
}

__attribute__((noinline))
void c_struct_copy(struct c_u64x4 *restrict dst,
                   const struct c_u64x4 *restrict src)
{
    *dst = *src;
}

__attribute__((noinline))
uint64_t c_struct_sum(const struct c_u64x4 *src)
{
    return src->a + src->b + src->c + src->d;
}

__attribute__((noinline))
size_t c_binary_search_u32(const uint32_t *a, size_t n, uint32_t key)
{
    size_t lo = 0;
    size_t hi = n;
    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (a[mid] < key)
            lo = mid + 1;
        else if (a[mid] > key)
            hi = mid;
        else
            return mid;
    }
    return SIZE_MAX;
}

__attribute__((noinline))
uint64_t c_atomic_fetch_add64(_Atomic uint64_t *p, uint64_t delta)
{
    return atomic_fetch_add_explicit(p, delta, memory_order_seq_cst);
}

__attribute__((noinline))
uint64_t c_atomic_load_acquire64(_Atomic uint64_t *p)
{
    return atomic_load_explicit(p, memory_order_acquire);
}

__attribute__((noinline))
void c_atomic_store_release64(_Atomic uint64_t *p, uint64_t value)
{
    atomic_store_explicit(p, value, memory_order_release);
}

__attribute__((noinline))
void c_spinlock_acquire(_Atomic uint32_t *lock)
{
    while (atomic_exchange_explicit(lock, 1, memory_order_acquire) != 0)
        ;
}

__attribute__((noinline))
void c_spinlock_release(_Atomic uint32_t *lock)
{
    atomic_store_explicit(lock, 0, memory_order_release);
}

__attribute__((noinline))
int32_t c_futex_wait_loop(_Atomic uint32_t *p, uint32_t expected)
{
    while (atomic_load_explicit(p, memory_order_acquire) == expected) {
        if (syscall(SYS_futex, p, FUTEX_WAIT_PRIVATE, expected, NULL, NULL, 0) == -1) {
            int error = errno;
            if (error != EINTR && error != EAGAIN)
                return -error;
        }
    }
    return 0;
}

__attribute__((noinline))
void c_counter_worker(_Atomic uint64_t *p, uint32_t iterations)
{
    while (iterations > 0) {
        atomic_fetch_add_explicit(p, UINT64_C(1), memory_order_seq_cst);
        --iterations;
    }
}
