/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include "functions.h"

#include <errno.h>
#include <inttypes.h>
#include <linux/futex.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

/* These are finite observations of the linked native object, not proofs of
 * functional correctness, the memory model, progress, or linearizability. */
#define COUNT_OF(a) (sizeof(a) / sizeof((a)[0]))

static void require(bool condition, const char *label)
{
    if (!condition) {
        fprintf(stderr, "native corpus check failed: %s\n", label);
        exit(1);
    }
}

static void require_u64(uint64_t actual, uint64_t expected, const char *label)
{
    if (actual != expected) {
        fprintf(stderr, "%s: got 0x%016" PRIx64 ", expected 0x%016" PRIx64 "\n",
                label, actual, expected);
        exit(1);
    }
}

static void require_system(bool condition, const char *operation)
{
    if (!condition) {
        perror(operation);
        exit(2);
    }
}

static void require_pthread(int error, const char *operation)
{
    if (error != 0) {
        fprintf(stderr, "%s: %s\n", operation, strerror(error));
        exit(2);
    }
}

static void timeout_handler(int signal_number)
{
    (void)signal_number;
    static const char message[] = "native corpus check timed out\n";
    ssize_t written = write(STDERR_FILENO, message, sizeof message - 1);
    (void)written;
    _exit(1);
}

static struct timespec deadline_after(clockid_t clock, time_t seconds)
{
    struct timespec result;
    require_system(clock_gettime(clock, &result) == 0, "clock_gettime");
    result.tv_sec += seconds;
    return result;
}

static bool before_deadline(struct timespec deadline)
{
    struct timespec now;
    require_system(clock_gettime(CLOCK_MONOTONIC, &now) == 0, "clock_gettime");
    return now.tv_sec < deadline.tv_sec
        || (now.tv_sec == deadline.tv_sec && now.tv_nsec < deadline.tv_nsec);
}

static void join_bounded(pthread_t thread)
{
    struct timespec deadline = deadline_after(CLOCK_REALTIME, 5);
    require_pthread(pthread_timedjoin_np(thread, NULL, &deadline), "pthread_timedjoin_np");
}

static void check_scalars(void)
{
    static const struct {
        int32_t x, lo, hi, result;
    } clamps[] = {
        {INT32_MIN, -7, 11, -7}, {INT32_MAX, -7, 11, 11},
        {-8, -7, 11, -7}, {-7, -7, 11, -7}, {-1, -7, 11, -1},
        {0, -7, 11, 0}, {11, -7, 11, 11}, {12, -7, 11, 11},
        {INT32_MIN, INT32_MIN, INT32_MAX, INT32_MIN},
        {INT32_MAX, INT32_MIN, INT32_MAX, INT32_MAX},
        {0, INT32_MIN, -1, -1}, {0, 1, INT32_MAX, 1},
        {INT32_MIN, 3, 3, 3}, {INT32_MAX, -3, -3, -3},
    };
    for (size_t i = 0; i < COUNT_OF(clamps); ++i)
        require(c_clamp_i32(clamps[i].x, clamps[i].lo, clamps[i].hi) == clamps[i].result,
                "signed clamp boundaries");

    static const struct { int32_t x, magnitude, sign; } signed_cases[] = {
        {INT32_MIN + 1, INT32_MAX, -1}, {-65536, 65536, -1},
        {-1, 1, -1}, {0, 0, 0}, {1, 1, 1}, {65536, 65536, 1},
        {INT32_MAX, INT32_MAX, 1},
    };
    require(c_sign_i32(INT32_MIN) == -1, "sign of minimum signed integer");
    for (size_t i = 0; i < COUNT_OF(signed_cases); ++i) {
        require(c_abs_i32(signed_cases[i].x) == signed_cases[i].magnitude,
                "absolute signed magnitude");
        require(c_sign_i32(signed_cases[i].x) == signed_cases[i].sign,
                "negative, zero, positive sign");
    }

    static const uint64_t edges[] = {
        0, 1, 2, UINT64_C(0xffffffff), UINT64_C(0x100000000),
        UINT64_C(0x7fffffffffffffff), UINT64_C(0x8000000000000000),
        UINT64_C(0xfedcba9876543210), UINT64_MAX - 1, UINT64_MAX,
    };
    for (size_t i = 0; i < COUNT_OF(edges); ++i) {
        for (size_t j = 0; j < COUNT_OF(edges); ++j) {
            uint64_t a = edges[i], b = edges[j];
            uint64_t lo = c_min_u64(a, b), hi = c_max_u64(a, b);
            require(lo <= a && lo <= b && hi >= a && hi >= b,
                    "unsigned extrema order");
            require((lo == a || lo == b) && (hi == a || hi == b)
                    && (__uint128_t)lo + hi == (__uint128_t)a + b,
                    "extrema preserve the input multiset");
            /* Widened arithmetic models mathematical results before reduction;
             * in particular, the average oracle cannot overflow at bit 64. */
            require_u64(c_add_mod64(a, b), (uint64_t)((__uint128_t)a + b),
                        "modular addition");
            require_u64(c_mul_mod64(a, b), (uint64_t)((__uint128_t)a * b),
                        "modular multiplication");
            require_u64(c_average_u64(a, b), (uint64_t)(((__uint128_t)a + b) / 2),
                        "floor average with an exact widened sum");
        }
    }
}

static void check_bits(void)
{
    static const uint32_t rotations[] = {0, 1, 2, 31, 32, 63, 64, 65, 127, 128, UINT32_MAX};
    /* A rotation must send each basis bit to its specified position. This
     * oracle does not implement rotation with paired shifts. */
    for (uint32_t bit = 0; bit < 64; ++bit) {
        uint64_t basis = UINT64_C(1) << bit;
        for (size_t j = 0; j < COUNT_OF(rotations); ++j) {
            uint32_t position = (uint32_t)(((uint64_t)bit + rotations[j]) % 64);
            require_u64(c_rotl64(basis, rotations[j]), UINT64_C(1) << position,
                        "rotation basis bit and count reduction");
        }
        require_u64(c_popcount_loop(basis), 1, "one set bit");
        require_u64(c_popcount_loop(~basis), 63, "one cleared bit");
        require_u64(c_parity_loop(basis), 1, "odd parity of one set bit");
        require_u64(c_parity_loop(~basis), 1, "odd parity of 63 set bits");
    }
    for (uint32_t bits = 0; bits <= 64; ++bits) {
        uint64_t low_mask = bits == 64 ? UINT64_MAX : (UINT64_C(1) << bits) - 1;
        require_u64(c_popcount_loop(low_mask), bits, "population of consecutive bits");
        require_u64(c_parity_loop(low_mask), bits % 2, "parity of consecutive bits");
    }
    require_u64(c_popcount_loop(UINT64_C(0xa5a5a5a55a5a5a5a)), 32, "mixed bit population");
    require_u64(c_parity_loop(UINT64_C(0xa5a5a5a55a5a5a5a)), 0, "mixed even parity");
    require_u64(c_rotl64(UINT64_C(0x8123456789abcdef), 4),
                UINT64_C(0x123456789abcdef8), "mixed rotation wraps the high nibble");
    require_u64(c_rotl64(UINT64_MAX, UINT32_MAX), UINT64_MAX, "rotate all bits");
    require_u64(c_rotl64(0, 64), 0, "rotate zero");

    static const struct { uint64_t input, output; } swaps[] = {
        {0, 0}, {UINT64_MAX, UINT64_MAX},
        {UINT64_C(0x0123456789abcdef), UINT64_C(0xefcdab8967452301)},
        {UINT64_C(0x8000000000000001), UINT64_C(0x0100000000000080)},
        {UINT64_C(0x00000000ffffffff), UINT64_C(0xffffffff00000000)},
    };
    for (size_t i = 0; i < COUNT_OF(swaps); ++i) {
        require_u64(c_byteswap64(swaps[i].input), swaps[i].output, "byte reversal vectors");
        require_u64(c_byteswap64(c_byteswap64(swaps[i].input)), swaps[i].input,
                    "byte reversal is an involution");
    }
}

static void check_integer_loops(void)
{
    static const struct { uint32_t a, b, gcd; } gcd_cases[] = {
        {0, 0, 0}, {0, UINT32_MAX, UINT32_MAX}, {UINT32_MAX, 0, UINT32_MAX},
        {48, 18, 6}, {18, 48, 6}, {65536, 65535, 1},
        {UINT32_MAX, 65535, 65535}, {UINT32_C(0x80000000), UINT32_MAX, 1},
        {UINT32_C(0x80000000), UINT32_C(0x40000000), UINT32_C(0x40000000)},
    };
    for (size_t i = 0; i < COUNT_OF(gcd_cases); ++i)
        require_u64(c_gcd_u32(gcd_cases[i].a, gcd_cases[i].b), gcd_cases[i].gcd,
                    "gcd known common factors and coprime boundaries");

    static const struct { uint32_t n; uint64_t factorial; } factorials[] = {
        {0, 1}, {1, 1}, {2, 2}, {5, 120}, {10, UINT64_C(3628800)},
        {20, UINT64_C(2432902008176640000)},
        {21, UINT64_C(14197454024290336768)},
        /* v2(64!) = v2(65!) = 63; v2(66!) = 64. */
        {64, UINT64_C(0x8000000000000000)},
        {65, UINT64_C(0x8000000000000000)}, {66, 0}, {1000, 0}, {UINT32_MAX, 0},
    };
    for (size_t i = 0; i < COUNT_OF(factorials); ++i)
        require_u64(c_factorial_mod64(factorials[i].n), factorials[i].factorial,
                    "factorial exact residues and zero threshold");

    static const uint32_t counts[] = {0, 1, 2, 3, 32, 65535, 65536, UINT32_MAX};
    for (size_t i = 0; i < COUNT_OF(counts); ++i) {
        __uint128_t n = counts[i];
        require_u64(c_triangular_mod64(counts[i]), (uint64_t)(n * (n + 1) / 2),
                    "triangular closed form including UINT32_MAX");
    }

    static const uint32_t exponents[] = {0, 1, 2, 3, 31, 32, 63, 64, 127, UINT32_MAX};
    for (size_t i = 0; i < COUNT_OF(exponents); ++i) {
        uint32_t exponent = exponents[i];
        require_u64(c_pow_mod64(0, exponent), exponent == 0 ? 1 : 0, "zero powers");
        require_u64(c_pow_mod64(1, exponent), 1, "identity powers");
        require_u64(c_pow_mod64(UINT64_MAX, exponent), exponent % 2 == 0 ? 1 : UINT64_MAX,
                    "powers of minus one modulo 2^64");
        uint64_t expected = exponent < 64 ? UINT64_C(1) << exponent : 0;
        require_u64(c_pow_mod64(2, exponent), expected, "powers of two and bit-64 reduction");
    }
    require_u64(c_pow_mod64(3, 13), UINT64_C(1594323), "odd base, mixed exponent bits");
    require_u64(c_pow_mod64(5, 27), UINT64_C(7450580596923828125), "large exact odd power");
    require_u64(c_pow_mod64(7, 20), UINT64_C(79792266297612001), "another odd base");
    require_u64(c_pow_mod64(UINT64_C(0x100000001), 3), UINT64_C(0x300000001),
                "binomial power reduced modulo 2^64");
}

struct guarded {
    uint8_t *mapping;
    uint8_t *end;
    size_t page;
};

static struct guarded guarded_allocate(void)
{
    long page = sysconf(_SC_PAGESIZE);
    require_system(page > 0, "sysconf(_SC_PAGESIZE)");
    uint8_t *mapping = mmap(NULL, 3 * (size_t)page, PROT_NONE,
                            MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    require_system(mapping != MAP_FAILED, "mmap guard pages");
    require_system(mprotect(mapping + page, (size_t)page, PROT_READ | PROT_WRITE) == 0,
                   "mprotect writable data page");
    return (struct guarded){mapping, mapping + 2 * page, (size_t)page};
}

static void guarded_read_only(struct guarded area)
{
    require_system(mprotect(area.mapping + area.page, area.page, PROT_READ) == 0,
                   "mprotect read-only input");
}

static void guarded_release(struct guarded area)
{
    require_system(munmap(area.mapping, 3 * area.page) == 0, "munmap guard pages");
}

static void check_byte_pair(const uint8_t *a, const uint8_t *b, size_t n)
{
    int expected = memcmp(a, b, n);
    int32_t actual = c_memcmp_bytes(a, b, n);
    require((actual > 0) - (actual < 0) == (expected > 0) - (expected < 0),
            "unsigned lexical order agrees with libc, including high bytes");
    require(c_bytes_equal(a, b, n) == (expected == 0), "byte equality agrees with lexical equality");
    require(c_bytes_equal(b, a, n) == (expected == 0), "byte equality is symmetric");
}

static void check_strings(void)
{
    static const size_t counts[] = {0, 1, 2, 3, 7, 15, 16, 31, 32, 63, 64, 65, 127};
    for (size_t k = 0; k < COUNT_OF(counts); ++k) {
        size_t n = counts[k];
        uint8_t a[132], b[132], saved_a[132], saved_b[132];
        for (size_t i = 0; i < sizeof a; ++i)
            a[i] = (uint8_t)(0x80 + 37 * i);
        memcpy(b, a, sizeof a);
        memcpy(saved_a, a, sizeof a);
        check_byte_pair(a + 1, b + 1, n);
        static const uint8_t needles[] = {0, 1, 0x7f, 0x80, 0xff};
        for (size_t j = 0; j < COUNT_OF(needles); ++j) {
            const uint8_t *found = memchr(a + 1, needles[j], n);
            size_t expected = found == NULL ? SIZE_MAX : (size_t)(found - (a + 1));
            require_u64(c_memchr_index(a + 1, n, needles[j]), expected,
                        "first byte index agrees with libc");
        }
        if (n > 0) {
            size_t positions[] = {0, n / 2, n - 1};
            for (size_t j = 0; j < COUNT_OF(positions); ++j) {
                memcpy(b, a, sizeof a);
                size_t pos = positions[j] + 1;
                b[pos] = (uint8_t)(a[pos] ^ 0x80);
                /* An opposite later difference must not override the first. */
                if (pos < n)
                    b[n] = (uint8_t)(a[n] ^ 0xff);
                memcpy(saved_b, b, sizeof b);
                check_byte_pair(a + 1, b + 1, n);
                check_byte_pair(b + 1, a + 1, n);
                require(memcmp(b, saved_b, sizeof b) == 0, "second byte input frame");
            }
        }
        require(memcmp(a, saved_a, sizeof a) == 0, "first byte input frame");

        struct guarded area = guarded_allocate();
        uint8_t *text = area.end - n - 1;
        for (size_t i = 0; i < n; ++i)
            text[i] = (uint8_t)(0x80 + i % 127);
        text[n] = 0;
        guarded_read_only(area);
        require_u64(c_strlen_bytes(text), n, "NUL terminator at the page boundary");
        require_u64(c_strnlen_bytes(text, n + 1), n, "bounded string stops at NUL");
        require_u64(c_strnlen_bytes(text, n / 2), n / 2, "bounded string stops at its count");
        require_u64(c_strnlen_bytes(text, n), n, "bounded non-NUL prefix");
        require_u64(c_memchr_index(text, n + 1, 0), n, "NUL search at the last accessible byte");
        require_u64(c_memchr_index(text, n, 0), SIZE_MAX, "NUL outside the search range");
        check_byte_pair(text, text, n + 1);
        require_u64(c_strnlen_bytes(area.end, 0), 0, "empty length does not read a guard page");
        require(c_memcmp_bytes(area.end, area.end, 0) == 0
                && c_bytes_equal(area.end, area.end, 0)
                && c_memchr_index(area.end, 0, 0) == SIZE_MAX,
                "empty byte operations do not access memory");
        guarded_release(area);
    }

    static const uint8_t repeated[] = {0xff, 0, 0x80, 0xff, 0x80, 0};
    require_u64(c_memchr_index(repeated, sizeof repeated, 0xff), 0, "first repeated high byte");
    require_u64(c_memchr_index(repeated, sizeof repeated, 0), 1, "first embedded NUL");
    require_u64(c_memchr_index(repeated, sizeof repeated, 0x80), 2, "first repeated sign-bit byte");
    require_u64(c_strlen_bytes(repeated), 1, "string ends at the first embedded NUL");
}

static void check_read_arrays(void)
{
    static const size_t counts[] = {0, 1, 2, 3, 7, 16, 31, 32, 63, 64, 65, 257};
    for (size_t k = 0; k < COUNT_OF(counts); ++k) {
        size_t n = counts[k];
        uint32_t a[257], b[257], saved_a[257], saved_b[257];
        for (size_t i = 0; i < COUNT_OF(a); ++i) {
            a[i] = (uint32_t)i + 1;
            b[i] = i < n ? (uint32_t)(n - i) : UINT32_C(0xa5a5a5a5);
        }
        memcpy(saved_a, a, sizeof a);
        memcpy(saved_b, b, sizeof b);
        __uint128_t count = n;
        require_u64(c_sum_u32(a, n), (uint32_t)(count * (count + 1) / 2),
                    "ramp sum closed form");
        require_u64(c_count_zero_u32(a, n), 0, "strictly positive ramp has no zero");
        if (n > 0)
            require_u64(c_max_u32(a, n), n, "last ramp element is the maximum");
        require_u64(c_dot_mod64(a, b, n), (uint64_t)(count * (count + 1) * (count + 2) / 6),
                    "ascending and descending dot product closed form");
        require_u64(c_dot_mod64(a, a, n), (uint64_t)(count * (count + 1) * (2 * count + 1) / 6),
                    "sum of squares closed form");
        uint32_t keys[] = {0, 1, (uint32_t)(n / 2), (uint32_t)n, (uint32_t)n + 1, UINT32_MAX};
        for (size_t j = 0; j < COUNT_OF(keys); ++j) {
            uint32_t key = keys[j];
            size_t expected = key >= 1 && key <= n ? (size_t)key - 1 : SIZE_MAX;
            require_u64(c_linear_search_u32(a, n, key), expected, "linear search in a ramp");
            size_t actual = c_binary_search_u32(a, n, key);
            require(actual == expected, "binary search in a unique sorted ramp");
        }
        require(memcmp(a, saved_a, sizeof a) == 0 && memcmp(b, saved_b, sizeof b) == 0,
                "read-only array operations preserve both inputs");

        for (size_t i = 0; i < COUNT_OF(a); ++i)
            a[i] = i % 3 == 0 ? 0 : UINT32_MAX;
        size_t zeros = (n + 2) / 3;
        require_u64(c_count_zero_u32(a, n), zeros, "periodic zero count closed form");
        require_u64(c_sum_u32(a, n), (uint32_t)(UINT64_C(0x100000000) - (n - zeros)),
                    "modular sum of minus-one entries");
        if (n > 0)
            require_u64(c_max_u32(a, n), n == 1 ? 0 : UINT32_MAX, "unsigned maximum with zero");
        for (size_t i = 0; i < COUNT_OF(a); ++i)
            a[i] = UINT32_MAX;
        __uint128_t product = (__uint128_t)UINT32_MAX * UINT32_MAX;
        require_u64(c_dot_mod64(a, a, n), (uint64_t)(count * product),
                    "full-width products and modular dot accumulation");

        struct guarded area = guarded_allocate();
        require(n * sizeof(uint32_t) <= area.page, "guarded array fits the data page");
        uint32_t *data = (uint32_t *)area.end - n;
        for (size_t i = 0; i < n; ++i)
            data[i] = (uint32_t)i + 1;
        guarded_read_only(area);
        require_u64(c_sum_u32(data, n), (uint32_t)(count * (count + 1) / 2),
                    "sum ending at a guard page");
        require_u64(c_count_zero_u32(data, n), 0, "zero count ending at a guard page");
        require_u64(c_linear_search_u32(data, n, 0), SIZE_MAX, "absent linear key at a guard page");
        require_u64(c_binary_search_u32(data, n, UINT32_MAX), SIZE_MAX,
                    "absent binary key at a guard page");
        require_u64(c_dot_mod64(data, data, n),
                    (uint64_t)(count * (count + 1) * (2 * count + 1) / 6),
                    "dot product ending at a guard page");
        if (n > 0)
            require_u64(c_max_u32(data, n), n, "maximum ending at a guard page");
        guarded_release(area);
    }

    static const uint32_t duplicate[] = {UINT32_MAX, 0, 7, 0, 7, UINT32_MAX};
    require_u64(c_linear_search_u32(duplicate, COUNT_OF(duplicate), 0), 1, "first zero index");
    require_u64(c_linear_search_u32(duplicate, COUNT_OF(duplicate), 7), 2, "first duplicate index");
    require_u64(c_linear_search_u32(duplicate, COUNT_OF(duplicate), UINT32_MAX), 0,
                "first unsigned maximum index");
    static const uint32_t sorted[] = {0, 0, 1, 7, 7, 7, 32, UINT32_MAX};
    static const struct { uint32_t key; bool present; } searches[] = {
        {0, true}, {1, true}, {2, false}, {7, true}, {31, false},
        {32, true}, {33, false}, {UINT32_C(0x80000000), false}, {UINT32_MAX, true},
    };
    for (size_t i = 0; i < COUNT_OF(searches); ++i) {
        size_t index = c_binary_search_u32(sorted, COUNT_OF(sorted), searches[i].key);
        if (searches[i].present)
            require(index < COUNT_OF(sorted) && sorted[index] == searches[i].key,
                    "binary search permits any matching duplicate");
        else
            require(index == SIZE_MAX, "binary search absent key among duplicates");
    }
}

static void check_u32_frame(const uint32_t *after, const uint32_t *before,
                            size_t total, size_t offset, size_t n)
{
    for (size_t i = 0; i < total; ++i) {
        if (i < offset || i - offset >= n)
            require(after[i] == before[i], "mutation stays inside its destination range");
    }
}

static void check_array_mutations(void)
{
    enum { WORDS = 273, OFFSET = 5 };
    static const size_t counts[] = {0, 1, 2, 3, 7, 16, 31, 32, 63, 64, 65, 257};
    for (size_t k = 0; k < COUNT_OF(counts); ++k) {
        size_t n = counts[k];
        uint32_t original[WORDS], data[WORDS], source[WORDS], saved_source[WORDS];
        for (size_t i = 0; i < WORDS; ++i) {
            original[i] = UINT32_C(0xfedcba98) ^ (uint32_t)(i * 66051);
            source[i] = UINT32_C(0x80000001) + (uint32_t)(i * 7919);
        }
        memcpy(data, original, sizeof data);
        c_reverse_u32(data + OFFSET, n);
        for (size_t i = 0; i < n; ++i)
            require(data[OFFSET + i] == original[OFFSET + n - 1 - i],
                    "reversal maps every output index to its mirrored input");
        check_u32_frame(data, original, WORDS, OFFSET, n);
        c_reverse_u32(data + OFFSET, n);
        require(memcmp(data, original, sizeof data) == 0, "reversal involution and frame");

        static const uint32_t fill_values[] = {0, UINT32_MAX, UINT32_C(0x80000001)};
        for (size_t j = 0; j < COUNT_OF(fill_values); ++j) {
            memcpy(data, original, sizeof data);
            c_fill_u32(data + OFFSET, n, fill_values[j]);
            for (size_t i = 0; i < n; ++i)
                require(data[OFFSET + i] == fill_values[j], "fill covers every destination element");
            check_u32_frame(data, original, WORDS, OFFSET, n);
        }

        memcpy(data, original, sizeof data);
        memcpy(saved_source, source, sizeof source);
        c_copy_u32(data + OFFSET, source + 3, n);
        require(memcmp(data + OFFSET, saved_source + 3, n * sizeof(uint32_t)) == 0,
                "copy matches the original source range");
        require(memcmp(source, saved_source, sizeof source) == 0, "copy preserves the source frame");
        check_u32_frame(data, original, WORDS, OFFSET, n);

        for (unsigned pattern = 0; pattern < 2; ++pattern) {
            memcpy(data, original, sizeof data);
            for (size_t i = 0; i < n; ++i)
                data[OFFSET + i] = pattern == 0 ? (uint32_t)i + 1 : UINT32_MAX;
            uint32_t before[WORDS];
            memcpy(before, data, sizeof data);
            c_prefix_sum_u32(data + OFFSET, n);
            for (size_t i = 0; i < n; ++i) {
                uint64_t length = i + 1;
                uint32_t expected = pattern == 0 ? (uint32_t)(length * (length + 1) / 2)
                    : (uint32_t)(UINT64_C(0x100000000) - length);
                require_u64(data[OFFSET + i], expected, "inclusive prefix closed form and wraparound");
                uint32_t previous = i == 0 ? 0 : data[OFFSET + i - 1];
                require((uint32_t)(data[OFFSET + i] - previous) == before[OFFSET + i],
                        "prefix finite differences recover the original sequence");
            }
            check_u32_frame(data, before, WORDS, OFFSET, n);
        }
    }
}

static void check_structs(void)
{
    struct framed {
        uint64_t before[2];
        struct c_u64x4 value;
        uint64_t after[2];
    };
    _Static_assert(sizeof(struct c_u64x4) == 4 * sizeof(uint64_t), "four-field native record ABI");
    static const struct c_u64x4 values[] = {
        {0, 0, 0, 0}, {1, 2, 3, 4},
        {UINT64_MAX, UINT64_MAX, UINT64_MAX, UINT64_MAX},
        {UINT64_MAX, 1, UINT64_C(0x8000000000000000), 7},
        {UINT64_C(0x0123456789abcdef), UINT64_C(0xfedcba9876543210), 17, 31},
        {0, 0, 0, UINT64_C(0x8000000000000000)},
    };
    for (size_t i = 0; i < COUNT_OF(values); ++i) {
        struct framed source = {{17, UINT64_MAX}, values[i], {31, UINT64_C(0xdeadbeef)}};
        struct framed destination = {{47, UINT64_C(0xabcdef01)}, {9, 8, 7, 6}, {59, 61}};
        struct framed saved_source = source, saved_destination = destination;
        c_struct_copy(&destination.value, &source.value);
        require(memcmp(&destination.value, &saved_source.value, sizeof source.value) == 0,
                "struct copy transfers all four fields");
        require(memcmp(destination.before, saved_destination.before, sizeof destination.before) == 0
                && memcmp(destination.after, saved_destination.after, sizeof destination.after) == 0,
                "struct copy destination frame");
        __uint128_t exact = (__uint128_t)values[i].a + values[i].b + values[i].c + values[i].d;
        require_u64(c_struct_sum(&source.value), (uint64_t)exact, "four-field sum reduced modulo 2^64");
        require(memcmp(&source, &saved_source, sizeof source) == 0, "struct source remains unchanged");
    }
}

static void check_atomics(void)
{
    struct {
        uint64_t before;
        _Atomic uint64_t value;
        uint64_t after;
    } frame = {UINT64_C(0x0123456789abcdef), 0, UINT64_C(0xfedcba9876543210)};
    uint64_t before = frame.before, after = frame.after;
    static const uint64_t values[] = {0, 1, UINT64_C(0x8000000000000000), UINT64_MAX - 1, UINT64_MAX};
    static const uint64_t deltas[] = {0, 1, 2, UINT64_C(0x100000001), UINT64_MAX};
    for (size_t i = 0; i < COUNT_OF(values); ++i) {
        atomic_store_explicit(&frame.value, values[i], memory_order_relaxed);
        require_u64(c_atomic_load_acquire64(&frame.value), values[i], "atomic acquire reads the word");
        c_atomic_store_release64(&frame.value, ~values[i]);
        require_u64(atomic_load_explicit(&frame.value, memory_order_relaxed), ~values[i],
                    "atomic release writes all 64 bits");
        for (size_t j = 0; j < COUNT_OF(deltas); ++j) {
            atomic_store_explicit(&frame.value, values[i], memory_order_relaxed);
            require_u64(c_atomic_fetch_add64(&frame.value, deltas[j]), values[i],
                        "fetch-add returns the old value");
            require_u64(atomic_load_explicit(&frame.value, memory_order_relaxed),
                        (uint64_t)((__uint128_t)values[i] + deltas[j]),
                        "atomic addition wraps modulo 2^64");
        }
        static const uint32_t iterations[] = {0, 1, 257};
        for (size_t j = 0; j < COUNT_OF(iterations); ++j) {
            atomic_store_explicit(&frame.value, values[i], memory_order_relaxed);
            c_counter_worker(&frame.value, iterations[j]);
            require_u64(atomic_load_explicit(&frame.value, memory_order_relaxed),
                        (uint64_t)((__uint128_t)values[i] + iterations[j]),
                        "sequential counter work including zero iterations and wraparound");
        }
    }
    require(frame.before == before && frame.after == after, "atomic operations preserve adjacent words");
}

struct counter_state {
    _Atomic uint64_t value;
    _Atomic bool start;
    uint32_t iterations;
};

enum { ticket_iterations = 50000, ticket_count = 2 * ticket_iterations };
struct ticket_state {
    _Atomic uint64_t value;
    _Atomic bool start;
    uint64_t returns[2][ticket_iterations];
};
struct ticket_argument { struct ticket_state *state; size_t index; };

static void *ticket_thread(void *argument)
{
    struct ticket_argument *entry = argument;
    while (!atomic_load_explicit(&entry->state->start, memory_order_acquire))
        sched_yield();
    for (size_t i = 0; i < ticket_iterations; ++i) {
        entry->state->returns[entry->index][i] =
            c_atomic_fetch_add64(&entry->state->value, 1);
        if (i % 128 == 0)
            sched_yield();
    }
    return NULL;
}

static void check_fetch_add_tickets(void)
{
    struct ticket_state *state = calloc(1, sizeof *state);
    bool *seen = calloc(ticket_count, sizeof *seen);
    require_system(state != NULL && seen != NULL, "calloc ticket buffers");
    uint64_t initial = UINT64_MAX - UINT64_C(12345);
    atomic_init(&state->value, initial);
    atomic_init(&state->start, false);
    pthread_t threads[2];
    struct ticket_argument arguments[2] = {{state, 0}, {state, 1}};
    for (size_t i = 0; i < COUNT_OF(threads); ++i)
        require_pthread(pthread_create(&threads[i], NULL, ticket_thread, &arguments[i]),
                        "pthread_create fetch-add tickets");
    atomic_store_explicit(&state->start, true, memory_order_release);
    for (size_t i = 0; i < COUNT_OF(threads); ++i)
        join_bounded(threads[i]);
    require_u64(atomic_load_explicit(&state->value, memory_order_relaxed),
                initial + ticket_count, "exported concurrent fetch-add loses no updates across wrap");
    /* The independently prescribed ticket set is the cyclic interval
     * initial+[0,ticket_count). The observer never reconstructs an execution. */
    for (size_t thread = 0; thread < COUNT_OF(threads); ++thread) {
        for (size_t i = 0; i < ticket_iterations; ++i) {
            uint64_t ticket = state->returns[thread][i] - initial;
            require(ticket < ticket_count, "fetch-add old value lies in the expected cyclic ticket interval");
            require(!seen[ticket], "concurrent exported fetch-add old values are unique");
            seen[ticket] = true;
        }
    }
    free(seen);
    free(state);
}

static void *counter_thread(void *argument)
{
    struct counter_state *state = argument;
    while (!atomic_load_explicit(&state->start, memory_order_acquire))
        sched_yield();
    c_counter_worker(&state->value, state->iterations);
    return NULL;
}

static void check_counter_threads(void)
{
    uint64_t initial = UINT64_MAX - UINT64_C(12345);
    struct counter_state state = {.value = initial, .start = false, .iterations = 200000};
    pthread_t threads[2];
    for (size_t i = 0; i < COUNT_OF(threads); ++i)
        require_pthread(pthread_create(&threads[i], NULL, counter_thread, &state), "pthread_create counter");
    atomic_store_explicit(&state.start, true, memory_order_release);
    for (size_t i = 0; i < COUNT_OF(threads); ++i)
        join_bounded(threads[i]);
    require_u64(atomic_load_explicit(&state.value, memory_order_relaxed),
                (uint64_t)((__uint128_t)initial + UINT64_C(2) * state.iterations),
                "two real counter workers preserve every increment through wraparound");
}

struct lock_state {
    _Atomic uint32_t lock;
    _Atomic bool start;
    _Atomic uint32_t inside;
    _Atomic bool overlap;
    uint64_t before;
    _Atomic uint64_t value;
    uint64_t after;
    uint32_t iterations;
};

static void *lock_thread(void *argument)
{
    struct lock_state *state = argument;
    while (!atomic_load_explicit(&state->start, memory_order_acquire))
        sched_yield();
    for (uint32_t i = 0; i < state->iterations; ++i) {
        c_spinlock_acquire(&state->lock);
        if (atomic_fetch_add_explicit(&state->inside, 1, memory_order_relaxed) != 0)
            atomic_store_explicit(&state->overlap, true, memory_order_relaxed);
        /* Separate relaxed atomic load/store keeps even a broken-lock
         * observation defined; mutual exclusion is needed to avoid loss. */
        uint64_t old = atomic_load_explicit(&state->value, memory_order_relaxed);
        if (i % 1024 == 0)
            sched_yield();
        atomic_store_explicit(&state->value, old + 1, memory_order_relaxed);
        if (atomic_fetch_sub_explicit(&state->inside, 1, memory_order_relaxed) != 1)
            atomic_store_explicit(&state->overlap, true, memory_order_relaxed);
        c_spinlock_release(&state->lock);
    }
    return NULL;
}

static void check_spinlock_threads(void)
{
    uint64_t initial = UINT64_MAX - 123;
    struct lock_state state = {
        .lock = 0, .start = false, .inside = 0, .overlap = false,
        .before = UINT64_C(0xa5a5a5a55a5a5a5a), .value = initial,
        .after = UINT64_C(0x5a5a5a5aa5a5a5a5), .iterations = 50000,
    };
    uint64_t before = state.before, after = state.after;
    c_spinlock_acquire(&state.lock);
    require_u64(atomic_load_explicit(&state.lock, memory_order_relaxed), 1, "acquire marks lock held");
    c_spinlock_release(&state.lock);
    require_u64(atomic_load_explicit(&state.lock, memory_order_relaxed), 0, "release marks lock free");
    pthread_t threads[2];
    for (size_t i = 0; i < COUNT_OF(threads); ++i)
        require_pthread(pthread_create(&threads[i], NULL, lock_thread, &state), "pthread_create spinlock");
    atomic_store_explicit(&state.start, true, memory_order_release);
    for (size_t i = 0; i < COUNT_OF(threads); ++i)
        join_bounded(threads[i]);
    require_u64(atomic_load_explicit(&state.value, memory_order_relaxed),
                (uint64_t)((__uint128_t)initial + UINT64_C(2) * state.iterations),
                "two spinlock workers protect separate atomic load/store increments");
    require(!atomic_load_explicit(&state.overlap, memory_order_relaxed)
            && atomic_load_explicit(&state.inside, memory_order_relaxed) == 0,
            "critical sections have exclusive observed occupancy");
    require(atomic_load_explicit(&state.lock, memory_order_relaxed) == 0
            && state.before == before && state.after == after, "spinlock final state and payload frame");
}

struct futex_state {
    uint32_t before;
    _Atomic uint32_t word;
    uint32_t after;
    _Atomic bool done;
    _Atomic uint64_t payload;
    uint64_t observed_payload;
    int32_t result;
};

static void *futex_thread(void *argument)
{
    struct futex_state *state = argument;
    state->result = c_futex_wait_loop(&state->word, 7);
    state->observed_payload = atomic_load_explicit(&state->payload, memory_order_relaxed);
    atomic_store_explicit(&state->done, true, memory_order_release);
    return NULL;
}

static long futex_wake(_Atomic uint32_t *word)
{
    long result = syscall(SYS_futex, word, FUTEX_WAKE_PRIVATE, 1, NULL, NULL, 0);
    require_system(result >= 0, "syscall FUTEX_WAKE_PRIVATE");
    require(result <= 1, "wake selects at most the requested one waiter");
    return result;
}

static void select_waiting_thread(struct futex_state *state)
{
    struct timespec deadline = deadline_after(CLOCK_MONOTONIC, 5);
    do {
        require(!atomic_load_explicit(&state->done, memory_order_acquire),
                "futex loop does not finish while the predicate still matches");
        /* A positive return, rather than a sleep or a userspace handshake,
         * establishes that the kernel actually selected a queued waiter. */
        if (futex_wake(&state->word) == 1)
            return;
        sched_yield();
    } while (before_deadline(deadline));
    require(false, "timed out waiting for a positive kernel futex wake count");
}

static void check_futex(void)
{
    /* Also bounds a broken mismatch implementation or an uninterruptible
     * userspace retry loop; timed joins alone do not cover direct calls. */
    alarm(15);
    struct futex_state state = {
        .before = UINT32_C(0x12345678), .word = 7, .after = UINT32_C(0x87654321),
        .done = false, .payload = 0, .observed_payload = 0, .result = -999,
    };
    uint32_t before = state.before, after = state.after;
    struct timespec immediate_deadline = deadline_after(CLOCK_MONOTONIC, 5);
    require(c_futex_wait_loop(&state.word, 8) == 0, "mismatching futex value returns zero");
    require(before_deadline(immediate_deadline), "mismatching futex does not block");
    pthread_t thread;
    require_pthread(pthread_create(&thread, NULL, futex_thread, &state), "pthread_create futex");
    select_waiting_thread(&state);
    /* Waking without a predicate change must lead back to a real kernel wait. */
    select_waiting_thread(&state);
    uint64_t message = UINT64_C(0xfedcba9876543210);
    atomic_store_explicit(&state.payload, message, memory_order_relaxed);
    atomic_store_explicit(&state.word, 9, memory_order_release);
    (void)futex_wake(&state.word);
    join_bounded(thread);
    require(state.result == 0, "waiter returns zero after a release-published predicate change");
    require_u64(state.observed_payload, message, "waiter observes the published payload");
    require(state.before == before && state.after == after, "futex loop preserves adjacent words");
    alarm(0);
}

int main(void)
{
    struct sigaction action = {.sa_handler = timeout_handler};
    require_system(sigemptyset(&action.sa_mask) == 0, "sigemptyset");
    require_system(sigaction(SIGALRM, &action, NULL) == 0, "sigaction timeout");
    alarm(60);
    check_scalars();
    check_bits();
    check_integer_loops();
    check_strings();
    check_read_arrays();
    check_array_mutations();
    check_structs();
    check_atomics();
    check_fetch_add_tickets();
    check_counter_threads();
    check_spinlock_threads();
    check_futex();
    puts("corpus-v1 native checks passed (observations only; no proof or linearizability claim)");
    return 0;
}
