/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <inttypes.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error "Comparison64 whole-call evidence requires Linux x86-64"
#endif
_Static_assert(CHAR_BIT == 8 && sizeof(uint64_t) == 8 && sizeof(void *) == 8 &&
    INT64_MIN == -INT64_MAX - 1, "Unsupported native integer/pointer representation");

enum { saved_count = 6, flag_profiles = 128, random_pairs = 8192 };
static const uint64_t arithmetic_flags = UINT64_C(0x8d5);
static const uint64_t direction_flag = UINT64_C(0x400);
static const uint64_t id_flag = UINT64_C(0x200000);
struct call_input { uint64_t left, right, saved[saved_count], flags; };
struct observation {
    uint64_t result, saved[saved_count], rsp_before, rsp_after, flags_before, flags_after;
};
_Static_assert(offsetof(struct call_input, saved) == 16 &&
    offsetof(struct call_input, flags) == 64 && sizeof(struct call_input) == 72 &&
    offsetof(struct observation, saved) == 8 && offsetof(struct observation, rsp_before) == 56 &&
    offsetof(struct observation, rsp_after) == 64 && offsetof(struct observation, flags_before) == 72 &&
    offsetof(struct observation, flags_after) == 80 && sizeof(struct observation) == 88,
    "Assembly whole-call capture ABI changed");
/* Single-threaded observer/recovery state; the probe restores the caller's
 * real stack, saved GPRs and flags before returning to C, even for mutants. */
struct call_input edsl_comparison64_input;
struct observation edsl_comparison64_output;
extern void edsl_comparison64_probe(const unsigned char *);

enum operation { unsigned_maximum, unsigned_minimum, signed_maximum };
struct contract {
    const char *name;
    const unsigned char *code, *end;
    enum operation operation;
};
#define POSITIVES(X) \
    X(gcc_maximum64,unsigned_maximum) \
    X(gcc_minimum64,unsigned_minimum) \
    X(gcc_signed_maximum64,signed_maximum) \
    X(clang_maximum64,unsigned_maximum) \
    X(clang_minimum64,unsigned_minimum) \
    X(clang_signed_maximum64,signed_maximum)
#define DECLARE(name,operation) \
    extern const unsigned char edsl_comparison64_##name[], edsl_comparison64_##name##_end[];
POSITIVES(DECLARE)
#define ENTRY(name,operation) \
    {#name,edsl_comparison64_##name,edsl_comparison64_##name##_end,operation},
static const struct contract positives[] = { POSITIVES(ENTRY) };

enum failure {
    bad_result = 1, bad_saved = 2, bad_stack = 4, bad_nonarithmetic_flags = 8, bad_setup = 16
};
struct mutant { struct contract contract; unsigned int reason; };
#define MUTANTS(X) \
    X(bad_maximum_direction,unsigned_maximum,bad_result) \
    X(bad_minimum_direction,unsigned_minimum,bad_result) \
    X(bad_signed_direction,signed_maximum,bad_result) \
    X(bad_maximum_signedness,unsigned_maximum,bad_result) \
    X(bad_minimum_signedness,unsigned_minimum,bad_result) \
    X(bad_signed_signedness,signed_maximum,bad_result) \
    X(bad_signed_overflow,signed_maximum,bad_result) \
    X(bad_operand,unsigned_maximum,bad_result) \
    X(bad_narrowing,unsigned_maximum,bad_result) \
    X(bad_rbx,unsigned_maximum,bad_saved) \
    X(bad_rbp,unsigned_maximum,bad_saved) \
    X(bad_r12,unsigned_maximum,bad_saved) \
    X(bad_r13,unsigned_maximum,bad_saved) \
    X(bad_r14,unsigned_maximum,bad_saved) \
    X(bad_r15,unsigned_maximum,bad_saved) \
    X(bad_rsp,unsigned_maximum,bad_stack) \
    X(bad_df,unsigned_maximum,bad_nonarithmetic_flags) \
    X(bad_id,unsigned_maximum,bad_nonarithmetic_flags)
#define DECLARE_MUTANT(name,operation,reason) extern const unsigned char edsl_comparison64_##name[];
MUTANTS(DECLARE_MUTANT)
#define MUTANT_ENTRY(name,operation,reason) \
    {{#name,edsl_comparison64_##name,NULL,operation},reason},
static const struct mutant mutants[] = { MUTANTS(MUTANT_ENTRY) };

/* Requested mathematical postconditions, independent of fixture instructions:
 * the result is an input and bounds both inputs in the requested order. There
 * is no instruction decoder, opcode-derived predicate or subtraction oracle. */
static int mathematical_result(enum operation operation, uint64_t left, uint64_t right,
    uint64_t result)
{
    if (result != left && result != right) return 0;
    switch (operation) {
    case unsigned_maximum: return result >= left && result >= right;
    case unsigned_minimum: return result <= left && result <= right;
    case signed_maximum: {
        int64_t signed_left, signed_right, signed_result;
        memcpy(&signed_left, &left, sizeof left);
        memcpy(&signed_right, &right, sizeof right);
        memcpy(&signed_result, &result, sizeof result);
        return signed_result >= signed_left && signed_result >= signed_right;
    }
    }
    abort();
}

/* Exact byte identity is checked for all six complete final .text files before
 * any native probe or positive evidence is emitted. The executed images were
 * embedded from these extractions with .incbin, not assembled from a decoder. */
static int same_extraction(const struct contract *contract, const char *path)
{
    const size_t size = (size_t)((uintptr_t)contract->end - (uintptr_t)contract->code);
    if (size == 0 || size == SIZE_MAX) return 0;
    FILE *file = fopen(path, "rb");
    if (!file) return 0;
    unsigned char *bytes = malloc(size + 1);
    if (!bytes) { fclose(file); return 0; }
    const size_t amount = fread(bytes, 1, size + 1, file);
    const int failed = ferror(file);
    const int closed = fclose(file);
    const int matches = !failed && closed == 0 && amount == size &&
        memcmp(bytes, contract->code, size) == 0;
    free(bytes);
    return matches;
}

static uint64_t flags_for(unsigned int profile)
{
    static const unsigned int positions[] = {0,2,4,6,7,11,21};
    uint64_t flags = 0;
    for (size_t i = 0; i < sizeof positions / sizeof positions[0]; ++i)
        if ((profile >> i) & 1) flags |= UINT64_C(1) << positions[i];
    return flags;
}

static unsigned int observe(const struct contract *contract, uint64_t left, uint64_t right,
    unsigned int profile)
{
    static const uint64_t saved[] = {
        UINT64_C(0x0123456789abcdef), UINT64_C(0xfedcba9876543210),
        UINT64_C(0x13579bdf2468ace0), UINT64_C(0xeca86420fdb97531),
        UINT64_C(0xa55a5aa50ff0f00f), UINT64_C(0x5aa5a55af00f0ff0)
    };
    edsl_comparison64_input.left = left;
    edsl_comparison64_input.right = right;
    edsl_comparison64_input.flags = flags_for(profile);
    for (size_t i = 0; i < saved_count; ++i)
        edsl_comparison64_input.saved[i] = saved[i] ^ ((uint64_t)profile << 32);
    edsl_comparison64_probe(contract->code);
    const struct observation *observed = &edsl_comparison64_output;
    const uint64_t installed_mask = arithmetic_flags | direction_flag | id_flag;
    if ((observed->flags_before & installed_mask) != edsl_comparison64_input.flags ||
        (observed->rsp_before & UINT64_C(15)) != 0) return bad_setup;
    unsigned int failures = 0;
    if (!mathematical_result(contract->operation, left, right, observed->result)) failures |= bad_result;
    if (memcmp(edsl_comparison64_input.saved, observed->saved, sizeof observed->saved) != 0)
        failures |= bad_saved;
    if (observed->rsp_after != observed->rsp_before) failures |= bad_stack;
    if (((observed->flags_before ^ observed->flags_after) & ~arithmetic_flags) != 0)
        failures |= bad_nonarithmetic_flags;
    return failures;
}

static void describe(FILE *file, const struct contract *contract, uint64_t left, uint64_t right,
    unsigned int profile, unsigned int failures)
{
    const struct observation *observed = &edsl_comparison64_output;
    fprintf(file, "%s left=%016" PRIx64 " right=%016" PRIx64 " profile=%u result=%016" PRIx64
        " failures=%u rsp=%016" PRIx64 "/%016" PRIx64 " flags=%016" PRIx64 "/%016" PRIx64 "\n",
        contract->name, left, right, profile, observed->result, failures,
        observed->rsp_before, observed->rsp_after, observed->flags_before, observed->flags_after);
}

static const uint64_t edges[] = {
    0,1,2,3,7,UINT64_C(0x7f),UINT64_C(0x80),UINT64_C(0xff),UINT64_C(0x100),
    UINT64_C(0x7fff),UINT64_C(0x8000),UINT64_C(0xffff),UINT64_C(0x10000),
    UINT64_C(0x7fffffff),UINT64_C(0x80000000),UINT64_C(0xffffffff),
    UINT64_C(0x100000000),UINT64_C(0x100000001),UINT64_C(0x7fffffff00000000),
    UINT64_C(0x7ffffffffffffffe),UINT64_C(0x7fffffffffffffff),UINT64_C(0x8000000000000000),
    UINT64_C(0x8000000000000001),UINT64_C(0x80000000ffffffff),UINT64_C(0xfffffffeffffffff),
    UINT64_C(0xffffffff00000000),UINT64_MAX-1,UINT64_MAX,
    UINT64_C(0x5555555555555555),UINT64_C(0xaaaaaaaaaaaaaaaa),
    UINT64_C(0x0123456789abcdef),UINT64_C(0xfedcba9876543210)
};
static int positive_case(const struct contract *contract, uint64_t left, uint64_t right,
    unsigned int profile, uint64_t *calls)
{
    const unsigned int failures = observe(contract, left, right, profile);
    if (failures) { describe(stderr, contract, left, right, profile, failures); return 0; }
    ++*calls;
    return 1;
}
static int all_profiles(const struct contract *contract, uint64_t left, uint64_t right, uint64_t *calls)
{
    for (unsigned int profile = 0; profile < flag_profiles; ++profile)
        if (!positive_case(contract, left, right, profile, calls)) return 0;
    return 1;
}
/* Deterministic operand generation only; this is never an expected-result
 * computation. All arithmetic intentionally uses defined uint64_t wraparound. */
static uint64_t next_operand(uint64_t *state)
{
    uint64_t value = (*state += UINT64_C(0x9e3779b97f4a7c15));
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}
static int run_positive(const struct contract *contract, uint64_t *calls)
{
    const size_t count = sizeof edges / sizeof edges[0];
    for (size_t i = 0; i < count; ++i)
    for (size_t j = 0; j < count; ++j)
        if (!all_profiles(contract, edges[i], edges[j], calls)) return 0;
    /* Both sides of every bit boundary, both argument orders and equality;
     * includes the signed overflow boundaries without subtracting operands. */
    for (unsigned int bit = 0; bit < 64; ++bit) {
        const uint64_t power = UINT64_C(1) << bit;
        const uint64_t pairs[][2] = {
            {power-1,power},{power,power-1},{power,power},
            {UINT64_MAX-power,UINT64_MAX},{UINT64_MAX,UINT64_MAX-power},
            {UINT64_MAX-power,UINT64_MAX-power}
        };
        for (size_t i = 0; i < sizeof pairs / sizeof pairs[0]; ++i)
            if (!all_profiles(contract, pairs[i][0], pairs[i][1], calls)) return 0;
    }
    uint64_t state = UINT64_C(0x434f4d5041524536);
    for (unsigned int i = 0; i < random_pairs; ++i) {
        const uint64_t left = next_operand(&state);
        const uint64_t generated = next_operand(&state);
        const uint64_t right = i % 16 == 0 ? left : generated;
        if (!positive_case(contract, left, right, i % flag_profiles, calls)) return 0;
    }
    return 1;
}

static int rejects_mutant(const struct mutant *mutant)
{
    const size_t count = sizeof edges / sizeof edges[0];
    for (size_t i = 0; i < count; ++i)
    for (size_t j = 0; j < count; ++j) {
        const unsigned int failures = observe(&mutant->contract, edges[i], edges[j], 0);
        if (failures == mutant->reason) {
            fputs("REJECTED owned mutant: ", stdout);
            describe(stdout, &mutant->contract, edges[i], edges[j], 0, failures);
            return 1;
        }
        if (failures != 0) {
            fputs("Unexpected mutant observation: ", stderr);
            describe(stderr, &mutant->contract, edges[i], edges[j], 0, failures);
            return 0;
        }
    }
    fprintf(stderr, "Owned mutant survived independent oracle: %s\n", mutant->contract.name);
    return 0;
}

int main(int argc, char **argv)
{
    const size_t count = sizeof positives / sizeof positives[0];
    if (argc != (int)count + 1) {
        fputs("usage: native-check GCC_MAX GCC_MIN GCC_SIGNED_MAX CLANG_MAX CLANG_MIN CLANG_SIGNED_MAX\n",
            stderr);
        return 2;
    }
    for (size_t i = 0; i < count; ++i) {
        if (!same_extraction(&positives[i], argv[i+1])) {
            fprintf(stderr, "Final ELF section extraction differs from executed bytes: %s\n", positives[i].name);
            return 2;
        }
    }
    uint64_t total = 0;
    for (size_t i = 0; i < count; ++i) {
        uint64_t calls = 0;
        if (!run_positive(&positives[i], &calls)) return 1;
        total += calls;
        printf("PASS %s: %" PRIu64 " whole calls, full64 order/result, six saved GPRs, RSP, nonarithmetic RFLAGS\n",
            positives[i].name, calls);
    }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i)
        if (!rejects_mutant(&mutants[i])) return 1;
    printf("PASS finite native evidence: %" PRIu64 " positive calls, %zu owned mutants rejected; no Lean proof run\n",
        total, sizeof mutants / sizeof mutants[0]);
    return 0;
}
