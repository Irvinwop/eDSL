/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <inttypes.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error "Logical64 whole-call evidence requires Linux x86-64"
#endif
_Static_assert(CHAR_BIT == 8 && sizeof(uint64_t) == 8 && sizeof(void *) == 8,
    "Unsupported native integer/pointer representation");

enum { saved_count = 6, flag_profiles = 128, seeded_pairs = 8192 };
/* All six arithmetic flags, including undefined AF, are unconstrained by the
 * scalar contract. Only effective nonarithmetic flags must be preserved. */
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
/* Single-threaded recovery globals. Assembly restores the real caller's
 * stack, saved GPRs and flags even after the owned ABI mutants. */
struct call_input edsl_logical64_input;
struct observation edsl_logical64_output;
extern void edsl_logical64_probe(const unsigned char *);

enum operation { intersection, union_membership, symmetric_difference };
struct contract {
    const char *name;
    const unsigned char *code, *end;
    enum operation operation;
};
#define POSITIVES(X) \
    X(gcc_intersection64,intersection) \
    X(gcc_union64,union_membership) \
    X(gcc_symmetric_difference64,symmetric_difference) \
    X(clang_intersection64,intersection) \
    X(clang_union64,union_membership) \
    X(clang_symmetric_difference64,symmetric_difference)
#define DECLARE(name,operation) \
    extern const unsigned char edsl_logical64_##name[], edsl_logical64_##name##_end[];
POSITIVES(DECLARE)
#define ENTRY(name,operation) \
    {#name,edsl_logical64_##name,edsl_logical64_##name##_end,operation},
static const struct contract positives[] = { POSITIVES(ENTRY) };

/* Acceptance controls deliberately set every arithmetic flag, including AF.
 * Their mathematical results and ABI are still checked independently. */
#define CONTROLS(X) \
    X(allowed_intersection_flags,intersection) \
    X(allowed_union_flags,union_membership) \
    X(allowed_difference_flags,symmetric_difference)
CONTROLS(DECLARE)
static const struct contract controls[] = { CONTROLS(ENTRY) };

enum failure {
    bad_result = 1, bad_saved = 2, bad_stack = 4, bad_nonarithmetic_flags = 8, bad_setup = 16
};
struct mutant { struct contract contract; unsigned int reason; };
#define MUTANTS(X) \
    X(bad_intersection_union,intersection,bad_result) \
    X(bad_intersection_difference,intersection,bad_result) \
    X(bad_union_intersection,union_membership,bad_result) \
    X(bad_union_difference,union_membership,bad_result) \
    X(bad_difference_intersection,symmetric_difference,bad_result) \
    X(bad_difference_union,symmetric_difference,bad_result) \
    X(bad_intersection_width,intersection,bad_result) \
    X(bad_union_width,union_membership,bad_result) \
    X(bad_difference_width,symmetric_difference,bad_result) \
    X(bad_intersection_operand,intersection,bad_result) \
    X(bad_union_operand,union_membership,bad_result) \
    X(bad_difference_operand,symmetric_difference,bad_result) \
    X(bad_rbx,intersection,bad_saved) \
    X(bad_rbp,intersection,bad_saved) \
    X(bad_r12,intersection,bad_saved) \
    X(bad_r13,intersection,bad_saved) \
    X(bad_r14,intersection,bad_saved) \
    X(bad_r15,intersection,bad_saved) \
    X(bad_rsp,intersection,bad_stack) \
    X(bad_df,intersection,bad_nonarithmetic_flags) \
    X(bad_id,intersection,bad_nonarithmetic_flags)
#define DECLARE_MUTANT(name,operation,reason) extern const unsigned char edsl_logical64_##name[];
MUTANTS(DECLARE_MUTANT)
#define MUTANT_ENTRY(name,operation,reason) \
    {{#name,edsl_logical64_##name,NULL,operation},reason},
static const struct mutant mutants[] = { MUTANTS(MUTANT_ENTRY) };

/* Define S(word) = {bit in [0,64) | floor(word / 2^bit) mod 2 = 1}.
 * Each output position must obey the requested finite-set membership truth:
 * intersection is membership in both sets, union in either set, symmetric
 * difference in exactly one set. No whole-word logical result computation,
 * instruction decoder or Lean backend supplies an expected result. */
static int mathematical_result(enum operation operation, uint64_t left, uint64_t right,
    uint64_t result)
{
    for (unsigned int bit = 0; bit < 64; ++bit) {
        const int in_left = (left >> bit) % 2 != 0;
        const int in_right = (right >> bit) % 2 != 0;
        const int in_result = (result >> bit) % 2 != 0;
        int present;
        switch (operation) {
        case intersection: present = in_left && in_right; break;
        case union_membership: present = in_left || in_right; break;
        case symmetric_difference: present = in_left != in_right; break;
        default: abort();
        }
        if (in_result != present) return 0;
    }
    return 1;
}

/* All six exact extractions must match the actually loaded executable slots
 * before the first probe or positive output. Inputs are only read as data;
 * they never become code pointers, executable mappings or syscall programs. */
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
    edsl_logical64_input.left = left;
    edsl_logical64_input.right = right;
    edsl_logical64_input.flags = flags_for(profile);
    for (size_t i = 0; i < saved_count; ++i)
        edsl_logical64_input.saved[i] = saved[i] ^ ((uint64_t)profile << 32);
    edsl_logical64_probe(contract->code);
    const struct observation *observed = &edsl_logical64_output;
    const uint64_t installed_mask = arithmetic_flags | direction_flag | id_flag;
    if ((observed->flags_before & installed_mask) != edsl_logical64_input.flags ||
        (observed->rsp_before & UINT64_C(15)) != 0) return bad_setup;
    unsigned int failures = 0;
    if (!mathematical_result(contract->operation, left, right, observed->result)) failures |= bad_result;
    if (memcmp(edsl_logical64_input.saved, observed->saved, sizeof observed->saved) != 0)
        failures |= bad_saved;
    if (observed->rsp_after != observed->rsp_before) failures |= bad_stack;
    if (((observed->flags_before ^ observed->flags_after) & ~arithmetic_flags) != 0)
        failures |= bad_nonarithmetic_flags;
    return failures;
}

static void describe(FILE *file, const struct contract *contract, uint64_t left, uint64_t right,
    unsigned int profile, unsigned int failures)
{
    const struct observation *observed = &edsl_logical64_output;
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
static int boundary_pairs(const struct contract *contract, uint64_t *calls)
{
    const size_t count = sizeof edges / sizeof edges[0];
    for (size_t i = 0; i < count; ++i)
    for (size_t j = 0; j < count; ++j)
        if (!all_profiles(contract, edges[i], edges[j], calls)) return 0;
    return 1;
}
/* Deterministic input generation only, never expected-result computation.
 * Arithmetic intentionally uses defined uint64_t wraparound. */
static uint64_t next_operand(uint64_t *state)
{
    uint64_t value = (*state += UINT64_C(0x9e3779b97f4a7c15));
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}
static int run_positive(const struct contract *contract, uint64_t *calls)
{
    if (!boundary_pairs(contract, calls)) return 0;
    /* All four membership combinations at every position, with all other
     * positions either absent or present. This includes bits 32 through 63. */
    for (unsigned int bit = 0; bit < 64; ++bit) {
        const uint64_t power = UINT64_C(1) << bit;
        for (unsigned int fill = 0; fill < 2; ++fill) {
            const uint64_t background = fill ? UINT64_MAX - power : 0;
            for (unsigned int left_member = 0; left_member < 2; ++left_member)
            for (unsigned int right_member = 0; right_member < 2; ++right_member)
                if (!all_profiles(contract, background + left_member * power,
                        background + right_member * power, calls)) return 0;
        }
        const uint64_t pairs[][2] = {
            {power,UINT64_MAX-power},{UINT64_MAX-power,power},
            {power,power},{UINT64_MAX-power,UINT64_MAX-power}
        };
        for (size_t i = 0; i < sizeof pairs / sizeof pairs[0]; ++i)
            if (!all_profiles(contract, pairs[i][0], pairs[i][1], calls)) return 0;
    }
    static const uint64_t seeds[] = {
        UINT64_C(0x4c4f474943414c36), UINT64_C(0x3141592653589793), UINT64_C(0xfedcba9876543210)
    };
    for (size_t seed = 0; seed < sizeof seeds / sizeof seeds[0]; ++seed) {
        uint64_t state = seeds[seed];
        for (unsigned int i = 0; i < seeded_pairs; ++i) {
            const uint64_t left = next_operand(&state);
            const uint64_t generated = next_operand(&state);
            const uint64_t right = i % 16 == 0 ? left :
                i % 16 == 1 ? UINT64_MAX - left : generated;
            if (!positive_case(contract, left, right, i % flag_profiles, calls)) return 0;
        }
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
        fputs("usage: native-check GCC_INTERSECTION GCC_UNION GCC_DIFFERENCE CLANG_INTERSECTION CLANG_UNION CLANG_DIFFERENCE\n",
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
        printf("PASS %s: %" PRIu64 " whole calls, full64 membership, six saved GPRs, RSP, nonarithmetic RFLAGS\n",
            positives[i].name, calls);
    }
    uint64_t control_calls = 0;
    for (size_t i = 0; i < sizeof controls / sizeof controls[0]; ++i)
        if (!boundary_pairs(&controls[i], &control_calls)) return 1;
    printf("PASS permitted arithmetic-flag controls: %" PRIu64 " whole calls across %zu owned controls\n",
        control_calls, sizeof controls / sizeof controls[0]);
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i)
        if (!rejects_mutant(&mutants[i])) return 1;
    printf("PASS finite native evidence: %" PRIu64 " compiler-output calls, %" PRIu64
        " control calls, %zu owned mutants rejected; no Lean proof run\n",
        total, control_calls, sizeof mutants / sizeof mutants[0]);
    return 0;
}
