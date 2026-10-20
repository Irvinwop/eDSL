/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <inttypes.h>
#include <limits.h>
#include <pthread.h>
#include <sched.h>
#include <stddef.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error "LockedSet64 native evidence requires Linux x86-64"
#endif
_Static_assert(CHAR_BIT == 8 && sizeof(uint64_t) == 8 && sizeof(void *) == 8 &&
    sizeof(_Atomic uint64_t) == 8, "Unsupported atomic/integer representation");

enum { gpr_count = 15, flag_profiles = 256, seeded_pairs = 8192,
    worker_count = 8, masks_per_worker = 8, worker_rounds = 257 };
enum gpr { reg_rax, reg_rbx, reg_rcx, reg_rdx, reg_rsi, reg_rdi, reg_rbp,
    reg_r8, reg_r9, reg_r10, reg_r11, reg_r12, reg_r13, reg_r14, reg_r15 };
static const uint64_t arithmetic_flags = UINT64_C(0x8d5); /* AF included */
static const uint64_t installed_flags = UINT64_C(0x200cd5);
struct call_input { uint64_t regs[gpr_count], flags; };
struct observation {
    uint64_t regs[gpr_count], rsp_before, rsp_after, flags_before, flags_after;
    uint64_t return_slot, stack_guards[4];
};
_Static_assert(offsetof(struct call_input, flags) == 120 && sizeof(struct call_input) == 128 &&
    offsetof(struct observation, rsp_before) == 120 &&
    offsetof(struct observation, rsp_after) == 128 &&
    offsetof(struct observation, flags_before) == 136 &&
    offsetof(struct observation, flags_after) == 144 &&
    offsetof(struct observation, return_slot) == 152 &&
    offsetof(struct observation, stack_guards) == 160 && sizeof(struct observation) == 192,
    "Assembly observation layout changed");
struct call_input edsl_set64_input;
struct observation edsl_set64_output;
extern void edsl_set64_probe(const unsigned char *);
extern const unsigned char edsl_set64_return[];

/* A real initialized atomic object, separate from its guard bytes. Its eight
 * bytes start at a 64-byte boundary, within one virtual line and 4-KiB page.
 * All pthread users finish before its next reset. No raw concurrent C reads. */
struct arena {
    _Alignas(64) unsigned char before[64];
    _Alignas(64) _Atomic uint64_t value;
    unsigned char after[56];
};
_Static_assert(offsetof(struct arena, value) == 64 && offsetof(struct arena, after) == 72 &&
    sizeof(struct arena) == 128 && _Alignof(struct arena) == 64,
    "Atomic arena geometry changed");
static struct arena cell;
static uint64_t last_word;
static unsigned char last_bytes[8];
typedef void (*atomic_function)(_Atomic uint64_t *, uint64_t);
enum operation { set_intersection, set_union, set_symmetric_difference };
struct contract {
    const char *name;
    const unsigned char *code, *end;
    atomic_function call;
    enum operation operation;
};
#define DECLARE(name) \
    extern void edsl_set64_##name(_Atomic uint64_t *, uint64_t); \
    extern const unsigned char edsl_set64_##name##_start[], edsl_set64_##name##_end[];
#define ENTRY(name,op) \
    {#name, edsl_set64_##name##_start, edsl_set64_##name##_end, edsl_set64_##name, op},
#define POSITIVES(X) \
X(gcc_c_and64,set_intersection) \
    X(gcc_c_or64,set_union) \
    X(gcc_c_xor64,set_symmetric_difference) \
    X(clang_c_and64,set_intersection) \
    X(clang_c_or64,set_union) \
    X(clang_c_xor64,set_symmetric_difference) \
    X(clang_cpp_and64,set_intersection) \
    X(clang_cpp_or64,set_union) \
    X(clang_cpp_xor64,set_symmetric_difference)
#define DECLARE_POSITIVE(name,op) DECLARE(name)
POSITIVES(DECLARE_POSITIVE)
static const struct contract positives[] = { POSITIVES(ENTRY) };
#define CONTROLS(X) \
X(and_af_clear,set_intersection) \
    X(and_af_set,set_intersection) \
    X(and_unlocked,set_intersection) \
    X(or_af_clear,set_union) \
    X(or_af_set,set_union) \
    X(or_unlocked,set_union) \
    X(xor_af_clear,set_symmetric_difference) \
    X(xor_af_set,set_symmetric_difference) \
    X(xor_unlocked,set_symmetric_difference)
CONTROLS(DECLARE_POSITIVE)
static const struct contract controls[] = { CONTROLS(ENTRY) };
enum failure { bad_membership = 1, bad_endian = 2, bad_gpr = 4, bad_stack = 8,
    bad_flags = 16, bad_guard = 32, bad_setup = 64, bad_nonarithmetic_flags = 128 };
#define MUTANTS(X) \
X(and_bad_width32,set_intersection,bad_membership) \
    X(and_bad_width16,set_intersection,bad_membership) \
    X(and_bad_source,set_intersection,bad_membership) \
    X(and_bad_mask,set_intersection,bad_membership) \
    X(and_bad_operation,set_intersection,bad_membership) \
    X(and_bad_fetched_rax,set_intersection,bad_gpr) \
    X(and_bad_rax,set_intersection,bad_gpr) \
    X(and_bad_rbx,set_intersection,bad_gpr) \
    X(and_bad_rcx,set_intersection,bad_gpr) \
    X(and_bad_rdx,set_intersection,bad_gpr) \
    X(and_bad_rsi,set_intersection,bad_gpr) \
    X(and_bad_rdi,set_intersection,bad_gpr) \
    X(and_bad_rbp,set_intersection,bad_gpr) \
    X(and_bad_r8,set_intersection,bad_gpr) \
    X(and_bad_r9,set_intersection,bad_gpr) \
    X(and_bad_r10,set_intersection,bad_gpr) \
    X(and_bad_r11,set_intersection,bad_gpr) \
    X(and_bad_r12,set_intersection,bad_gpr) \
    X(and_bad_r13,set_intersection,bad_gpr) \
    X(and_bad_r14,set_intersection,bad_gpr) \
    X(and_bad_r15,set_intersection,bad_gpr) \
    X(and_bad_rsp,set_intersection,bad_stack) \
    X(and_bad_guard_before,set_intersection,bad_guard) \
    X(and_bad_guard_after,set_intersection,bad_guard) \
    X(and_bad_cf,set_intersection,bad_flags) \
    X(and_bad_pf,set_intersection,bad_flags) \
    X(and_bad_zf,set_intersection,bad_flags) \
    X(and_bad_sf,set_intersection,bad_flags) \
    X(and_bad_of,set_intersection,bad_flags) \
    X(and_bad_flags_unchanged,set_intersection,bad_flags) \
    X(and_bad_df,set_intersection,bad_nonarithmetic_flags) \
    X(and_bad_id,set_intersection,bad_nonarithmetic_flags) \
    X(or_bad_width32,set_union,bad_membership) \
    X(or_bad_width16,set_union,bad_membership) \
    X(or_bad_source,set_union,bad_membership) \
    X(or_bad_mask,set_union,bad_membership) \
    X(or_bad_operation,set_union,bad_membership) \
    X(or_bad_fetched_rax,set_union,bad_gpr) \
    X(or_bad_rax,set_union,bad_gpr) \
    X(or_bad_rbx,set_union,bad_gpr) \
    X(or_bad_rcx,set_union,bad_gpr) \
    X(or_bad_rdx,set_union,bad_gpr) \
    X(or_bad_rsi,set_union,bad_gpr) \
    X(or_bad_rdi,set_union,bad_gpr) \
    X(or_bad_rbp,set_union,bad_gpr) \
    X(or_bad_r8,set_union,bad_gpr) \
    X(or_bad_r9,set_union,bad_gpr) \
    X(or_bad_r10,set_union,bad_gpr) \
    X(or_bad_r11,set_union,bad_gpr) \
    X(or_bad_r12,set_union,bad_gpr) \
    X(or_bad_r13,set_union,bad_gpr) \
    X(or_bad_r14,set_union,bad_gpr) \
    X(or_bad_r15,set_union,bad_gpr) \
    X(or_bad_rsp,set_union,bad_stack) \
    X(or_bad_guard_before,set_union,bad_guard) \
    X(or_bad_guard_after,set_union,bad_guard) \
    X(or_bad_cf,set_union,bad_flags) \
    X(or_bad_pf,set_union,bad_flags) \
    X(or_bad_zf,set_union,bad_flags) \
    X(or_bad_sf,set_union,bad_flags) \
    X(or_bad_of,set_union,bad_flags) \
    X(or_bad_flags_unchanged,set_union,bad_flags) \
    X(or_bad_df,set_union,bad_nonarithmetic_flags) \
    X(or_bad_id,set_union,bad_nonarithmetic_flags) \
    X(xor_bad_width32,set_symmetric_difference,bad_membership) \
    X(xor_bad_width16,set_symmetric_difference,bad_membership) \
    X(xor_bad_source,set_symmetric_difference,bad_membership) \
    X(xor_bad_mask,set_symmetric_difference,bad_membership) \
    X(xor_bad_operation,set_symmetric_difference,bad_membership) \
    X(xor_bad_fetched_rax,set_symmetric_difference,bad_gpr) \
    X(xor_bad_rax,set_symmetric_difference,bad_gpr) \
    X(xor_bad_rbx,set_symmetric_difference,bad_gpr) \
    X(xor_bad_rcx,set_symmetric_difference,bad_gpr) \
    X(xor_bad_rdx,set_symmetric_difference,bad_gpr) \
    X(xor_bad_rsi,set_symmetric_difference,bad_gpr) \
    X(xor_bad_rdi,set_symmetric_difference,bad_gpr) \
    X(xor_bad_rbp,set_symmetric_difference,bad_gpr) \
    X(xor_bad_r8,set_symmetric_difference,bad_gpr) \
    X(xor_bad_r9,set_symmetric_difference,bad_gpr) \
    X(xor_bad_r10,set_symmetric_difference,bad_gpr) \
    X(xor_bad_r11,set_symmetric_difference,bad_gpr) \
    X(xor_bad_r12,set_symmetric_difference,bad_gpr) \
    X(xor_bad_r13,set_symmetric_difference,bad_gpr) \
    X(xor_bad_r14,set_symmetric_difference,bad_gpr) \
    X(xor_bad_r15,set_symmetric_difference,bad_gpr) \
    X(xor_bad_rsp,set_symmetric_difference,bad_stack) \
    X(xor_bad_guard_before,set_symmetric_difference,bad_guard) \
    X(xor_bad_guard_after,set_symmetric_difference,bad_guard) \
    X(xor_bad_cf,set_symmetric_difference,bad_flags) \
    X(xor_bad_pf,set_symmetric_difference,bad_flags) \
    X(xor_bad_zf,set_symmetric_difference,bad_flags) \
    X(xor_bad_sf,set_symmetric_difference,bad_flags) \
    X(xor_bad_of,set_symmetric_difference,bad_flags) \
    X(xor_bad_flags_unchanged,set_symmetric_difference,bad_flags) \
    X(xor_bad_df,set_symmetric_difference,bad_nonarithmetic_flags) \
    X(xor_bad_id,set_symmetric_difference,bad_nonarithmetic_flags)
#define DECLARE_MUTANT(name,op,reason) DECLARE(name)
MUTANTS(DECLARE_MUTANT)
struct mutant { struct contract contract; unsigned int reason; };
#define MUTANT_ENTRY(name,op,reason) {{#name,edsl_set64_##name##_start, \
    edsl_set64_##name##_end,edsl_set64_##name,op},reason},
static const struct mutant mutants[] = { MUTANTS(MUTANT_ENTRY) };

/* Independent finite-set contract: i is in S(word) iff floor(word/2^i)
 * mod 2 is one. No whole-word AND/OR/XOR expression or instruction/model decoder
 * supplies an expected result. The byte oracle separately locates bit i at
 * byte floor(i/8), bit i mod 8, checking little-endian physical readback. */
static int member(uint64_t word, unsigned int bit) { return (word >> bit) % 2 != 0; }
static int expected_member(enum operation operation, int left, int right)
{
    switch (operation) {
    case set_intersection: return left && right;
    case set_union: return left || right;
    case set_symmetric_difference: return left != right;
    }
    abort();
}
static int membership_ok(enum operation operation, uint64_t old, uint64_t mask, uint64_t actual)
{
    for (unsigned int bit = 0; bit < 64; ++bit)
        if (member(actual, bit) != expected_member(operation, member(old, bit), member(mask, bit))) return 0;
    return 1;
}
static int endian_ok(enum operation operation, uint64_t old, uint64_t mask, const unsigned char bytes[8])
{
    for (unsigned int bit = 0; bit < 64; ++bit)
        if ((int)((bytes[bit / 8] >> (bit % 8)) % 2) !=
                expected_member(operation, member(old, bit), member(mask, bit))) return 0;
    return 1;
}
static int logical_flags_ok(enum operation operation, uint64_t old, uint64_t mask, uint64_t flags)
{
    unsigned int low_members = 0, all_members = 0;
    for (unsigned int bit = 0; bit < 64; ++bit) {
        const unsigned int present = (unsigned int)expected_member(operation, member(old, bit), member(mask, bit));
        all_members += present;
        if (bit < 8) low_members += present;
    }
    return !member(flags, 0) && !member(flags, 11) &&
        member(flags, 2) == (low_members % 2 == 0) &&
        member(flags, 6) == (all_members == 0) &&
        member(flags, 7) == expected_member(operation, member(old, 63), member(mask, 63));
    /* AF (bit 4) is deliberately never compared. */
}
static uint64_t flags_for(unsigned int profile)
{
    static const unsigned int positions[] = {0,2,4,6,7,11,10,21};
    uint64_t flags = 0;
    for (size_t i = 0; i < sizeof positions / sizeof positions[0]; ++i)
        if ((profile >> i) % 2) flags += UINT64_C(1) << positions[i];
    return flags;
}
static void prepare_guards(unsigned int profile)
{
    for (size_t i = 0; i < sizeof cell.before; ++i)
        cell.before[i] = (unsigned char)(17 * i + profile + 0x35);
    for (size_t i = 0; i < sizeof cell.after; ++i)
        cell.after[i] = (unsigned char)(29 * i + profile + 0xa7);
}
static unsigned int observe(const struct contract *contract, uint64_t old, uint64_t mask,
    unsigned int profile, int reset)
{
    static const uint64_t seeds[gpr_count] = {
        UINT64_C(0x91b2c3d4e5f60718), UINT64_C(0x0123456789abcdef),
        UINT64_C(0x5379bdf12468ace0), UINT64_C(0xd0e1f20314253647),
        0,0, UINT64_C(0xfedcba9876543210), UINT64_C(0x16c80e2a94b7d35f),
        UINT64_C(0xa3d179f60b5e842c), UINT64_C(0x74eac820953fd16b),
        UINT64_C(0xc628fa049d13b75e), UINT64_C(0x13579bdf2468ace0),
        UINT64_C(0xeca86420fdb97531), UINT64_C(0xa55a5aa50ff0f00f),
        UINT64_C(0x5aa5a55af00f0ff0)
    };
    static const uint64_t stack_guards[] = { UINT64_C(0x6d3a8271f0b459ce),
        UINT64_C(0xa159c7302edb864f), UINT64_C(0x38b64fa20dc195e7),
        UINT64_C(0xf4719dce620ba358) };
    if (reset) atomic_store_explicit(&cell.value, old, memory_order_seq_cst);
    else if (atomic_load_explicit(&cell.value, memory_order_seq_cst) != old) return bad_setup;
    prepare_guards(profile);
    unsigned char before[sizeof cell.before], after[sizeof cell.after];
    memcpy(before, cell.before, sizeof before);
    memcpy(after, cell.after, sizeof after);
    for (size_t i = 0; i < gpr_count; ++i)
        edsl_set64_input.regs[i] = seeds[i] ^ ((uint64_t)profile << 32);
    edsl_set64_input.regs[reg_rdi] = (uintptr_t)&cell.value;
    edsl_set64_input.regs[reg_rsi] = mask;
    edsl_set64_input.flags = flags_for(profile);
    edsl_set64_probe(contract->code);
    last_word = atomic_load_explicit(&cell.value, memory_order_seq_cst);
    /* Quiescent object-representation inspection only. */
    memcpy(last_bytes, &cell.value, sizeof last_bytes);
    const struct observation *out = &edsl_set64_output;
    if ((out->flags_before & installed_flags) != edsl_set64_input.flags ||
        out->rsp_before % 16 != 0) return bad_setup;
    unsigned int failures = 0;
    if (!membership_ok(contract->operation, old, mask, last_word)) failures |= bad_membership;
    if (!endian_ok(contract->operation, old, mask, last_bytes)) failures |= bad_endian;
    if (memcmp(out->regs, edsl_set64_input.regs, sizeof out->regs)) failures |= bad_gpr;
    if (out->rsp_after != out->rsp_before ||
        out->return_slot != (uintptr_t)edsl_set64_return ||
        memcmp(out->stack_guards, stack_guards, sizeof stack_guards)) failures |= bad_stack;
    if (!logical_flags_ok(contract->operation, old, mask, out->flags_after)) failures |= bad_flags;
    if (((out->flags_before ^ out->flags_after) & ~arithmetic_flags) != 0)
        failures |= bad_nonarithmetic_flags;
    if (memcmp(before, cell.before, sizeof before) || memcmp(after, cell.after, sizeof after))
        failures |= bad_guard;
    return failures;
}
static void describe(FILE *file, const struct contract *contract, uint64_t old, uint64_t mask,
    unsigned int profile, unsigned int failures)
{
    fprintf(file, "%s old=%016" PRIx64 " mask=%016" PRIx64 " actual=%016" PRIx64
        " profile=%u failures=%u flags=%016" PRIx64 "/%016" PRIx64 "\n",
        contract->name, old, mask, last_word, profile, failures,
        edsl_set64_output.flags_before, edsl_set64_output.flags_after);
}
static int positive_case(const struct contract *contract, uint64_t old, uint64_t mask,
    unsigned int profile, int reset, uint64_t *calls)
{
    const unsigned int failures = observe(contract, old, mask, profile, reset);
    if (failures) { describe(stderr, contract, old, mask, profile, failures); return 0; }
    ++*calls;
    return 1;
}
static int all_profiles(const struct contract *contract, uint64_t old, uint64_t mask,
    uint64_t *calls)
{
    for (unsigned int p = 0; p < flag_profiles; ++p)
        if (!positive_case(contract, old, mask, p, 1, calls)) return 0;
    return 1;
}
static const uint64_t edges[] = {
    0,1,2,3,7,UINT64_C(0x7f),UINT64_C(0x80),UINT64_C(0xff),UINT64_C(0x100),
    UINT64_C(0x7fffffff),UINT64_C(0x80000000),UINT64_C(0xffffffff),
    UINT64_C(0x100000000),UINT64_C(0x100000001),UINT64_C(0x7fffffff00000000),
    UINT64_C(0x7fffffffffffffff),UINT64_C(0x8000000000000000),
    UINT64_C(0x8000000000000001),UINT64_C(0x80000000ffffffff),
    UINT64_C(0xffffffff00000000),UINT64_MAX-1,UINT64_MAX,
    UINT64_C(0x5555555555555555),UINT64_C(0xaaaaaaaaaaaaaaaa),
    UINT64_C(0x0123456789abcdef),UINT64_C(0xfedcba9876543210)
};
static int boundary_pairs(const struct contract *contract, uint64_t *calls)
{
    for (size_t i = 0; i < sizeof edges / sizeof edges[0]; ++i)
    for (size_t j = 0; j < sizeof edges / sizeof edges[0]; ++j)
        if (!all_profiles(contract, edges[i], edges[j], calls)) return 0;
    return 1;
}
/* Deterministic input generation only; never expected-result computation. */
static uint64_t next_operand(uint64_t *state)
{
    uint64_t value = (*state += UINT64_C(0x9e3779b97f4a7c15));
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}
static int sequence_cases(const struct contract *contract, uint64_t *calls)
{
    static const uint64_t initial[] = {0,UINT64_C(0x100),UINT64_C(0x8000000000000000),UINT64_MAX};
    static const uint64_t masks[] = {0,1,UINT64_C(0x100000000),UINT64_C(0x8000000000000000),
        1,UINT64_C(0x8000000100000001),UINT64_C(0x100000000),0,
        UINT64_C(0x81),UINT64_C(0x80),UINT64_C(0x8000000000000080),0};
    for (size_t s = 0; s < sizeof initial / sizeof initial[0]; ++s)
    for (unsigned int p = 0; p < flag_profiles; ++p) {
        atomic_store_explicit(&cell.value, initial[s], memory_order_seq_cst);
        int present[64];
        for (unsigned int bit = 0; bit < 64; ++bit) present[bit] = member(initial[s], bit);
        for (size_t m = 0; m < sizeof masks / sizeof masks[0]; ++m) {
            const uint64_t old = atomic_load_explicit(&cell.value, memory_order_seq_cst);
            if (!positive_case(contract, old, masks[m], p, 0, calls)) return 0;
            for (unsigned int bit = 0; bit < 64; ++bit) {
                present[bit] = expected_member(contract->operation, present[bit], member(masks[m], bit));
                if (member(last_word, bit) != present[bit]) return 0;
            }
        }
    }
    return 1;
}
static int run_positive(const struct contract *contract, uint64_t *calls)
{
    if (!boundary_pairs(contract, calls)) return 0;
    for (unsigned int bit = 0; bit < 64; ++bit) {
        const uint64_t power = UINT64_C(1) << bit;
        for (unsigned int fill = 0; fill < 2; ++fill) {
            const uint64_t background = fill ? UINT64_MAX - power : 0;
            for (unsigned int a = 0; a < 2; ++a)
            for (unsigned int b = 0; b < 2; ++b)
                if (!all_profiles(contract, background + a * power, background + b * power, calls))
                    return 0;
        }
    }
    static const uint64_t seeds[] = {UINT64_C(0x41544f4d49433634),
        UINT64_C(0x3141592653589793),UINT64_C(0xfedcba9876543210)};
    for (size_t s = 0; s < sizeof seeds / sizeof seeds[0]; ++s) {
        uint64_t state = seeds[s];
        for (unsigned int i = 0; i < seeded_pairs; ++i) {
            const uint64_t old = next_operand(&state), generated = next_operand(&state);
            const uint64_t mask = i % 16 == 0 ? 0 : i % 16 == 1 ? old : generated;
            if (!positive_case(contract, old, mask, i % flag_profiles, 1, calls)) return 0;
        }
    }
    if (!sequence_cases(contract, calls)) return 0;
    if (!positive_case(contract, UINT64_C(0x0000000100000080), UINT64_C(0x8000000000000001),
            255, 1, calls)) return 0;
    /* Literal vectors are specified independently for these concrete operands. */
    static const unsigned char literal[3][8] = {
        {0,0,0,0,0,0,0,0}, {0x81,0,0,0,1,0,0,0x80}, {0x81,0,0,0,1,0,0,0x80}
    };
    if (memcmp(last_bytes, literal[contract->operation], 8)) return 0;
    /* Equal high/low mask: XOR must cancel, AND/OR retain both bits. */
    if (!positive_case(contract, UINT64_C(0x8000000000000001), UINT64_C(0x8000000000000001),
            0, 1, calls)) return 0;
    static const unsigned char equal_literal[3][8] = {
        {1,0,0,0,0,0,0,0x80}, {1,0,0,0,0,0,0,0x80}, {0,0,0,0,0,0,0,0}
    };
    if (memcmp(last_bytes, equal_literal[contract->operation], 8)) return 0;
    printf("PASS independently specified endian/cancellation literals %s\n", contract->name);
    return 1;
}
static int rejects_mutant(const struct mutant *mutant)
{
    const unsigned int allowed = mutant->reason == bad_membership ?
        bad_membership | bad_endian | bad_flags : mutant->reason;
    for (size_t i = 0; i < sizeof edges / sizeof edges[0]; ++i)
    for (size_t j = 0; j < sizeof edges / sizeof edges[0]; ++j)
    for (unsigned int p = 0; p < flag_profiles; ++p) {
        const unsigned int failures = observe(&mutant->contract, edges[i], edges[j], p, 1);
        if ((failures & mutant->reason) && !(failures & ~allowed)) {
            fputs("REJECTED owned mutant: ", stdout);
            describe(stdout, &mutant->contract, edges[i], edges[j], p, failures);
            return 1;
        }
        /* A narrow operation can first fail only SF/ZF before a later input
         * exposes truncated data. Keep searching for the requested witness;
         * never attribute a flags-only rejection to the membership oracle. */
        if (failures & ~allowed) {
            fputs("Unexpected mutant failure: ", stderr);
            describe(stderr, &mutant->contract, edges[i], edges[j], p, failures);
            return 0;
        }
    }
    fprintf(stderr, "Owned mutant survived oracle: %s\n", mutant->contract.name);
    return 0;
}

/* Validate ALL NINE complete loaded execution slots before ANY native probe,
 * worker or positive stdout. File inputs remain data, never entry addresses.
 * The admitted file must itself be exactly the supported five bytes. */
static int same_extraction(const struct contract *contract, const char *path)
{
    static const unsigned char identities[3][5] = {
        {0xf0,0x48,0x21,0x37,0xc3}, {0xf0,0x48,0x09,0x37,0xc3}, {0xf0,0x48,0x31,0x37,0xc3}
    };
    const unsigned char *identity = identities[contract->operation];
    const size_t identity_size = sizeof identities[0];
    if ((uintptr_t)contract->end - (uintptr_t)contract->code != identity_size) return 0;
    FILE *file = fopen(path, "rb");
    if (!file) return 0;
    unsigned char bytes[identity_size + 1];
    const size_t amount = fread(bytes, 1, sizeof bytes, file);
    const int failed = ferror(file), closed = fclose(file);
    return !failed && closed == 0 && amount == identity_size &&
        !memcmp(bytes, identity, identity_size) && !memcmp(bytes, contract->code, identity_size);
}

struct worker {
    atomic_function call;
    uint64_t masks[masks_per_worker], calls;
    unsigned int rounds;
};
/* Static storage also remains live if a pthread operation fails. On join
 * failure main exits immediately without inspecting possibly active data. */
static struct worker workers[worker_count];
static _Atomic int start_workers;
static void *worker_main(void *argument)
{
    struct worker *worker = argument;
    while (!atomic_load_explicit(&start_workers, memory_order_acquire)) sched_yield();
    for (unsigned int round = 0; round < worker->rounds; ++round)
    for (unsigned int i = 0; i < masks_per_worker; ++i) {
        worker->call(&cell.value, worker->masks[(i + round) % masks_per_worker]);
        ++worker->calls;
    }
    return worker;
}
static int threaded_case(const struct contract *contract, unsigned int workload, uint64_t *calls)
{
    const uint64_t initial = contract->operation == set_intersection ? UINT64_MAX :
        workload == 0 ? UINT64_C(0x10000) : workload == 1 ? UINT64_C(0x80000081) :
        workload == 2 ? UINT64_C(0x100000000) : UINT64_C(0xa55a5aa50ff0f00f);
    /* Independent history contract: count each bit's requests, including every
     * repetition. AND requires membership in ALL masks; OR in at least one;
     * XOR toggles iff the total count is odd. No whole-word logical fold. */
    uint64_t requested[64] = {0}, history_length = 0;
    uint64_t random = UINT64_C(0x7a8ce4219b60d35f);
    for (unsigned int w = 0; w < worker_count; ++w) {
        workers[w].call = contract->call;
        workers[w].calls = 0;
        workers[w].rounds = workload == 1 ? worker_rounds + 1 :
            workload == 2 ? worker_rounds + w % 2 : worker_rounds;
        for (unsigned int i = 0; i < masks_per_worker; ++i) {
            uint64_t mask;
            if (workload == 0) mask = i == 0 ? UINT64_C(1) << w :
                i == 1 ? UINT64_C(1) << (w + 56) : 0;
            else if (workload == 1) mask = UINT64_C(1) << (32 + (w + i) % 32);
            else if (workload == 2) mask = i % 3 == 0 ? 0 :
                i % 3 == 1 ? UINT64_C(0x8000000100000001) : UINT64_C(0x100000081);
            else mask = UINT64_C(1) << (next_operand(&random) % 64);
            if (contract->operation == set_intersection) mask = UINT64_MAX - mask;
            workers[w].masks[i] = mask;
            history_length += workers[w].rounds;
            for (unsigned int bit = 0; bit < 64; ++bit)
                if (member(mask, bit)) requested[bit] += workers[w].rounds;
        }
    }
    prepare_guards(workload);
    unsigned char before[sizeof cell.before], after[sizeof cell.after];
    memcpy(before, cell.before, sizeof before);
    memcpy(after, cell.after, sizeof after);
    atomic_store_explicit(&cell.value, initial, memory_order_seq_cst);
    atomic_store_explicit(&start_workers, 0, memory_order_release);
    pthread_t threads[worker_count];
    unsigned int created = 0;
    int create_failed = 0, join_failed = 0;
    for (unsigned int w = 0; w < worker_count; ++w) {
        const int error = pthread_create(&threads[w], NULL, worker_main, &workers[w]);
        if (error) {
            fprintf(stderr, "pthread_create workload=%u worker=%u error=%d (%s)\n",
                workload, w, error, strerror(error));
            create_failed = 1;
            break;
        }
        ++created;
    }
    atomic_store_explicit(&start_workers, 1, memory_order_release);
    for (unsigned int w = 0; w < created; ++w) {
        void *returned = NULL;
        const int error = pthread_join(threads[w], &returned);
        if (error || returned != &workers[w]) {
            fprintf(stderr, "pthread_join workload=%u worker=%u error=%d returned_matches=%d\n",
                workload, w, error, returned == &workers[w]);
            join_failed = 1;
        }
    }
    if (create_failed || join_failed) return 0;
    const uint64_t actual = atomic_load_explicit(&cell.value, memory_order_seq_cst);
    unsigned char bytes[8];
    memcpy(bytes, &cell.value, sizeof bytes);
    uint64_t expected = 0;
    for (unsigned int bit = 0; bit < 64; ++bit) {
        const int present = contract->operation == set_intersection ?
            member(initial, bit) && requested[bit] == history_length :
            contract->operation == set_union ? member(initial, bit) || requested[bit] != 0 :
            (member(initial, bit) + requested[bit]) % 2 != 0;
        if (member(actual, bit) != present ||
            (int)((bytes[bit / 8] >> (bit % 8)) % 2) != present) {
            fprintf(stderr, "Thread independent history mismatch: %s workload=%u bit=%u actual=%016" PRIx64 "\n",
                contract->name, workload, bit, actual);
            return 0;
        }
        if (present) expected += UINT64_C(1) << bit;
    }
    if (memcmp(before, cell.before, sizeof before) || memcmp(after, cell.after, sizeof after)) return 0;
    for (unsigned int w = 0; w < worker_count; ++w) {
        if (workers[w].calls != workers[w].rounds * masks_per_worker) return 0;
        *calls += workers[w].calls;
    }
    printf("PASS pthread %s workload=%u create=8/8 join=8/8 calls=%" PRIu64 " initial=%016" PRIx64
        " bit_history=%016" PRIx64 " actual=%016" PRIx64 " guards=preserved\n",
        contract->name, workload, history_length, initial, expected, actual);
    return 1;
}

int main(int argc, char **argv)
{
    const size_t count = sizeof positives / sizeof positives[0];
    if (argc != (int)count + 1) {
        fputs("usage: native-check GCC_C_AND GCC_C_OR GCC_C_XOR CLANG_C_AND CLANG_C_OR CLANG_C_XOR CLANG_CPP_AND CLANG_CPP_OR CLANG_CPP_XOR\n", stderr);
        return 2;
    }
    for (size_t i = 0; i < count; ++i)
        if (!same_extraction(&positives[i], argv[i+1])) {
            fprintf(stderr, "Extraction rejected before native execution: %s\n", positives[i].name);
            return 2;
        }
    atomic_init(&cell.value, 0);
    atomic_init(&start_workers, 0);
    const uintptr_t address = (uintptr_t)&cell.value;
    if (!atomic_is_lock_free(&cell.value) || address % 8 || address % 64 + 8 > 64 ||
        address % 4096 + 8 > 4096 || sysconf(_SC_PAGESIZE) != 4096) {
        fputs("Unsupported atomic representation or virtual memory geometry\n", stderr);
        return 2;
    }
    printf("SETUP initialized live _Atomic uint64_t: size=8 alignment=64 lock_free=1 page=4096\n");
    uint64_t total = 0, control_calls = 0, thread_calls = 0;
    for (size_t i = 0; i < count; ++i) {
        uint64_t calls = 0;
        if (!run_positive(&positives[i], &calls)) return 1;
        total += calls;
        printf("PASS %s: %" PRIu64 " calls; full64 membership/endian/guards, all 15 non-RSP GPRs, "
            "stack/return slot, defined flags, 256 pre-flags; AF unrestricted\n", positives[i].name, calls);
    }
    for (size_t i = 0; i < sizeof controls / sizeof controls[0]; ++i) {
        uint64_t calls = 0;
        if (!boundary_pairs(&controls[i], &calls)) return 1;
        /* Observe that the two acceptance controls actually exercise both
         * undefined AF outcomes; their names alone establish nothing. */
        if (i % 3 != 2 && member(edsl_set64_output.flags_after, 4) != (int)(i % 3)) {
            fprintf(stderr, "AF acceptance control did not produce its requested outcome: %s\n",
                controls[i].name);
            return 1;
        }
        control_calls += calls;
        printf("PASS control %s: %" PRIu64 " single-thread calls%s\n", controls[i].name, calls,
            i % 3 == 2 ? "; missing LOCK is observationally indistinguishable here; no atomicity evidence" :
            "; either undefined AF value admitted");
    }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i)
        if (!rejects_mutant(&mutants[i])) return 1;
    for (size_t i = 0; i < count; ++i)
    for (unsigned int workload = 0; workload < 4; ++workload)
        if (!threaded_case(&positives[i], workload, &thread_calls)) return 1;
    printf("PASS finite native evidence: compiler_calls=%" PRIu64 " control_calls=%" PRIu64
        " pthread_calls=%" PRIu64 " owned_mutants=%zu; proof-status NOT RUN; "
        "no LOCK/CPU/C/C++ source proof\n", total, control_calls, thread_calls, sizeof mutants / sizeof mutants[0]);
    return 0;
}
