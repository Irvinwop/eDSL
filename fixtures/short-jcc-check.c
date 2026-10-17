/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <inttypes.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error "Short-Jcc native evidence requires Linux x86-64 and the System V ABI"
#endif
_Static_assert(CHAR_BIT == 8 && sizeof(uint64_t) == 8 && sizeof(void *) == 8,
    "Unsupported native representation");
struct observation { uintptr_t reached; uint64_t before, after; };
_Static_assert(offsetof(struct observation, before) == 8 &&
    offsetof(struct observation, after) == 16 && sizeof(struct observation) == 24,
    "Assembly capture ABI changed");
struct observation edsl_short_jcc_observation;
extern void edsl_short_jcc_probe(const unsigned char *, uint64_t);
extern const unsigned char edsl_short_jcc_images_begin[], edsl_short_jcc_images_end[];

enum condition {
    overflow, not_overflow, below, above_equal, equal, not_equal, below_equal, above,
    sign, not_sign, parity, not_parity, less, greater_equal, less_equal, greater
};
/* This oracle describes named x86 conditions directly from effective flags.
 * It neither decodes bytes nor derives expected answers from the asm paths.
 * AF and ID are deliberately irrelevant and varied independently. */
static int condition_holds(enum condition condition, uint64_t flags)
{
    const int cf = (flags & UINT64_C(0x1)) != 0;
    const int pf = (flags & UINT64_C(0x4)) != 0;
    const int zf = (flags & UINT64_C(0x40)) != 0;
    const int sf = (flags & UINT64_C(0x80)) != 0;
    const int of = (flags & UINT64_C(0x800)) != 0;
    switch (condition) {
    case overflow: return of;
    case not_overflow: return !of;
    case below: return cf;
    case above_equal: return !cf;
    case equal: return zf;
    case not_equal: return !zf;
    case below_equal: return cf || zf;
    case above: return !cf && !zf;
    case sign: return sf;
    case not_sign: return !sf;
    case parity: return pf;
    case not_parity: return !pf;
    case less: return sf != of;
    case greater_equal: return sf == of;
    case less_equal: return zf || sf != of;
    case greater: return !zf && sf == of;
    }
    abort();
}
#define CONDITIONS(X) \
    X(overflow,0x70) X(not_overflow,0x71) X(below,0x72) X(above_equal,0x73) \
    X(equal,0x74) X(not_equal,0x75) X(below_equal,0x76) X(above,0x77) \
    X(sign,0x78) X(not_sign,0x79) X(parity,0x7a) X(not_parity,0x7b) \
    X(less,0x7c) X(greater_equal,0x7d) X(less_equal,0x7e) X(greater,0x7f)
#define DECLARE(name) \
    extern const unsigned char edsl_short_jcc_##name##_begin[], \
        edsl_short_jcc_##name##_entry[], edsl_short_jcc_##name##_branch[], \
        edsl_short_jcc_##name##_fallthrough[], edsl_short_jcc_##name##_taken[], \
        edsl_short_jcc_##name##_physical_taken[], edsl_short_jcc_##name##_end[];
#define DECLARE_BOTH(name,opcode) DECLARE(name##_forward) DECLARE(name##_backward)
CONDITIONS(DECLARE_BOTH)
DECLARE(bad_inverse)
DECLARE(bad_displacement)
DECLARE(bad_flags)
struct fixture {
    const char *name;
    enum condition condition;
    const unsigned char *begin, *entry, *branch, *fallthrough, *taken, *physical_taken, *end;
    unsigned int opcode;
    int displacement;
    int flag_prefix;
};
#define FIXTURE(name,condition,opcode,displacement,prefix) \
    {#name,condition,edsl_short_jcc_##name##_begin,edsl_short_jcc_##name##_entry, \
    edsl_short_jcc_##name##_branch,edsl_short_jcc_##name##_fallthrough, \
    edsl_short_jcc_##name##_taken,edsl_short_jcc_##name##_physical_taken, \
    edsl_short_jcc_##name##_end,opcode,displacement,prefix}
#define BOTH(name,opcode) \
    FIXTURE(name##_forward,name,opcode,127,0), FIXTURE(name##_backward,name,opcode,-128,0),
static const struct fixture positives[] = { CONDITIONS(BOTH) };
enum failure { wrong_path = 1, changed_flags = 2, bad_setup = 4 };
struct mutant { struct fixture fixture; unsigned int reason; unsigned int witnesses; };
static const struct mutant mutants[] = {
    {FIXTURE(bad_inverse,overflow,0x71,127,0),wrong_path,128},
    {FIXTURE(bad_displacement,overflow,0x70,119,0),wrong_path,64},
    {FIXTURE(bad_flags,overflow,0x70,127,1),changed_flags,128}
};

static uint64_t flags_for(unsigned int profile)
{
    static const unsigned int positions[] = {0,2,4,6,7,11,21};
    uint64_t flags = 0;
    for (size_t i = 0; i < sizeof positions / sizeof positions[0]; ++i)
        if ((profile >> i) & 1U) flags |= UINT64_C(1) << positions[i];
    return flags;
}
static unsigned int observe(const struct fixture *fixture, unsigned int profile)
{
    const uint64_t requested = flags_for(profile);
    edsl_short_jcc_probe(fixture->entry, requested);
    const struct observation *observed = &edsl_short_jcc_observation;
    if ((observed->before & UINT64_C(0x200cd5)) != requested) return bad_setup;
    const uintptr_t expected = (uintptr_t)(condition_holds(fixture->condition, observed->before) ?
        fixture->taken : fixture->fallthrough);
    unsigned int failures = 0;
    if (observed->reached != expected) failures |= wrong_path;
    if (observed->before != observed->after) failures |= changed_flags;
    return failures;
}
static void describe(FILE *file, const struct fixture *fixture, unsigned int profile,
    unsigned int failures)
{
    const struct observation *observed = &edsl_short_jcc_observation;
    fprintf(file, "%s profile=%u flags=%016" PRIx64 "/%016" PRIx64
        " reached=%016" PRIxPTR " failures=%u\n", fixture->name, profile,
        observed->before, observed->after, observed->reached, failures);
}

/* Before the first execution, check actual emitted rel8 opcode, signed target,
 * path labels and section bounds. Only the owned statically linked entries can
 * reach the observer; supplied files are compared, never mapped/executed. */
static int emitted_layout(const struct fixture *fixture)
{
    const uintptr_t begin = (uintptr_t)fixture->begin;
    const uintptr_t end = (uintptr_t)fixture->end;
    const uintptr_t branch = (uintptr_t)fixture->branch;
    const uintptr_t entry = (uintptr_t)fixture->entry;
    const uintptr_t image_begin = (uintptr_t)edsl_short_jcc_images_begin;
    const uintptr_t image_end = (uintptr_t)edsl_short_jcc_images_end;
    if (begin < image_begin || end > image_end || begin >= end ||
        entry < begin || entry >= end || branch < begin || branch + 2 > end ||
        (uintptr_t)fixture->fallthrough != branch + 2 ||
        (uintptr_t)fixture->taken < begin || (uintptr_t)fixture->taken >= end ||
        (uintptr_t)fixture->physical_taken < begin || (uintptr_t)fixture->physical_taken >= end)
        return 0;
    if (fixture->branch[0] != fixture->opcode) return 0;
    const int encoded = fixture->branch[1] <= 127 ? fixture->branch[1] :
        (int)fixture->branch[1] - 256;
    if (encoded != fixture->displacement ||
        (uintptr_t)((intptr_t)(branch + 2) + encoded) != (uintptr_t)fixture->physical_taken)
        return 0;
    if (fixture->flag_prefix)
        return branch == entry + 1 && fixture->entry[0] == 0xf5;
    return entry == branch;
}
static int same_extraction(const char *path)
{
    const size_t size = (size_t)((uintptr_t)edsl_short_jcc_images_end -
        (uintptr_t)edsl_short_jcc_images_begin);
    if (size == 0 || size == SIZE_MAX) return 0;
    FILE *file = fopen(path, "rb");
    if (!file) return 0;
    unsigned char *bytes = malloc(size + 1);
    if (!bytes) { fclose(file); return 0; }
    const size_t amount = fread(bytes, 1, size + 1, file);
    const int failed = ferror(file);
    const int closed = fclose(file);
    const int matches = !failed && closed == 0 && amount == size &&
        memcmp(bytes, edsl_short_jcc_images_begin, size) == 0;
    free(bytes);
    return matches;
}
int main(int argc, char **argv)
{
    if (argc != 2 || !same_extraction(argv[1])) {
        fputs("Owned fixture section differs from executed bytes\n", stderr);
        return 2;
    }
    for (size_t i = 0; i < sizeof positives / sizeof positives[0]; ++i)
        if (!emitted_layout(&positives[i])) {
            fprintf(stderr, "Unsupported emitted fixture layout: %s\n", positives[i].name);
            return 2;
        }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i)
        if (!emitted_layout(&mutants[i].fixture)) {
            fprintf(stderr, "Unsupported emitted mutant layout: %s\n", mutants[i].fixture.name);
            return 2;
        }
    uint64_t calls = 0;
    for (size_t i = 0; i < sizeof positives / sizeof positives[0]; ++i) {
        const struct fixture *fixture = &positives[i];
        for (unsigned int profile = 0; profile < 128; ++profile) {
            const unsigned int failures = observe(fixture, profile);
            if (failures) { describe(stderr, fixture, profile, failures); return 1; }
            ++calls;
        }
        printf("PASS %s opcode=%02x displacement=%d profiles=128\n", fixture->name,
            fixture->opcode, fixture->displacement);
    }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        const struct mutant *mutant = &mutants[i];
        unsigned int witnesses = 0;
        for (unsigned int profile = 0; profile < 128; ++profile) {
            const unsigned int failures = observe(&mutant->fixture, profile);
            if (failures != 0 && failures != mutant->reason) {
                describe(stderr, &mutant->fixture, profile, failures);
                return 1;
            }
            if (failures == mutant->reason) {
                if (witnesses == 0) describe(stdout, &mutant->fixture, profile, failures);
                ++witnesses;
            }
        }
        if (witnesses != mutant->witnesses) {
            fprintf(stderr, "Mutant rejection witnesses: %s expected=%u actual=%u\n",
                mutant->fixture.name, mutant->witnesses, witnesses);
            return 1;
        }
        printf("REJECT %s expected-reason=%u profiles=%u/128\n", mutant->fixture.name,
            mutant->reason, witnesses);
    }
    printf("PASS %" PRIu64 " positive calls; all 16 conditions, both signed rel8 boundaries, "
        "all 64 arithmetic flag profiles with both ID values; 3 synthetic mutants rejected\n", calls);
    return 0;
}
