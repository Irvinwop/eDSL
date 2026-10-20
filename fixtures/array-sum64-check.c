/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <inttypes.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error "ArraySum64 native evidence requires Linux x86-64/System V"
#endif
_Static_assert(CHAR_BIT == 8 && sizeof(uint64_t) == 8 && sizeof(void *) == 8,
    "Unsupported native integer/pointer representation");

enum { saved_count = 6, extra_count = 4, flag_profiles = 128, random_arrays = 1024 };
static const uint64_t arithmetic_flags = UINT64_C(0x8d5);
static const uint64_t direction_flag = UINT64_C(0x400);
static const uint64_t id_flag = UINT64_C(0x200000);
struct call_input {
    uint64_t base, count, initial_rax, saved[saved_count], extra[extra_count], flags;
};
struct observation {
    uint64_t result, saved[saved_count], arguments[2], extra[extra_count];
    uint64_t rsp_before, rsp_after, flags_before, flags_after;
};
_Static_assert(offsetof(struct call_input, initial_rax) == 16 &&
    offsetof(struct call_input, saved) == 24 && offsetof(struct call_input, extra) == 72 &&
    offsetof(struct call_input, flags) == 104 && sizeof(struct call_input) == 112 &&
    offsetof(struct observation, saved) == 8 && offsetof(struct observation, arguments) == 56 &&
    offsetof(struct observation, extra) == 72 && offsetof(struct observation, rsp_before) == 104 &&
    offsetof(struct observation, rsp_after) == 112 && offsetof(struct observation, flags_before) == 120 &&
    offsetof(struct observation, flags_after) == 128 && sizeof(struct observation) == 136,
    "Assembly observer ABI changed");
/* Single-threaded recovery globals. Raw base bits let empty calls exercise an
 * unused invalid address without constructing/dereferencing a C data pointer. */
struct call_input edsl_array_sum64_input;
struct observation edsl_array_sum64_output;
extern void edsl_array_sum64_probe(const unsigned char *);
extern const unsigned char edsl_array_sum64_gcc[], edsl_array_sum64_gcc_end[];
extern const unsigned char edsl_array_sum64_clang[], edsl_array_sum64_clang_end[];

/* Artifact identity only, deliberately separate from the mathematical oracle.
 * Even a manually rebuilt observer cannot probe a substituted .incbin image. */
static const unsigned char gcc_profile[] =
    "\x31\xc0\x31\xd2\x48\x39\xf0\x74\x09\x48\x03\x14\xc7\x48\xff\xc0"
    "\xeb\xf2\x48\x89\xd0\xc3";
static const unsigned char clang_profile[] =
    "\x48\x85\xf6\x74\x11\x31\xc9\x31\xc0\x48\x03\x04\xcf\x48\xff\xc1"
    "\x48\x39\xce\x75\xf4\xc3\x31\xc0\xc3";
_Static_assert(sizeof gcc_profile - 1 == 22 && sizeof clang_profile - 1 == 25,
    "Complete final compiler profiles changed");
struct program {
    const char *name;
    const unsigned char *code, *end, *profile;
    size_t profile_size;
};
static const struct program positives[] = {
    {"gcc_sum64_array", edsl_array_sum64_gcc, edsl_array_sum64_gcc_end,
        gcc_profile, sizeof gcc_profile - 1},
    {"clang_sum64_array", edsl_array_sum64_clang, edsl_array_sum64_clang_end,
        clang_profile, sizeof clang_profile - 1}
};
enum failure {
    bad_result = 1, nonzero_empty = 4, changed_input = 8,
    changed_saved = 16, changed_arguments = 32, changed_extra = 64,
    changed_stack = 128, changed_nonarithmetic = 256, bad_setup = 512
};
enum witness { ordered, high_sign, wide, carry, empty };
struct mutant {
    struct program program;
    enum witness witness;
    unsigned int reason;
    const char *reason_name;
};
#define MUTANTS(X) \
    X(bad_xor,ordered,bad_result,"modular-sum") \
    X(bad_sign_extend,high_sign,bad_result,"modular-sum") \
    X(bad_narrowing,wide,bad_result,"modular-sum") \
    X(bad_skip_last,ordered,bad_result,"modular-sum") \
    X(bad_zero,ordered,bad_result,"modular-sum") \
    X(bad_saturating,carry,bad_result,"modular-sum") \
    X(bad_empty,empty,nonzero_empty,"empty-result") \
    X(bad_data,ordered,changed_input,"input-bytes") \
    X(bad_rbx,ordered,changed_saved,"saved-GPR") \
    X(bad_rbp,ordered,changed_saved,"saved-GPR") \
    X(bad_r12,ordered,changed_saved,"saved-GPR") \
    X(bad_r13,ordered,changed_saved,"saved-GPR") \
    X(bad_r14,ordered,changed_saved,"saved-GPR") \
    X(bad_r15,ordered,changed_saved,"saved-GPR") \
    X(bad_rdi,ordered,changed_arguments,"RDI/RSI") \
    X(bad_rsi,ordered,changed_arguments,"RDI/RSI") \
    X(bad_r8,ordered,changed_extra,"R8..R11") \
    X(bad_r9,ordered,changed_extra,"R8..R11") \
    X(bad_r10,ordered,changed_extra,"R8..R11") \
    X(bad_r11,ordered,changed_extra,"R8..R11") \
    X(bad_rsp,ordered,changed_stack,"RSP") \
    X(bad_df,ordered,changed_nonarithmetic,"nonarithmetic-RFLAGS") \
    X(bad_id,ordered,changed_nonarithmetic,"nonarithmetic-RFLAGS")
#define DECLARE(name,witness,reason,label) extern const unsigned char edsl_array_sum64_##name[];
MUTANTS(DECLARE)
#define ENTRY(name,witness,reason,label) \
    {{#name,edsl_array_sum64_##name,NULL,NULL,0},witness,reason,label},
static const struct mutant mutants[] = { MUTANTS(ENTRY) };

struct input_case {
    const char *name;
    uint64_t base;
    size_t count, offset;
    unsigned char *mapping, *page, *snapshot;
};
struct statistics { uint64_t calls, cases; };
static size_t page_size;
static uint64_t probe_calls;

/* Match BOTH the complete embedded slot and its fixed profile before ANY
 * native call or stdout. Supplied paths are read as data, never executed/mapped. */
static int same_extraction(const struct program *program, const char *path)
{
    const size_t size = (size_t)((uintptr_t)program->end - (uintptr_t)program->code);
    unsigned char bytes[64];
    if (size != program->profile_size || size >= sizeof bytes ||
        memcmp(program->code, program->profile, size) != 0) return 0;
    FILE *file = fopen(path, "rb");
    if (!file) return 0;
    const size_t amount = fread(bytes, 1, size + 1, file);
    const int failed = ferror(file);
    const int closed = fclose(file);
    return !failed && closed == 0 && amount == size && memcmp(bytes, program->code, size) == 0;
}

static int dispose_case(struct input_case *input)
{
    free(input->snapshot);
    if (input->mapping && munmap(input->mapping, 3 * page_size) != 0) {
        perror("munmap owned array");
        return 0;
    }
    return 1;
}
/* All accessible bytes, including padding, have an immutable oracle snapshot.
 * Aligned read-only arrays end exactly at the trailing PROT_NONE page. An
 * unaligned array ends one byte before it. Writable cases are centrally padded. */
static int make_case(struct input_case *input, const char *name, const uint64_t *values,
    size_t count, int unaligned, int writable)
{
    *input = (struct input_case){.name = name, .count = count};
    if (count > 511) return 0;
    if (count == 0) return 1;
    if (count > (page_size - 128) / sizeof(uint64_t) && writable) return 0;
    if (count > (page_size - (unaligned != 0)) / sizeof(uint64_t)) return 0;
    void *mapping = mmap(NULL, 3 * page_size, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED) { perror("mmap owned array"); return 0; }
    input->mapping = mapping;
    input->page = input->mapping + page_size;
    if (mprotect(input->page, page_size, PROT_READ | PROT_WRITE) != 0) {
        perror("mprotect fill array");
        dispose_case(input);
        return 0;
    }
    input->offset = writable ? 64 : page_size - count * sizeof(uint64_t) - (unaligned != 0);
    memset(input->page, 0xa7, page_size);
    memcpy(input->page + input->offset, values, count * sizeof(uint64_t));
    input->base = (uint64_t)(uintptr_t)(input->page + input->offset);
    input->snapshot = malloc(page_size);
    if (!input->snapshot) { perror("malloc snapshot"); dispose_case(input); return 0; }
    memcpy(input->snapshot, input->page, page_size);
    if (!writable && mprotect(input->page, page_size, PROT_READ) != 0) {
        perror("mprotect read-only array");
        dispose_case(input);
        return 0;
    }
    return 1;
}

/* Independent base-256 postcondition on the pre-call snapshot. Each output
 * byte must equal its input-byte column plus the carry from the previous
 * column. The carry above byte seven is discarded: the specified sum is modulo
 * 2^64. This does not run a second scalar qword accumulator or reuse tested code.
 * At most 511 selected inputs bound every column below 2^18. */
static unsigned int mathematical_result(const struct input_case *input, uint64_t result)
{
    if (input->count == 0) return result == 0 ? 0 : nonzero_empty;
    uint64_t carry = 0;
    for (unsigned int lane = 0; lane < 8; ++lane) {
        uint64_t column = carry;
        for (size_t i = 0; i < input->count; ++i) {
            uint64_t value;
            memcpy(&value, input->snapshot + input->offset + i * sizeof value, sizeof value);
            column += (value >> (8 * lane)) & UINT64_C(0xff);
        }
        if (((result >> (8 * lane)) & UINT64_C(0xff)) != (column & UINT64_C(0xff)))
            return bad_result;
        carry = column >> 8;
    }
    return 0;
}
static uint64_t flags_for(unsigned int profile)
{
    static const unsigned int positions[] = {0,2,4,6,7,11,21};
    uint64_t flags = 0;
    for (size_t i = 0; i < sizeof positions / sizeof positions[0]; ++i)
        if ((profile >> i) & 1) flags |= UINT64_C(1) << positions[i];
    return flags;
}
/* Deterministic stimulus generation only. It never defines an expected result. */
static uint64_t next_operand(uint64_t *state)
{
    uint64_t value = (*state += UINT64_C(0x9e3779b97f4a7c15));
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}
static unsigned int observe(const struct program *program, const struct input_case *input,
    unsigned int profile)
{
    uint64_t state = UINT64_C(0x415252415936344d) ^ probe_calls;
    struct call_input *request = &edsl_array_sum64_input;
    request->base = input->base;
    request->count = input->count;
    request->flags = flags_for(profile);
    request->initial_rax = profile % 4 == 0 ? 0 :
        profile % 4 == 1 ? UINT64_MAX : next_operand(&state);
    for (size_t i = 0; i < saved_count; ++i) request->saved[i] = next_operand(&state) | 1;
    for (size_t i = 0; i < extra_count; ++i) request->extra[i] = next_operand(&state) | 1;
    ++probe_calls;
    edsl_array_sum64_probe(program->code);
    const struct observation *observed = &edsl_array_sum64_output;
    if ((observed->flags_before & (arithmetic_flags | direction_flag | id_flag)) != request->flags ||
        (observed->rsp_before & UINT64_C(15)) != 0) return bad_setup;
    unsigned int failures = mathematical_result(input, observed->result);
    if (input->count && memcmp(input->page, input->snapshot, page_size) != 0)
        failures |= changed_input;
    if (memcmp(request->saved, observed->saved, sizeof observed->saved) != 0)
        failures |= changed_saved;
    if (observed->arguments[0] != input->base || observed->arguments[1] != input->count)
        failures |= changed_arguments;
    if (memcmp(request->extra, observed->extra, sizeof observed->extra) != 0)
        failures |= changed_extra;
    if (observed->rsp_after != observed->rsp_before) failures |= changed_stack;
    if (((observed->flags_before ^ observed->flags_after) & ~arithmetic_flags) != 0)
        failures |= changed_nonarithmetic;
    return failures;
}
static void describe(FILE *file, const struct program *program, const struct input_case *input,
    unsigned int profile, unsigned int failures)
{
    const struct observation *observed = &edsl_array_sum64_output;
    fprintf(file, "%s case=%s count=%zu base=%016" PRIx64 " profile=%u initial-rax=%016" PRIx64
        " result=%016" PRIx64 " failures=%u rsp=%016" PRIx64 "/%016" PRIx64
        " flags=%016" PRIx64 "/%016" PRIx64 " input=[",
        program->name, input->name, input->count, input->base, profile,
        edsl_array_sum64_input.initial_rax, observed->result, failures,
        observed->rsp_before, observed->rsp_after, observed->flags_before, observed->flags_after);
    for (size_t i = 0; i < input->count && i < 16; ++i) {
        uint64_t value;
        memcpy(&value, input->snapshot + input->offset + i * sizeof value, sizeof value);
        fprintf(file, "%s%016" PRIx64, i ? "," : "", value);
    }
    fprintf(file, "%s]\n", input->count > 16 ? ",..." : "");
    static const char *const saved_names[] = {"RBX","RBP","R12","R13","R14","R15"};
    for (size_t i = 0; i < saved_count; ++i)
        if (observed->saved[i] != edsl_array_sum64_input.saved[i])
            fprintf(file, "  %s before=%016" PRIx64 " after=%016" PRIx64 "\n",
                saved_names[i], edsl_array_sum64_input.saved[i], observed->saved[i]);
    const uint64_t arguments[] = {input->base,input->count};
    for (size_t i = 0; i < 2; ++i)
        if (observed->arguments[i] != arguments[i])
            fprintf(file, "  %s before=%016" PRIx64 " after=%016" PRIx64 "\n",
                i ? "RSI" : "RDI", arguments[i], observed->arguments[i]);
    for (size_t i = 0; i < extra_count; ++i)
        if (observed->extra[i] != edsl_array_sum64_input.extra[i])
            fprintf(file, "  R%zu before=%016" PRIx64 " after=%016" PRIx64 "\n",
                i+8, edsl_array_sum64_input.extra[i], observed->extra[i]);
    if (failures & changed_input)
        for (size_t i = 0; i < page_size; ++i)
            if (input->page[i] != input->snapshot[i]) {
                fprintf(file, "  owned-page-byte[%zu] before=%02x after=%02x\n",
                    i, (unsigned int)input->snapshot[i], (unsigned int)input->page[i]);
                break;
            }
}
static int check_case(const struct program *program, const struct input_case *input,
    unsigned int profiles, unsigned int first_profile, struct statistics *statistics)
{
    ++statistics->cases;
    for (unsigned int i = 0; i < profiles; ++i) {
        const unsigned int profile = (first_profile + i) % flag_profiles;
        const unsigned int failures = observe(program, input, profile);
        ++statistics->calls;
        if (failures) { describe(stderr, program, input, profile, failures); return 0; }
    }
    return 1;
}
static int check_values(const struct program *program, const char *name, const uint64_t *values,
    size_t count, int unaligned, int writable, unsigned int profiles, unsigned int first_profile,
    struct statistics *statistics)
{
    struct input_case input;
    if (!make_case(&input, name, values, count, unaligned, writable)) return 0;
    const int passed = check_case(program, &input, profiles, first_profile, statistics);
    const int disposed = dispose_case(&input);
    return passed && disposed;
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
static int run_positive(const struct program *program, struct statistics *statistics)
{
    struct input_case unused = {.name = "empty-null"};
    if (!check_case(program, &unused, flag_profiles, 0, statistics)) return 0;
    void *guard = mmap(NULL, page_size, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (guard == MAP_FAILED) { perror("mmap unused guard base"); return 0; }
    unused.name = "empty-PROT_NONE";
    unused.base = (uint64_t)(uintptr_t)guard;
    const int passed = check_case(program, &unused, flag_profiles, 0, statistics);
    if (munmap(guard, page_size) != 0) { perror("munmap unused guard base"); return 0; }
    if (!passed) return 0;
    unused.name = "empty-noncanonical-48-and-57-bit";
    unused.base = UINT64_C(0x0200000000000000);
    if (!check_case(program, &unused, flag_profiles, 0, statistics)) return 0;

    const size_t edge_count = sizeof edges / sizeof edges[0];
    for (size_t i = 0; i < edge_count; ++i) {
        if (!check_values(program, "edge-singleton", &edges[i], 1, 0, 0,
            flag_profiles, 0, statistics)) return 0;
        for (size_t j = 0; j < edge_count; ++j) {
            const uint64_t pair[] = {edges[i],edges[j]};
            if (!check_values(program, "edge-pair", pair, 2, 0, 0,
                flag_profiles, 0, statistics)) return 0;
        }
    }
    for (unsigned int bit = 0; bit < 64; ++bit) {
        const uint64_t power = UINT64_C(1) << bit;
        const uint64_t pairs[][2] = {
            {power-1,power},{power,power-1},{power,power},
            {UINT64_MAX-power,UINT64_MAX},{UINT64_MAX,UINT64_MAX-power},
            {UINT64_MAX-power,UINT64_MAX-power}
        };
        for (size_t i = 0; i < sizeof pairs / sizeof pairs[0]; ++i)
            if (!check_values(program, "bit-boundary-pair", pairs[i], 2, 0, 0,
                flag_profiles, 0, statistics)) return 0;
    }
    static const size_t lengths[] = {3,4,7,8,15,16,31,32,63,64,127,128,255,256,511};
    uint64_t state = UINT64_C(0x61727261796d6178), values[511];
    for (size_t n = 0; n < sizeof lengths / sizeof lengths[0]; ++n) {
        const size_t count = lengths[n], positions[] = {0,count/2,count-1};
        for (size_t position = 0; position < sizeof positions / sizeof positions[0]; ++position) {
            for (size_t i = 0; i < count; ++i) values[i] = next_operand(&state);
            values[positions[position]] = UINT64_MAX;
            if (!check_values(program, "carry-first-middle-last", values, count, 0, 0,
                flag_profiles, 0, statistics)) return 0;
        }
        if (!check_values(program, "unaligned-base", values, count, 1, 0,
            flag_profiles, 0, statistics)) return 0;
    }
    for (size_t i = 0; i < 64; ++i) values[i] = i % 3 ? UINT64_MAX : UINT64_C(0x100000000);
    if (!check_values(program, "wrap-heavy-array", values, 64, 0, 0,
        flag_profiles, 0, statistics)) return 0;
    if (!check_values(program, "writable-padded-frame", values, 64, 0, 1,
        flag_profiles, 0, statistics)) return 0;
    for (unsigned int sample = 0; sample < random_arrays; ++sample) {
        const size_t count = 1 + next_operand(&state) % (sizeof values / sizeof values[0]);
        for (size_t i = 0; i < count; ++i) {
            values[i] = next_operand(&state);
            if (sample % 16 == 0 && i % 3 == 1) values[i] = values[0];
        }
        if (!check_values(program, "random-array", values, count, sample % 2, 0,
            1, sample % flag_profiles, statistics)) return 0;
    }
    return 1;
}
static int rejects_mutant(const struct mutant *mutant)
{
    const uint64_t witnesses[][2] = {
        [ordered] = {1,3}, [high_sign] = {1,UINT64_C(0x80000000)},
        [wide] = {UINT64_C(0x100000000),UINT64_C(0x100000001)},
        [carry] = {UINT64_MAX,2}, [empty] = {0,0}
    };
    struct input_case input;
    if (!make_case(&input, "owned-writable-padded-counterexample", witnesses[mutant->witness],
        mutant->witness == empty ? 0 : 2, 0, 1)) return 0;
    const unsigned int failures = observe(&mutant->program, &input, 0);
    const int rejected = failures == mutant->reason;
    if (rejected) {
        printf("REJECTED owned mutant expected=%s: ", mutant->reason_name);
        describe(stdout, &mutant->program, &input, 0, failures);
    } else {
        fprintf(stderr, "Owned mutant did not give required counterexample (expected=%u): ", mutant->reason);
        describe(stderr, &mutant->program, &input, 0, failures);
    }
    const int disposed = dispose_case(&input);
    return rejected && disposed;
}
int main(int argc, char **argv)
{
    if (argc != 3) { fputs("usage: native-check GCC_TEXT CLANG_TEXT\n", stderr); return 2; }
    for (size_t i = 0; i < sizeof positives / sizeof positives[0]; ++i) {
        if (!same_extraction(&positives[i], argv[i+1])) {
            fprintf(stderr, "Final ELF section extraction differs from executed bytes: %s\n", positives[i].name);
            return 2;
        }
    }
    const long host_page_size = sysconf(_SC_PAGESIZE);
    if (host_page_size < 4096 || (uintmax_t)host_page_size > SIZE_MAX / 3 || host_page_size % 8) {
        fputs("Unsupported host page size for guarded arrays\n", stderr);
        return 1;
    }
    page_size = (size_t)host_page_size;
    uint64_t total = 0;
    for (size_t i = 0; i < sizeof positives / sizeof positives[0]; ++i) {
        struct statistics statistics = {0};
        if (!run_positive(&positives[i], &statistics)) return 1;
        total += statistics.calls;
        printf("PASS %s: %" PRIu64 " whole calls, %" PRIu64 " arrays, full64 byte-column-modular-sum/empty, "
            "unchanged bytes, six saved GPRs, RDI/RSI/R8..R11, RSP, nonarithmetic RFLAGS\n",
            positives[i].name, statistics.calls, statistics.cases);
    }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i)
        if (!rejects_mutant(&mutants[i])) return 1;
    printf("PASS finite native evidence: %" PRIu64 " positive calls, %zu owned mutants rejected, "
        "%" PRIu64 " actual probe calls; universal Lean NOTRUN\n",
        total, sizeof mutants / sizeof mutants[0], probe_calls);
    return 0;
}
