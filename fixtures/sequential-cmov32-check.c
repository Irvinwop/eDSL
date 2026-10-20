/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <cpuid.h>
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { register_count = 16, condition_vectors = 32, payload_profiles = 6 };
struct snapshot { uint64_t registers[register_count]; uint64_t flags; };
_Static_assert(offsetof(struct snapshot, flags) == 128 && sizeof(struct snapshot) == 136,
    "Assembly snapshot ABI changed");
struct snapshot edsl_cmov32_input, edsl_cmov32_output;
uint64_t edsl_cmov32_effective_flags;
extern void edsl_cmov32_probe(const unsigned char *);
extern const unsigned char edsl_cmov32_section_start[], edsl_cmov32_section_end[];

enum condition {
    overflow, no_overflow, below, above_equal, equal, not_equal, below_equal, above,
    negative, nonnegative, even_parity, odd_parity, less, greater_equal, less_equal, greater
};
struct contract {
    const char *name;
    const unsigned char *code, *end;
    enum condition condition;
    unsigned int destination, source;
};
/* Requested operations are independent of the .byte instruction declarations.
 * There is no instruction, REX or ModRM decoder in this observer. Register
 * numbers name positions in the full-register assembly snapshot ABI. */
#define CONDITIONS(X) \
    X(c_o,overflow,0,1) \
    X(c_no,no_overflow,0,1) \
    X(c_b,below,0,1) \
    X(c_ae,above_equal,0,1) \
    X(c_e,equal,0,1) \
    X(c_ne,not_equal,0,1) \
    X(c_be,below_equal,0,1) \
    X(c_a,above,0,1) \
    X(c_s,negative,0,1) \
    X(c_ns,nonnegative,0,1) \
    X(c_p,even_parity,0,1) \
    X(c_np,odd_parity,0,1) \
    X(c_l,less,0,1) \
    X(c_ge,greater_equal,0,1) \
    X(c_le,less_equal,0,1) \
    X(c_g,greater,0,1)
#define BANKS(X) \
    X(b0,overflow,0,1) \
    X(b1,no_overflow,1,10) \
    X(b2,below,2,3) \
    X(b3,above_equal,3,12) \
    X(b4,equal,4,5) \
    X(b5,not_equal,5,14) \
    X(b6,below_equal,6,7) \
    X(b7,above,7,8) \
    X(b8,negative,8,9) \
    X(b9,nonnegative,9,2) \
    X(b10,even_parity,10,11) \
    X(b11,odd_parity,11,4) \
    X(b12,less,12,13) \
    X(b13,greater_equal,13,6) \
    X(b14,less_equal,14,15) \
    X(b15,greater,15,0)
#define ALIASES(X) \
    X(s0,overflow,0,0) \
    X(s1,no_overflow,1,1) \
    X(s2,below,2,2) \
    X(s3,above_equal,3,3) \
    X(s4,equal,4,4) \
    X(s5,not_equal,5,5) \
    X(s6,below_equal,6,6) \
    X(s7,above,7,7) \
    X(s8,negative,8,8) \
    X(s9,nonnegative,9,9) \
    X(s10,even_parity,10,10) \
    X(s11,odd_parity,11,11) \
    X(s12,less,12,12) \
    X(s13,greater_equal,13,13) \
    X(s14,less_equal,14,14) \
    X(s15,greater,15,15)
#define IGNORED_X(X) \
    X(x0,equal,1,3) \
    X(x1,equal,1,11) \
    X(x2,equal,9,3) \
    X(x3,equal,9,11)
#define MUTANTS(X) \
    X(mutant_condition,equal,0,9) \
    X(mutant_direction,equal,0,9) \
    X(mutant_width64,equal,0,9) \
    X(mutant_width16,equal,0,9) \
    X(mutant_flags,equal,0,9) \
    X(mutant_false_no_write,equal,4,9) \
    X(mutant_source,equal,0,9) \
    X(mutant_false_alias,equal,8,8)
#define DECLARE(name,c,d,s) \
    extern const unsigned char edsl_cmov32_##name[], edsl_cmov32_##name##_end[];
CONDITIONS(DECLARE) BANKS(DECLARE) ALIASES(DECLARE) IGNORED_X(DECLARE) MUTANTS(DECLARE)
#define ENTRY(name,c,d,s) {#name,edsl_cmov32_##name,edsl_cmov32_##name##_end,c,d,s},
static const struct contract contracts[] = {
    CONDITIONS(ENTRY) BANKS(ENTRY) ALIASES(ENTRY) IGNORED_X(ENTRY)
};
static const struct contract mutants[] = { MUTANTS(ENTRY) };

/* SDM condition contracts over effective flags, not opcode-derived conditions.
 * AF and DF occur in neither signed nor unsigned comparisons. */
static int requested(enum condition condition, uint64_t flags)
{
    const int carry = (flags & UINT64_C(1)) != 0;
    const int parity = (flags & UINT64_C(4)) != 0;
    const int zero = (flags & UINT64_C(0x40)) != 0;
    const int sign = (flags & UINT64_C(0x80)) != 0;
    const int over = (flags & UINT64_C(0x800)) != 0;
    switch (condition) {
    case overflow: return over;
    case no_overflow: return over == 0;
    case below: return carry;
    case above_equal: return carry == 0;
    case equal: return zero;
    case not_equal: return zero == 0;
    case below_equal: return carry + zero != 0;
    case above: return carry + zero == 0;
    case negative: return sign;
    case nonnegative: return sign == 0;
    case even_parity: return parity;
    case odd_parity: return parity == 0;
    case less: return sign != over;
    case greater_equal: return sign == over;
    case less_equal: return zero || sign != over;
    case greater: return !zero && sign == over;
    }
    abort();
}

static uint64_t flags_for(unsigned int vector, unsigned int outside_profile)
{
    static const unsigned int positions[] = {0, 2, 6, 7, 11};
    uint64_t flags = UINT64_C(0x202) | (outside_profile ? UINT64_C(0x410) : 0);
    for (unsigned int i = 0; i < 5; ++i)
        if ((vector >> i) & 1) flags |= UINT64_C(1) << positions[i];
    return flags;
}

static void install_payload(const struct contract *contract, unsigned int vector,
    unsigned int outside_profile, unsigned int payload)
{
    /* Independent width boundaries: zero, all ones, the sign boundary, one,
     * and mixed bytes. Distinct high halves must disappear only at destination. */
    static const uint32_t lows[payload_profiles][2] = {
        {UINT32_C(0),UINT32_C(0xffffffff)},
        {UINT32_C(0xffffffff),UINT32_C(0)},
        {UINT32_C(0x80000000),UINT32_C(0x7fffffff)},
        {UINT32_C(0x7fffffff),UINT32_C(0x80000000)},
        {UINT32_C(1),UINT32_C(0xfffffffe)},
        {UINT32_C(0x89abcdef),UINT32_C(0x12345678)}
    };
    for (unsigned int i = 0; i < register_count; ++i)
        edsl_cmov32_input.registers[i] = UINT64_C(0x8123456700000000) +
            (uint64_t)(i + 1) * UINT64_C(0x0101010100101011) +
            (uint64_t)vector * UINT64_C(0x0001000100000101);
    const unsigned int d = contract->destination, s = contract->source;
    edsl_cmov32_input.registers[d] = (edsl_cmov32_input.registers[d] &
        UINT64_C(0xffffffff00000000)) | lows[payload][0];
    if (d != s)
        edsl_cmov32_input.registers[s] = (edsl_cmov32_input.registers[s] &
            UINT64_C(0xffffffff00000000)) | lows[payload][1];
    edsl_cmov32_input.flags = flags_for(vector, outside_profile);
}

static void print_registers(const uint64_t *values)
{
    for (unsigned int i = 0; i < register_count; ++i)
        printf("%s%016" PRIx64, i ? "," : "", values[i]);
}

static int run_case(const struct contract *contract, unsigned int vector,
    unsigned int outside_profile, unsigned int payload, int emit)
{
    install_payload(contract, vector, outside_profile, payload);
    edsl_cmov32_probe(contract->code);
    if ((edsl_cmov32_effective_flags & UINT64_C(0xcd5)) !=
        (edsl_cmov32_input.flags & UINT64_C(0xcd5))) return -1;
    struct snapshot expected = edsl_cmov32_input;
    expected.flags = edsl_cmov32_effective_flags;
    const int take = requested(contract->condition, edsl_cmov32_effective_flags);
    /* A false r32 CMOV retains the original low destination, then zero extends.
     * In particular, a self alias still clears the high half for either result. */
    const uint64_t selected = edsl_cmov32_input.registers[
        take ? contract->source : contract->destination];
    expected.registers[contract->destination] = (uint32_t)selected;
    int matches = memcmp(expected.registers, edsl_cmov32_output.registers,
        sizeof expected.registers) == 0 && expected.flags == edsl_cmov32_output.flags;
    if (!matches || !emit) return matches;

    printf("%s\t%u\t%u\t%u\t%d\t%" PRIuPTR "\t%" PRIuPTR "\t",
        contract->name, vector, outside_profile, payload, take,
        (uintptr_t)contract->code, (uintptr_t)contract->end);
    const size_t length = (size_t)((uintptr_t)contract->end - (uintptr_t)contract->code);
    for (size_t i = 0; i < length; ++i) printf("%02x", (unsigned int)contract->code[i]);
    printf("\t%016" PRIx64 "\t", edsl_cmov32_effective_flags);
    print_registers(edsl_cmov32_input.registers);
    printf("\t%016" PRIx64 "\t", edsl_cmov32_output.flags);
    print_registers(edsl_cmov32_output.registers);
    putchar('\n');
    return 1;
}

int main(int argc, char **argv)
{
    if (argc != 2) return 2;
    FILE *file = fopen(argv[1], "rb");
    if (!file) return 2;
    const size_t size = (size_t)((uintptr_t)edsl_cmov32_section_end -
        (uintptr_t)edsl_cmov32_section_start);
    unsigned char *bytes = malloc(size + 1);
    if (!bytes) { fclose(file); return 2; }
    const size_t amount = fread(bytes, 1, size + 1, file);
    const int failed = ferror(file);
    fclose(file);
    if (failed || amount != size || memcmp(bytes, edsl_cmov32_section_start, size) != 0) {
        fputs("Final ELF section extraction differs from executed bytes\n", stderr);
        free(bytes);
        return 2;
    }
    free(bytes);
    unsigned int a, b, c, d;
    if (!__get_cpuid(1, &a, &b, &c, &d) || !(d & bit_CMOV)) {
        fputs("Native CPU does not advertise CMOV\n", stderr);
        return 2;
    }
    puts("window\tflags_vector\taf_df_profile\tpayload\tcondition_true\tpc\tcontinuation\tbytes\tinput_flags\tinput_registers\toutput_flags\toutput_registers");
    size_t observations = 0, true_cases = 0, false_cases = 0;
    for (size_t i = 0; i < sizeof contracts / sizeof contracts[0]; ++i)
    for (unsigned int vector = 0; vector < condition_vectors; ++vector)
    for (unsigned int outside = 0; outside < 2; ++outside)
    for (unsigned int payload = 0; payload < payload_profiles; ++payload) {
        if (run_case(&contracts[i], vector, outside, payload, 1) != 1) {
            fprintf(stderr, "Independent native contract or flags setup failed: %s/%u/%u/%u\n",
                contracts[i].name, vector, outside, payload);
            return 1;
        }
        if (requested(contracts[i].condition, edsl_cmov32_effective_flags)) ++true_cases;
        else ++false_cases;
        ++observations;
    }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        int rejected = 0;
        for (unsigned int vector = 0; vector < condition_vectors && !rejected; ++vector)
        for (unsigned int payload = 0; payload < payload_profiles && !rejected; ++payload) {
            int matches = run_case(&mutants[i], vector, 0, payload, 0);
            if (matches < 0) {
                fputs("Effective requested flags were not installed\n", stderr);
                return 1;
            }
            if (!matches) {
                fprintf(stderr, "REJECTED owned mutant: %s (vector %u, payload %u)\n",
                    mutants[i].name, vector, payload);
                rejected = 1;
            }
        }
        if (!rejected) {
            fprintf(stderr, "Independent observer failed to reject owned mutant: %s\n", mutants[i].name);
            return 1;
        }
    }
    fprintf(stderr, "Checked %zu native CMOV32 observations across %zu windows; "
        "true=%zu false=%zu; all32 condition flags, both AF/DF profiles, six payloads; "
        "rejected %zu owned semantic mutants; final ELF bytes matched\n", observations,
        sizeof contracts / sizeof contracts[0], true_cases, false_cases,
        sizeof mutants / sizeof mutants[0]);
    return ferror(stdout) ? 1 : 0;
}
