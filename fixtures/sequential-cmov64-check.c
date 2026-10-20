/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { register_count = 16, condition_vectors = 32 };
struct snapshot { uint64_t registers[register_count]; uint64_t flags; };
_Static_assert(offsetof(struct snapshot, flags) == 128 && sizeof(struct snapshot) == 136,
    "Assembly snapshot ABI changed");
struct snapshot edsl_cmov_input, edsl_cmov_output;
uint64_t edsl_cmov_effective_flags;
extern void edsl_cmov_probe(const unsigned char *);
extern const unsigned char edsl_cmov_section_start[], edsl_cmov_section_end[];

enum condition {
    overflow, no_overflow, below, above_equal, equal, not_equal, below_equal, above,
    negative, nonnegative, even_parity, odd_parity, less, greater_equal, less_equal, greater
};
struct contract {
    const char *name;
    const unsigned char *code, *end;
    enum condition condition;
    unsigned int destination, source, outside_profile;
};
/* Independently requested operations. This observer contains no instruction,
 * REX or ModRM decoder, and does not derive a condition from the opcode. The
 * register numbering follows the stated snapshot ABI. */
#define CONDITIONS(X) \
    X(c_o,overflow,0,9,0) \
    X(c_no,no_overflow,0,9,0) \
    X(c_b,below,0,9,0) \
    X(c_ae,above_equal,0,9,0) \
    X(c_e,equal,0,9,0) \
    X(c_ne,not_equal,0,9,0) \
    X(c_be,below_equal,0,9,0) \
    X(c_a,above,0,9,0) \
    X(c_s,negative,0,9,0) \
    X(c_ns,nonnegative,0,9,0) \
    X(c_p,even_parity,0,9,0) \
    X(c_np,odd_parity,0,9,0) \
    X(c_l,less,0,9,0) \
    X(c_ge,greater_equal,0,9,0) \
    X(c_le,less_equal,0,9,0) \
    X(c_g,greater,0,9,0)
/* Each condition also runs with AF and DF set, a different register pair and
 * all 32 condition-flag settings. Every GPR is both a source and destination. */
#define BANKS(X) \
    X(b0,overflow,0,1,1) \
    X(b1,no_overflow,1,10,1) \
    X(b2,below,2,3,1) \
    X(b3,above_equal,3,12,1) \
    X(b4,equal,4,5,1) \
    X(b5,not_equal,5,14,1) \
    X(b6,below_equal,6,7,1) \
    X(b7,above,7,8,1) \
    X(b8,negative,8,9,1) \
    X(b9,nonnegative,9,2,1) \
    X(b10,even_parity,10,11,1) \
    X(b11,odd_parity,11,4,1) \
    X(b12,less,12,13,1) \
    X(b13,greater_equal,13,6,1) \
    X(b14,less_equal,14,15,1) \
    X(b15,greater,15,0,1)
#define ALIASES(X) \
    X(s0,overflow,0,0,0) \
    X(s1,no_overflow,1,1,0) \
    X(s2,below,2,2,0) \
    X(s3,above_equal,3,3,0) \
    X(s4,equal,4,4,0) \
    X(s5,not_equal,5,5,0) \
    X(s6,below_equal,6,6,0) \
    X(s7,above,7,7,0) \
    X(s8,negative,8,8,0) \
    X(s9,nonnegative,9,9,0) \
    X(s10,even_parity,10,10,0) \
    X(s11,odd_parity,11,11,0) \
    X(s12,less,12,12,0) \
    X(s13,greater_equal,13,13,0) \
    X(s14,less_equal,14,14,0) \
    X(s15,greater,15,15,0)
#define IGNORED_X(X) \
    X(x0,equal,1,3,1) \
    X(x1,equal,1,11,1) \
    X(x2,equal,9,3,1) \
    X(x3,equal,9,11,1)
#define MUTANTS(X) \
    X(mutant_condition,equal,0,9,0) \
    X(mutant_direction,equal,0,9,0) \
    X(mutant_width,equal,0,9,0) \
    X(mutant_flags,equal,0,9,0) \
    X(mutant_false_rsp,equal,4,9,0) \
    X(mutant_source,equal,0,9,0)
#define DECLARE(name,c,d,s,p) \
    extern const unsigned char edsl_cmov_##name[], edsl_cmov_##name##_end[];
CONDITIONS(DECLARE) BANKS(DECLARE) ALIASES(DECLARE) IGNORED_X(DECLARE) MUTANTS(DECLARE)
#define ENTRY(name,c,d,s,p) {#name,edsl_cmov_##name,edsl_cmov_##name##_end,c,d,s,p},
static const struct contract contracts[] = {
    CONDITIONS(ENTRY) BANKS(ENTRY) ALIASES(ENTRY) IGNORED_X(ENTRY)
};
static const struct contract mutants[] = { MUTANTS(ENTRY) };

/* Architectural requested predicates over the actual effective status flags.
 * AF and DF deliberately occur in neither signed nor unsigned comparisons. */
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
static void print_words(const uint64_t *values, size_t count)
{
    putchar('[');
    for (size_t i = 0; i < count; ++i) printf("%s%" PRIu64, i ? "," : "", values[i]);
    putchar(']');
}
static void print_bytes(const unsigned char *values, size_t count)
{
    putchar('[');
    for (size_t i = 0; i < count; ++i) printf("%s%u", i ? "," : "", (unsigned int)values[i]);
    putchar(']');
}
static int run_case(const struct contract *contract, unsigned int vector, int emit)
{
    for (unsigned int i = 0; i < register_count; ++i)
        edsl_cmov_input.registers[i] = UINT64_C(0x8123456700000000) +
            (uint64_t)(i + 1) * UINT64_C(0x0100010000101011) +
            (uint64_t)vector * UINT64_C(0x0001000100000101);
    edsl_cmov_input.flags = flags_for(vector, contract->outside_profile);
    edsl_cmov_probe(contract->code);
    /* Refuse a platform that did not actually install the requested five
     * condition bits or AF/DF. Coverage counts refer to captured flags. */
    if ((edsl_cmov_effective_flags & UINT64_C(0xcd5)) !=
        (edsl_cmov_input.flags & UINT64_C(0xcd5))) return -1;
    struct snapshot expected = edsl_cmov_input;
    expected.flags = edsl_cmov_effective_flags;
    if (requested(contract->condition, edsl_cmov_effective_flags))
        expected.registers[contract->destination] = edsl_cmov_input.registers[contract->source];
    int matches = memcmp(expected.registers, edsl_cmov_output.registers, sizeof expected.registers) == 0 &&
        expected.flags == edsl_cmov_output.flags;
    if (!matches || !emit) return matches;

    size_t length = (size_t)((uintptr_t)contract->end - (uintptr_t)contract->code);
    printf("-- Native requested %s, condition-flag vector %u, AF/DF profile %u.\n",
        contract->name, vector, contract->outside_profile);
    printf("theorem observed_%s_%u (af : Bool) : observe af (entry ", contract->name, vector);
    print_bytes(contract->code, length);
    printf(" %" PRIuPTR " ", (uintptr_t)contract->code);
    print_words(edsl_cmov_input.registers, register_count);
    printf(" %" PRIu64 ") = some (", edsl_cmov_effective_flags);
    print_words(edsl_cmov_output.registers, register_count);
    printf(",%" PRIu64 ",%" PRIuPTR ",[]) := by cases af <;> rfl\n",
        edsl_cmov_output.flags, (uintptr_t)contract->end);
    return 1;
}

int main(int argc, char **argv)
{
    if (argc != 2) return 2;
    FILE *file = fopen(argv[1], "rb");
    if (!file) return 2;
    size_t size = (size_t)((uintptr_t)edsl_cmov_section_end - (uintptr_t)edsl_cmov_section_start);
    unsigned char *bytes = malloc(size + 1);
    if (!bytes) return 2;
    size_t amount = fread(bytes, 1, size + 1, file);
    int failed = ferror(file);
    fclose(file);
    if (failed || amount != size || memcmp(bytes, edsl_cmov_section_start, size) != 0) {
        fputs("Final ELF section extraction differs from executed bytes\n", stderr);
        free(bytes);
        return 2;
    }
    free(bytes);
    puts("/- Finite native register CMOV64 observations. The independent C\n"
         "requested predicates checked all 16 GPRs and complete effective RFLAGS.\n"
         "RIP uses extracted continuation labels; [] is the independently requested\n"
         "operand-read footprint, not a hardware trace. Memory CMOV is excluded. -/\n"
         "import EDSL.X86.Sequential.Machine\nimport EDSL.Audit\n"
         "namespace EDSL.Tests.NativeSequentialCmov64\nopen EDSL.X86\n"
         "def allRegisters : List Register := [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,"
         ".r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]\n"
         "def entry (code : List Byte) (pc : Word) (registers : List Word) (flags : Word) : State where\n"
         "  registers r := registers.getD (allRegisters.idxOf r) 0\n"
         "  rip := pc\n  flags := flags\n"
         "  memory := {\n"
         "    read := fun a => if pc.toNat ≤ a.toNat ∧ a.toNat < pc.toNat + code.length\n"
         "      then code[a.toNat - pc.toNat]? else none\n"
         "    executable := fun a => decide (pc.toNat ≤ a.toNat ∧ a.toNat < pc.toNat + code.length)\n"
         "    writable := fun _ => false }\n"
         "def observe (af : Bool) (initial : State) :\n"
         "    Option (List Word × Word × Word × List Sequential.Read) := do\n"
         "  let observation ← (Sequential.step af initial).toOption\n"
         "  match observation.result with\n"
         "  | .next final => return (allRegisters.map final.registers,final.flags,final.rip,observation.reads)\n"
         "  | _ => none");
    size_t observations = 0;
    for (size_t i = 0; i < sizeof contracts / sizeof contracts[0]; ++i)
    for (unsigned int vector = 0; vector < condition_vectors; ++vector) {
        if (run_case(&contracts[i], vector, 1) != 1) {
            fprintf(stderr, "Independent native contract or flags setup failed: %s/%u\n", contracts[i].name, vector);
            return 1;
        }
        ++observations;
    }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        unsigned int vector;
        for (vector = 0; vector < condition_vectors; ++vector) {
            int matches = run_case(&mutants[i], vector, 0);
            if (matches < 0) {
                fputs("Effective requested flags were not installed\n", stderr);
                return 1;
            }
            if (!matches) break;
        }
        if (vector == condition_vectors) {
            fprintf(stderr, "Independent observer failed to reject owned mutant: %s\n", mutants[i].name);
            return 1;
        }
        fprintf(stderr, "REJECTED owned mutant: %s (vector %u)\n", mutants[i].name, vector);
    }
    puts("end EDSL.Tests.NativeSequentialCmov64\n#audit_edsl");
    fprintf(stderr, "Checked %zu native CMOV64 observations across %zu windows with all 32 condition-flag settings; "
        "rejected %zu owned semantic mutants; final ELF bytes matched\n", observations,
        sizeof contracts / sizeof contracts[0], sizeof mutants / sizeof mutants[0]);
    return 0;
}
