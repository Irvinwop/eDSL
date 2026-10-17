/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { register_count = 16, vector_count = 12 };
struct snapshot { uint64_t registers[register_count]; uint64_t flags; };
_Static_assert(offsetof(struct snapshot, flags) == 128 && sizeof(struct snapshot) == 136,
    "Assembly snapshot ABI changed");
struct snapshot edsl_logical_input, edsl_logical_output;
uint64_t edsl_logical_effective_flags;
extern void edsl_logical_probe(const unsigned char *);
extern const unsigned char edsl_logical_section_start[], edsl_logical_section_end[];

enum operation { intersection, union_bits, difference_bits };
struct contract {
    const char *name;
    const unsigned char *code, *end;
    enum operation operation;
    unsigned int destination, source;
};
/* Requested operations, independently of instruction encodings. The observer
 * has no opcode, REX or ModRM decoder. Register numbers follow the explicitly
 * stated snapshot ABI, rather than an inference from the executed bytes. */
#define PAIRS(X,P,K) \
    X(P##_mr0,K,0,1) X(P##_mr1,K,1,10) \
    X(P##_mr2,K,2,3) X(P##_mr3,K,3,12) \
    X(P##_mr4,K,4,5) X(P##_mr5,K,5,14) \
    X(P##_mr6,K,6,7) X(P##_mr7,K,7,8) \
    X(P##_mr8,K,8,9) X(P##_mr9,K,9,2) \
    X(P##_mr10,K,10,11) X(P##_mr11,K,11,4) \
    X(P##_mr12,K,12,13) X(P##_mr13,K,13,6) \
    X(P##_mr14,K,14,15) X(P##_mr15,K,15,0) \
    X(P##_rm0,K,0,15) X(P##_rm1,K,1,0) \
    X(P##_rm2,K,2,9) X(P##_rm3,K,3,2) \
    X(P##_rm4,K,4,11) X(P##_rm5,K,5,4) \
    X(P##_rm6,K,6,13) X(P##_rm7,K,7,6) \
    X(P##_rm8,K,8,7) X(P##_rm9,K,9,8) \
    X(P##_rm10,K,10,1) X(P##_rm11,K,11,10) \
    X(P##_rm12,K,12,3) X(P##_rm13,K,13,12) \
    X(P##_rm14,K,14,5) X(P##_rm15,K,15,14)
#define SELF(X,P,K,N) X(P##_selfmr##N,K,N,N) X(P##_selfrm##N,K,N,N)
#define SELVES(X,P,K) \
    SELF(X,P,K,0) SELF(X,P,K,1) SELF(X,P,K,2) SELF(X,P,K,3) \
    SELF(X,P,K,4) SELF(X,P,K,5) SELF(X,P,K,6) SELF(X,P,K,7) \
    SELF(X,P,K,8) SELF(X,P,K,9) SELF(X,P,K,10) SELF(X,P,K,11) \
    SELF(X,P,K,12) SELF(X,P,K,13) SELF(X,P,K,14) SELF(X,P,K,15)
#define EXTRAS(X,P,K) \
    X(P##_xmr0,K,0,3) X(P##_xmr1,K,8,3) \
    X(P##_xmr2,K,0,11) X(P##_xmr3,K,8,11) \
    X(P##_xrm0,K,3,0) X(P##_xrm1,K,3,8) \
    X(P##_xrm2,K,11,0) X(P##_xrm3,K,11,8)
#define OPERATION(X,P,K) PAIRS(X,P,K) SELVES(X,P,K) EXTRAS(X,P,K)
#define POSITIVES(X) \
    OPERATION(X,band,intersection) OPERATION(X,bor,union_bits) \
    OPERATION(X,bxor,difference_bits)
#define MUTANT_OPERATION(X,P,K) \
    X(mutant_##P##_operation,K,0,1) X(mutant_##P##_direction,K,0,1) \
    X(mutant_##P##_source,K,0,1) X(mutant_##P##_width,K,0,1) \
    X(mutant_##P##_flags,K,0,1)
#define MUTANTS(X) \
    MUTANT_OPERATION(X,band,intersection) MUTANT_OPERATION(X,bor,union_bits) \
    MUTANT_OPERATION(X,bxor,difference_bits)
#define DECLARE(name,k,d,s) \
    extern const unsigned char edsl_logical_##name[], edsl_logical_##name##_end[];
POSITIVES(DECLARE) MUTANTS(DECLARE)
#define ENTRY(name,k,d,s) {#name,edsl_logical_##name,edsl_logical_##name##_end,k,d,s},
static const struct contract contracts[] = { POSITIVES(ENTRY) };
static const struct contract mutants[] = { MUTANTS(ENTRY) };

/* A finite set of bit positions defines the requested mathematical operation.
 * This oracle neither decodes bytes nor dispatches through the model. */
static uint64_t requested_result(enum operation operation, uint64_t left, uint64_t right)
{
    uint64_t result = 0;
    for (unsigned int bit = 0; bit < 64; ++bit) {
        int in_left = (left >> bit) % 2 != 0;
        int in_right = (right >> bit) % 2 != 0;
        int present;
        switch (operation) {
        case intersection: present = in_left && in_right; break;
        case union_bits: present = in_left || in_right; break;
        case difference_bits: present = in_left != in_right; break;
        default: abort();
        }
        if (present) result += UINT64_C(1) << bit;
    }
    return result;
}

/* Intel SDM revision 093: CF/OF clear, ZF/SF/PF describe the result, AF is
 * undefined. All remaining effective flags are preserved. Only bit4 is masked
 * when comparing to hardware; the captured physical AF later witnesses replay. */
static uint64_t requested_flags(uint64_t old, uint64_t result)
{
    uint64_t flags = old & ~UINT64_C(0x8d5);
    unsigned int population = 0;
    for (unsigned int bit = 0; bit < 8; ++bit)
        population += (unsigned int)((result >> bit) % 2);
    if (population % 2 == 0) flags |= UINT64_C(4);
    if (result == 0) flags |= UINT64_C(0x40);
    if (result > INT64_MAX) flags |= UINT64_C(0x80);
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
    static const uint64_t left[vector_count] = {
        0, UINT64_MAX, INT64_MAX, UINT64_C(0x8000000000000000), 0xf, 0x10,
        0x80, UINT64_C(0x100000000), UINT64_C(0xfeedface89abcdef), 1,
        UINT64_C(0xaaaaaaaaaaaaaaaa), UINT64_C(0xffffffffffffffff)
    };
    static const uint64_t right[vector_count] = {
        0, 0, UINT64_C(0x8000000000000000), UINT64_C(0x8000000000000000), 1, 0xf,
        0xff, UINT64_C(0x1ffffffff), UINT64_C(0x1122334455667788), 2,
        UINT64_C(0x5555555555555555), UINT64_C(0x8000000000000001)
    };
    for (unsigned int i = 0; i < register_count; ++i) {
        if (vector % 4 == 0)
            edsl_logical_input.registers[i] = UINT64_C(0x100000001) + i * UINT64_C(0x100000011);
        else if (vector % 4 == 1)
            edsl_logical_input.registers[i] = UINT64_C(0x8000000000000001) + i * UINT64_C(0x0101010101010101);
        else if (vector % 4 == 2)
            edsl_logical_input.registers[i] = UINT64_MAX - i * UINT64_C(0x0101010101010101);
        else
            edsl_logical_input.registers[i] = UINT64_C(0x0000800000000000) + i * UINT64_C(0x800000000000001);
    }
    edsl_logical_input.registers[contract->destination] = left[vector];
    if (contract->source != contract->destination)
        edsl_logical_input.registers[contract->source] = right[vector];
    static const uint64_t flags[] = { 0x202, 0xed7 };
    edsl_logical_input.flags = flags[vector % 2];
    struct snapshot expected = edsl_logical_input;
    uint64_t result = requested_result(contract->operation,
        expected.registers[contract->destination], expected.registers[contract->source]);
    expected.registers[contract->destination] = result;
    edsl_logical_probe(contract->code);
    expected.flags = requested_flags(edsl_logical_effective_flags, result);
    int matches = memcmp(expected.registers, edsl_logical_output.registers, sizeof expected.registers) == 0 &&
        (expected.flags & ~UINT64_C(0x10)) == (edsl_logical_output.flags & ~UINT64_C(0x10));
    if (!matches || !emit) return matches;

    size_t length = (size_t)((uintptr_t)contract->end - (uintptr_t)contract->code);
    printf("-- Native requested %s, vector %u; captured AF is an explicit witness.\n", contract->name, vector);
    printf("theorem observed_%s_%u : observe %s (entry ", contract->name, vector,
        edsl_logical_output.flags & UINT64_C(0x10) ? "true" : "false");
    print_bytes(contract->code, length);
    printf(" %" PRIuPTR " ", (uintptr_t)contract->code);
    print_words(edsl_logical_input.registers, register_count);
    printf(" %" PRIu64 ") = some (", edsl_logical_effective_flags);
    print_words(edsl_logical_output.registers, register_count);
    printf(",%" PRIu64 ",%" PRIuPTR ",[]) := by rfl\n",
        edsl_logical_output.flags, (uintptr_t)contract->end);
    return 1;
}

int main(int argc, char **argv)
{
    if (argc != 2) return 2;
    FILE *file = fopen(argv[1], "rb");
    if (!file) return 2;
    size_t size = (size_t)((uintptr_t)edsl_logical_section_end - (uintptr_t)edsl_logical_section_start);
    unsigned char *bytes = malloc(size + 1);
    if (!bytes) { fclose(file); return 2; }
    size_t amount = fread(bytes, 1, size + 1, file);
    int failed = ferror(file);
    fclose(file);
    if (failed || amount != size || memcmp(bytes, edsl_logical_section_start, size) != 0) {
        fputs("Final ELF section extraction differs from executed bytes\n", stderr);
        free(bytes);
        return 2;
    }
    free(bytes);
    puts("/- Finite native register AND64/OR64/XOR64 observations. An independent C\n"
         "mathematical contract checked all 16 GPRs and effective RFLAGS, masking\n"
         "only undefined AF. Actual captured AF explicitly witnesses full replay.\n"
         "RIP uses extracted continuation labels; [] is the independently requested\n"
         "operand-read footprint, not a hardware trace. -/\n"
         "import EDSL.X86.Sequential.Machine\nimport EDSL.Audit\n"
         "namespace EDSL.Tests.NativeSequentialLogical64\nopen EDSL.X86\n"
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
    unsigned int counts[3] = { 0, 0, 0 }, captured_af[2] = { 0, 0 };
    for (size_t i = 0; i < sizeof contracts / sizeof contracts[0]; ++i) {
        for (unsigned int vector = 0; vector < vector_count; ++vector) {
            if (run_case(&contracts[i], vector, 1) != 1) {
                fprintf(stderr, "Independent native contract failed: %s/%u\n", contracts[i].name, vector);
                return 1;
            }
            ++counts[contracts[i].operation];
            ++captured_af[(edsl_logical_output.flags & UINT64_C(0x10)) != 0];
        }
    }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        unsigned int vector;
        for (vector = 0; vector < vector_count; ++vector)
            if (run_case(&mutants[i], vector, 0) == 0) break;
        if (vector == vector_count) {
            fprintf(stderr, "Independent observer failed to reject owned mutant: %s\n", mutants[i].name);
            return 1;
        }
        fprintf(stderr, "REJECTED owned mutant: %s (vector %u)\n", mutants[i].name, vector);
    }
    puts("end EDSL.Tests.NativeSequentialLogical64\n#audit_edsl");
    fprintf(stderr, "Checked %u native observations (%u AND64, %u OR64, %u XOR64) across %zu windows; "
        "rejected %zu owned semantic mutants; final ELF bytes matched; captured AF=0: %u, AF=1: %u\n",
        counts[0] + counts[1] + counts[2], counts[0], counts[1], counts[2],
        sizeof contracts / sizeof contracts[0], sizeof mutants / sizeof mutants[0],
        captured_af[0], captured_af[1]);
    return 0;
}
