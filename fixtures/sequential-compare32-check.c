/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { register_count = 16, vector_count = 10 };
struct snapshot { uint64_t registers[register_count]; uint64_t flags; };
_Static_assert(offsetof(struct snapshot, flags) == 128 && sizeof(struct snapshot) == 136,
    "Assembly snapshot ABI changed");
struct snapshot edsl_compare32_input, edsl_compare32_output;
uint64_t edsl_compare32_effective_flags;
extern void edsl_compare32_probe(const unsigned char *);
extern const unsigned char edsl_compare32_section_start[], edsl_compare32_section_end[];

enum operation { compare, intersection, preserve };
struct contract {
    const char *name;
    const unsigned char *code, *end;
    enum operation operation;
    unsigned int left, right;
};
/* Requested operations, not an opcode/REX/ModRM decoder. Register numbers
 * follow the explicit RAX,RCX,RDX,RBX,RSP,RBP,RSI,RDI,R8..R15 snapshot ABI. */
#define REGISTER_CASE(X,P,K,N,R) X(P##_pair##N,K,N,R) X(P##_self##N,K,N,N)
#define REGISTERS(X,P,K) \
    REGISTER_CASE(X,P,K,0,1) REGISTER_CASE(X,P,K,1,2) \
    REGISTER_CASE(X,P,K,2,3) REGISTER_CASE(X,P,K,3,4) \
    REGISTER_CASE(X,P,K,4,5) REGISTER_CASE(X,P,K,5,6) \
    REGISTER_CASE(X,P,K,6,7) REGISTER_CASE(X,P,K,7,8) \
    REGISTER_CASE(X,P,K,8,9) REGISTER_CASE(X,P,K,9,10) \
    REGISTER_CASE(X,P,K,10,11) REGISTER_CASE(X,P,K,11,12) \
    REGISTER_CASE(X,P,K,12,13) REGISTER_CASE(X,P,K,13,14) \
    REGISTER_CASE(X,P,K,14,15) REGISTER_CASE(X,P,K,15,0)
#define PLAIN(X,P,K) \
    X(P##_plain0,K,0,1) X(P##_plain1,K,1,2) \
    X(P##_plain2,K,2,3) X(P##_plain3,K,3,4) \
    X(P##_plain4,K,4,5) X(P##_plain5,K,5,6) \
    X(P##_plain6,K,6,7) X(P##_plain7,K,7,0)
#define MR_REX(X,P,K) \
    X(P##_rex0,K,0,3) X(P##_rex1,K,8,3) \
    X(P##_rex2,K,0,3) X(P##_rex3,K,8,3) \
    X(P##_rex4,K,0,11) X(P##_rex5,K,8,11) \
    X(P##_rex6,K,0,11) X(P##_rex7,K,8,11)
#define RM_REX(X,P,K) \
    X(P##_rex0,K,3,0) X(P##_rex1,K,3,8) \
    X(P##_rex2,K,3,0) X(P##_rex3,K,3,8) \
    X(P##_rex4,K,11,0) X(P##_rex5,K,11,8) \
    X(P##_rex6,K,11,0) X(P##_rex7,K,11,8)
#define POSITIVES(X) \
    REGISTERS(X,cmp39,compare) PLAIN(X,cmp39,compare) MR_REX(X,cmp39,compare) \
    REGISTERS(X,cmp3b,compare) PLAIN(X,cmp3b,compare) RM_REX(X,cmp3b,compare) \
    REGISTERS(X,test85,intersection) PLAIN(X,test85,intersection) MR_REX(X,test85,intersection) \
    X(endbr,preserve,0,0) X(nop1,preserve,0,0) X(nop2,preserve,0,0) \
    X(nop3,preserve,0,0) X(nop4,preserve,0,0) X(nop5,preserve,0,0)
#define MUTANTS(X) \
    X(mutant_cmp_width,compare,0,1) X(mutant_cmp_direction,compare,0,1) \
    X(mutant_cmp_register,compare,0,1) X(mutant_cmp_write,compare,0,1) \
    X(mutant_cmp_flags,compare,0,1) X(mutant_test_width,intersection,0,1) \
    X(mutant_test_register,intersection,0,1) X(mutant_test_write,intersection,0,1) \
    X(mutant_test_flags,intersection,0,1) X(mutant_nop_write,preserve,0,0) \
    X(mutant_nop_flags,preserve,0,0)
#define DECLARE(name,k,l,r) \
    extern const unsigned char edsl_compare32_##name[], edsl_compare32_##name##_end[];
POSITIVES(DECLARE) MUTANTS(DECLARE)
#define ENTRY(name,k,l,r) {#name,edsl_compare32_##name,edsl_compare32_##name##_end,k,l,r},
static const struct contract contracts[] = { POSITIVES(ENTRY) };
static const struct contract mutants[] = { MUTANTS(ENTRY) };

/* CMP uses mathematical integers: unsigned comparison determines borrow;
 * signed difference outside [-2^31,2^31-1] determines overflow; low-nibble
 * comparison determines AF. No implementation bit trick or model call. */
static uint64_t requested_flags(enum operation op, uint64_t old, uint64_t l, uint64_t r)
{
    if (op == preserve) return old;
    uint64_t left = l % UINT64_C(0x100000000), right = r % UINT64_C(0x100000000);
    uint64_t result;
    uint64_t flags = old & ~UINT64_C(0x8d5);
    if (op == compare) {
        result = (left + UINT64_C(0x100000000) - right) % UINT64_C(0x100000000);
        int64_t sl = left <= INT32_MAX ? (int64_t)left : (int64_t)left - INT64_C(0x100000000);
        int64_t sr = right <= INT32_MAX ? (int64_t)right : (int64_t)right - INT64_C(0x100000000);
        int64_t difference = sl - sr;
        if (left < right) flags |= 1;
        if (left % 16 < right % 16) flags |= 0x10;
        if (difference < INT32_MIN || difference > INT32_MAX) flags |= 0x800;
    } else {
        result = 0;
        for (unsigned int bit = 0; bit < 32; ++bit)
            if ((left >> bit) % 2 && (right >> bit) % 2) result += UINT64_C(1) << bit;
    }
    unsigned int population = 0;
    for (unsigned int bit = 0; bit < 8; ++bit) population += (unsigned int)((result >> bit) % 2);
    if (population % 2 == 0) flags |= 4;
    if (result == 0) flags |= 0x40;
    if (result > INT32_MAX) flags |= 0x80;
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
        0, UINT64_C(0xdeadbeefffffffff), 0x7fffffff, 0x80000000, 0x10,
        0x80, UINT64_C(0x100000000), UINT64_C(0xfeedface00000003),
        UINT64_C(0xaaaaaaaa80000000), UINT64_C(0xffffffffffffffff)
    };
    static const uint64_t right[vector_count] = {
        1, UINT64_C(0x1122334400000000), 0xffffffff, 1, 1,
        0xff, UINT64_C(0x200000000), UINT64_C(0x1122334400000005),
        UINT64_C(0x55555555ffffffff), UINT64_C(0x1111111180000000)
    };
    for (unsigned int i = 0; i < register_count; ++i) {
        switch (vector % 4) {
        case 0: edsl_compare32_input.registers[i] = UINT64_C(0x100000001) + i * UINT64_C(0x100000011); break;
        case 1: edsl_compare32_input.registers[i] = UINT64_C(0x8000000000000001) + i * UINT64_C(0x0101010101010101); break;
        case 2: edsl_compare32_input.registers[i] = UINT64_MAX - i * UINT64_C(0x0101010101010101); break;
        default: edsl_compare32_input.registers[i] = UINT64_C(0x0000800000000000) + i * UINT64_C(0x800000000000001); break;
        }
    }
    if (contract->operation != preserve) {
        edsl_compare32_input.registers[contract->left] = left[vector];
        if (contract->right != contract->left)
            edsl_compare32_input.registers[contract->right] = right[vector];
    }
    static const uint64_t flags[] = { 0x202, 0xed7 };
    edsl_compare32_input.flags = flags[vector % 2];
    struct snapshot expected = edsl_compare32_input;
    edsl_compare32_probe(contract->code);
    expected.flags = requested_flags(contract->operation, edsl_compare32_effective_flags,
        expected.registers[contract->left], expected.registers[contract->right]);
    uint64_t mask = contract->operation == intersection ? ~UINT64_C(0x10) : UINT64_MAX;
    int matches = memcmp(expected.registers, edsl_compare32_output.registers, sizeof expected.registers) == 0 &&
        (expected.flags & mask) == (edsl_compare32_output.flags & mask);
    if (!matches || !emit) return matches;
    size_t length = (size_t)((uintptr_t)contract->end - (uintptr_t)contract->code);
    printf("-- Native requested %s, vector %u.\n", contract->name, vector);
    printf("theorem observed_%s_%u : observe %s (entry ", contract->name, vector,
        contract->operation == intersection && (edsl_compare32_output.flags & 0x10) ? "true" : "false");
    print_bytes(contract->code, length);
    printf(" %" PRIuPTR " ", (uintptr_t)contract->code);
    print_words(edsl_compare32_input.registers, register_count);
    printf(" %" PRIu64 ") = some (", edsl_compare32_effective_flags);
    print_words(edsl_compare32_output.registers, register_count);
    printf(",%" PRIu64 ",%" PRIuPTR ",[]) := by rfl\n",
        edsl_compare32_output.flags, (uintptr_t)contract->end);
    return 1;
}

int main(int argc, char **argv)
{
    if (argc != 2) return 2;
    FILE *file = fopen(argv[1], "rb");
    if (!file) return 2;
    size_t size = (size_t)((uintptr_t)edsl_compare32_section_end - (uintptr_t)edsl_compare32_section_start);
    unsigned char *bytes = malloc(size + 1);
    if (!bytes) { fclose(file); return 2; }
    size_t amount = fread(bytes, 1, size + 1, file);
    int failed = ferror(file);
    fclose(file);
    /* This must precede every probe and all generated Lean output. */
    if (failed || amount != size || memcmp(bytes, edsl_compare32_section_start, size) != 0) {
        fputs("Final ELF section extraction differs from executed bytes\n", stderr);
        free(bytes);
        return 2;
    }
    free(bytes);
    puts("/- Finite Linux x86-64 CMP32/TEST32 and CET/IBT-disabled ENDBR/NOP observations.\n"
         "Independent C contracts check all 16 GPRs and complete effective RFLAGS.\n"
         "Only TEST AF is unconstrained, with its captured value witnessing replay.\n"
         "RIP uses linked continuation labels; [] is the independently requested\n"
         "operand-read footprint, not a hardware memory-access trace. -/\n"
         "import EDSL.X86.Sequential.Machine\nimport EDSL.Audit\n"
         "namespace EDSL.Tests.NativeSequentialCompare32\nopen EDSL.X86\n"
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
    unsigned int counts[3] = {0,0,0}, test_af[2] = {0,0};
    for (size_t i = 0; i < sizeof contracts / sizeof contracts[0]; ++i) {
        for (unsigned int vector = 0; vector < vector_count; ++vector) {
            if (!run_case(&contracts[i], vector, 1)) {
                fprintf(stderr, "Independent native contract failed: %s/%u\n", contracts[i].name, vector);
                return 1;
            }
            ++counts[contracts[i].operation];
            if (contracts[i].operation == intersection)
                ++test_af[(edsl_compare32_output.flags & 0x10) != 0];
        }
    }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        unsigned int vector;
        for (vector = 0; vector < vector_count; ++vector)
            if (!run_case(&mutants[i], vector, 0)) break;
        if (vector == vector_count) {
            fprintf(stderr, "Independent observer failed to reject owned mutant: %s\n", mutants[i].name);
            return 1;
        }
        fprintf(stderr, "REJECTED owned mutant: %s (vector %u)\n", mutants[i].name, vector);
    }
    puts("end EDSL.Tests.NativeSequentialCompare32\n#audit_edsl");
    fprintf(stderr, "Checked %u native observations (%u CMP32, %u TEST32, %u ENDBR/NOP) across %zu windows; "
        "rejected %zu owned semantic mutants; final ELF bytes matched; TEST AF=0: %u, AF=1: %u\n",
        counts[0] + counts[1] + counts[2], counts[0], counts[1], counts[2],
        sizeof contracts / sizeof contracts[0], sizeof mutants / sizeof mutants[0], test_af[0], test_af[1]);
    return ferror(stdout) ? 1 : 0;
}
