/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { register_count = 16, no_index = -1 };
struct snapshot { uint64_t registers[register_count]; uint64_t flags; };
_Static_assert(offsetof(struct snapshot, flags) == 128 && sizeof(struct snapshot) == 136,
    "Assembly snapshot ABI changed");
struct snapshot edsl_arithmetic_input, edsl_arithmetic_output;
uint64_t edsl_arithmetic_effective_flags;
extern void edsl_arithmetic_probe(const unsigned char *);
extern const unsigned char edsl_arithmetic_section_start[], edsl_arithmetic_section_end[];

enum kind { address_value, addition };
struct contract {
    const char *name;
    const unsigned char *code, *end;
    enum kind kind;
    unsigned int destination, source, base;
    int index;
    unsigned int scale;
};
/* Requested operations, independently of instruction encodings. The observer
 * has no opcode, REX, ModRM or SIB decoder. Register numbers follow the stated
 * snapshot ABI, not an inference from the executed bytes. */
#define LEA_PLAIN(X) \
    X(lp0,address_value,0,0,1,no_index,0) \
    X(lp1,address_value,1,0,2,no_index,0) \
    X(lp2,address_value,2,0,3,no_index,0) \
    X(lp3,address_value,3,0,6,no_index,0) \
    X(lp4,address_value,4,0,7,no_index,0) \
    X(lp5,address_value,5,0,8,no_index,0) \
    X(lp6,address_value,6,0,9,no_index,0) \
    X(lp7,address_value,7,0,10,no_index,0) \
    X(lp8,address_value,8,0,11,no_index,0) \
    X(lp9,address_value,9,0,14,no_index,0) \
    X(lp10,address_value,10,0,15,no_index,0) \
    X(lp11,address_value,11,0,0,no_index,0) \
    X(lp12,address_value,12,0,1,no_index,0) \
    X(lp13,address_value,13,0,2,no_index,0) \
    X(lp14,address_value,14,0,3,no_index,0) \
    X(lp15,address_value,15,0,6,no_index,0) \
    X(lx0,address_value,0,0,3,no_index,0) \
    X(lx1,address_value,0,0,11,no_index,0) \
    X(lx2,address_value,8,0,3,no_index,0) \
    X(lx3,address_value,8,0,11,no_index,0)
#define LEA_SIB(X,S) \
    X(ls##S##_0,address_value,2,0,0,1,S) \
    X(ls##S##_1,address_value,2,0,8,1,S) \
    X(ls##S##_2,address_value,2,0,0,9,S) \
    X(ls##S##_3,address_value,2,0,8,9,S) \
    X(ls##S##_4,address_value,10,0,0,1,S) \
    X(ls##S##_5,address_value,10,0,8,1,S) \
    X(ls##S##_6,address_value,10,0,0,9,S) \
    X(ls##S##_7,address_value,10,0,8,9,S)
#define LEA_ALIASES(X) \
    X(lbase,address_value,8,0,8,9,1) \
    X(lindex,address_value,9,0,8,9,1) \
    X(lsame,address_value,10,0,9,9,2) \
    X(lall,address_value,9,0,9,9,3) \
    X(lrspbase,address_value,4,0,4,5,1) \
    X(lr12base,address_value,4,0,12,5,1) \
    X(lr12index,address_value,12,0,4,12,2) \
    X(lr12all,address_value,12,0,12,12,0)
#define ADD_PAIRS(X) \
    X(a01_0,addition,0,1,0,no_index,0) \
    X(a01_1,addition,1,10,0,no_index,0) \
    X(a01_2,addition,2,3,0,no_index,0) \
    X(a01_3,addition,3,12,0,no_index,0) \
    X(a01_4,addition,4,5,0,no_index,0) \
    X(a01_5,addition,5,14,0,no_index,0) \
    X(a01_6,addition,6,7,0,no_index,0) \
    X(a01_7,addition,7,8,0,no_index,0) \
    X(a01_8,addition,8,9,0,no_index,0) \
    X(a01_9,addition,9,2,0,no_index,0) \
    X(a01_10,addition,10,11,0,no_index,0) \
    X(a01_11,addition,11,4,0,no_index,0) \
    X(a01_12,addition,12,13,0,no_index,0) \
    X(a01_13,addition,13,6,0,no_index,0) \
    X(a01_14,addition,14,15,0,no_index,0) \
    X(a01_15,addition,15,0,0,no_index,0) \
    X(a03_0,addition,0,15,0,no_index,0) \
    X(a03_1,addition,1,0,0,no_index,0) \
    X(a03_2,addition,2,9,0,no_index,0) \
    X(a03_3,addition,3,2,0,no_index,0) \
    X(a03_4,addition,4,11,0,no_index,0) \
    X(a03_5,addition,5,4,0,no_index,0) \
    X(a03_6,addition,6,13,0,no_index,0) \
    X(a03_7,addition,7,6,0,no_index,0) \
    X(a03_8,addition,8,7,0,no_index,0) \
    X(a03_9,addition,9,8,0,no_index,0) \
    X(a03_10,addition,10,1,0,no_index,0) \
    X(a03_11,addition,11,10,0,no_index,0) \
    X(a03_12,addition,12,3,0,no_index,0) \
    X(a03_13,addition,13,12,0,no_index,0) \
    X(a03_14,addition,14,5,0,no_index,0) \
    X(a03_15,addition,15,14,0,no_index,0)
#define ADD_SELF(X,N) X(aself##N,addition,N,N,0,no_index,0)
#define ADD_EXTRAS(X) \
    X(ax01_0,addition,0,3,0,no_index,0) \
    X(ax01_1,addition,8,3,0,no_index,0) \
    X(ax01_2,addition,0,11,0,no_index,0) \
    X(ax01_3,addition,8,11,0,no_index,0) \
    X(ax03_0,addition,3,0,0,no_index,0) \
    X(ax03_1,addition,3,8,0,no_index,0) \
    X(ax03_2,addition,11,0,0,no_index,0) \
    X(ax03_3,addition,11,8,0,no_index,0)
#define MUTANTS(X) \
    X(mutant_lea_scale,address_value,0,0,3,1,1) \
    X(mutant_lea_base,address_value,0,0,3,1,1) \
    X(mutant_lea_width,address_value,0,0,3,1,1) \
    X(mutant_lea_flags,address_value,0,0,3,1,1) \
    X(mutant_add_source,addition,0,1,0,no_index,0) \
    X(mutant_add_width,addition,0,1,0,no_index,0) \
    X(mutant_add_flags,addition,0,1,0,no_index,0) \
    X(mutant_add_carry,addition,0,1,0,no_index,0) \
    X(mutant_add_direction,addition,0,1,0,no_index,0)
#define ALL_LEA(X) LEA_PLAIN(X) LEA_SIB(X,0) LEA_SIB(X,1) LEA_SIB(X,2) LEA_SIB(X,3) LEA_ALIASES(X)
#define ALL_ADD(X) ADD_PAIRS(X) \
    ADD_SELF(X,0) ADD_SELF(X,1) ADD_SELF(X,2) ADD_SELF(X,3) \
    ADD_SELF(X,4) ADD_SELF(X,5) ADD_SELF(X,6) ADD_SELF(X,7) \
    ADD_SELF(X,8) ADD_SELF(X,9) ADD_SELF(X,10) ADD_SELF(X,11) \
    ADD_SELF(X,12) ADD_SELF(X,13) ADD_SELF(X,14) ADD_SELF(X,15) ADD_EXTRAS(X)
#define DECLARE(name,k,d,s,b,i,c) \
    extern const unsigned char edsl_arithmetic_##name[], edsl_arithmetic_##name##_end[];
ALL_LEA(DECLARE) ALL_ADD(DECLARE) MUTANTS(DECLARE)
#define ENTRY(name,k,d,s,b,i,c) \
    {#name,edsl_arithmetic_##name,edsl_arithmetic_##name##_end,k,d,s,b,i,c},
static const struct contract contracts[] = { ALL_LEA(ENTRY) ALL_ADD(ENTRY) };
static const struct contract mutants[] = { MUTANTS(ENTRY) };

/* A mathematical unsigned 65-bit sum, sign comparison, nibble addition and
 * low-byte population count independently define the six ADD status flags. */
static uint64_t addition_flags(uint64_t old, uint64_t left, uint64_t right)
{
    const uint64_t arithmetic = UINT64_C(0x8d5);
    __uint128_t wide = (__uint128_t)left + (__uint128_t)right;
    uint64_t result = (uint64_t)wide;
    unsigned int population = 0;
    for (unsigned int bit = 0; bit < 8; ++bit) population += (unsigned int)((result >> bit) & 1);
    int negative_left = left > INT64_MAX, negative_right = right > INT64_MAX;
    int negative_result = result > INT64_MAX;
    uint64_t flags = old & ~arithmetic;
    if (wide > UINT64_MAX) flags |= UINT64_C(1);
    if (population % 2 == 0) flags |= UINT64_C(4);
    if ((left % 16) + (right % 16) > 15) flags |= UINT64_C(0x10);
    if (result == 0) flags |= UINT64_C(0x40);
    if (negative_result) flags |= UINT64_C(0x80);
    if (negative_left == negative_right && negative_left != negative_result) flags |= UINT64_C(0x800);
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

enum { lea_vectors = 4, add_vectors = 12 };
static int run_case(const struct contract *contract, unsigned int vector, int emit)
{
    static const uint64_t left[] = {
        0, UINT64_MAX, INT64_MAX, UINT64_C(0x8000000000000000), 0xf, 0x10,
        0x80, UINT64_C(0x100000000), UINT64_C(0xfeedface89abcdef), 1,
        UINT64_C(0xfffffffffffffffe), UINT64_C(0xfffffffffffffff0)
    };
    static const uint64_t right[] = {
        0, 1, 1, UINT64_C(0x8000000000000000), 1, 0xf,
        0x80, UINT64_C(0xffffffff), UINT64_C(0x1122334455667788), 2, 0, 0x10
    };
    for (unsigned int i = 0; i < register_count; ++i) {
        if (vector % lea_vectors == 0)
            edsl_arithmetic_input.registers[i] = UINT64_C(0x100000001) + i * UINT64_C(0x100000011);
        else if (vector % lea_vectors == 1)
            edsl_arithmetic_input.registers[i] = UINT64_C(0x8000000000000001) + i * UINT64_C(0x0101010101010101);
        else if (vector % lea_vectors == 2)
            edsl_arithmetic_input.registers[i] = UINT64_MAX - i * UINT64_C(0x0101010101010101);
        else
            edsl_arithmetic_input.registers[i] = UINT64_C(0x0000800000000000) + i * UINT64_C(0x800000000000001);
    }
    if (contract->kind == addition) {
        edsl_arithmetic_input.registers[contract->destination] = left[vector];
        if (contract->source != contract->destination)
            edsl_arithmetic_input.registers[contract->source] = right[vector];
    }
    static const uint64_t requested_flags[] = { 0x202, 0xed7 };
    edsl_arithmetic_input.flags = requested_flags[vector % 2];
    struct snapshot expected = edsl_arithmetic_input;
    uint64_t before_left = edsl_arithmetic_input.registers[contract->destination];
    uint64_t before_right = edsl_arithmetic_input.registers[contract->source];
    if (contract->kind == address_value) {
        uint64_t value = edsl_arithmetic_input.registers[contract->base];
        if (contract->index != no_index)
            value += edsl_arithmetic_input.registers[contract->index] * (UINT64_C(1) << contract->scale);
        expected.registers[contract->destination] = value;
    } else {
        expected.registers[contract->destination] = before_left + before_right;
    }
    edsl_arithmetic_probe(contract->code);
    expected.flags = contract->kind == addition
        ? addition_flags(edsl_arithmetic_effective_flags, before_left, before_right)
        : edsl_arithmetic_effective_flags;
    int matches = memcmp(expected.registers, edsl_arithmetic_output.registers, sizeof expected.registers) == 0 &&
        expected.flags == edsl_arithmetic_output.flags;
    if (!matches || !emit) return matches;

    size_t length = (size_t)((uintptr_t)contract->end - (uintptr_t)contract->code);
    printf("-- Native requested %s, vector %u; complete captured registers and flags.\n", contract->name, vector);
    printf("theorem observed_%s_%u (af : Bool) : observe af (entry ", contract->name, vector);
    print_bytes(contract->code, length);
    printf(" %" PRIuPTR " ", (uintptr_t)contract->code);
    print_words(edsl_arithmetic_input.registers, register_count);
    printf(" %" PRIu64 ") = some (", edsl_arithmetic_effective_flags);
    print_words(edsl_arithmetic_output.registers, register_count);
    printf(",%" PRIu64 ",%" PRIuPTR ",[]) := by cases af <;> rfl\n",
        edsl_arithmetic_output.flags, (uintptr_t)contract->end);
    return 1;
}

int main(int argc, char **argv)
{
    if (argc != 2) return 2;
    FILE *file = fopen(argv[1], "rb");
    if (!file) return 2;
    size_t size = (size_t)((uintptr_t)edsl_arithmetic_section_end - (uintptr_t)edsl_arithmetic_section_start);
    unsigned char *bytes = malloc(size + 1);
    if (!bytes) return 2;
    size_t amount = fread(bytes, 1, size + 1, file);
    int failed = ferror(file);
    fclose(file);
    if (failed || amount != size || memcmp(bytes, edsl_arithmetic_section_start, size) != 0) {
        fputs("Final ELF section extraction differs from executed bytes\n", stderr);
        free(bytes);
        return 2;
    }
    free(bytes);
    puts("/- Finite native LEA64/register ADD64 observations. An independent C\n"
         "mathematical contract checked all 16 GPRs and complete effective RFLAGS.\n"
         "RIP uses extracted continuation labels; [] is the independently requested\n"
         "operand-read footprint, not a hardware trace. -/\n"
         "import EDSL.X86.Sequential.Machine\nimport EDSL.Audit\n"
         "namespace EDSL.Tests.NativeSequentialArithmetic64\nopen EDSL.X86\n"
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
    unsigned int lea_count = 0, add_count = 0;
    for (size_t i = 0; i < sizeof contracts / sizeof contracts[0]; ++i) {
        unsigned int count = contracts[i].kind == addition ? add_vectors : lea_vectors;
        for (unsigned int vector = 0; vector < count; ++vector) {
            if (run_case(&contracts[i], vector, 1) != 1) {
                fprintf(stderr, "Independent native contract failed: %s/%u\n", contracts[i].name, vector);
                return 1;
            }
            if (contracts[i].kind == addition) ++add_count; else ++lea_count;
        }
    }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        unsigned int count = mutants[i].kind == addition ? add_vectors : lea_vectors;
        unsigned int vector;
        for (vector = 0; vector < count; ++vector)
            if (run_case(&mutants[i], vector, 0) == 0) break;
        if (vector == count) {
            fprintf(stderr, "Independent observer failed to reject owned mutant: %s\n", mutants[i].name);
            return 1;
        }
        fprintf(stderr, "REJECTED owned mutant: %s (vector %u)\n", mutants[i].name, vector);
    }
    puts("end EDSL.Tests.NativeSequentialArithmetic64\n#audit_edsl");
    fprintf(stderr, "Checked %u native observations (%u LEA64, %u register ADD64) across %zu windows; "
        "rejected %zu owned semantic mutants; final ELF bytes matched\n",
        lea_count + add_count, lea_count, add_count, sizeof contracts / sizeof contracts[0],
        sizeof mutants / sizeof mutants[0]);
    return 0;
}
