/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

enum { register_count = 16, no_index = -1, vectors = 12 };
enum { changed_register = 1, changed_arithmetic = 2, changed_nonarith = 4, changed_memory = 8 };
static const uint64_t arithmetic = UINT64_C(0x8d5), varied_flags = UINT64_C(0x200cd5);
struct snapshot { uint64_t registers[register_count]; uint64_t flags; };
_Static_assert(offsetof(struct snapshot, flags) == 128 && sizeof(struct snapshot) == 136,
    "Assembly snapshot ABI changed");
struct snapshot edsl_add_memory64_input, edsl_add_memory64_initial, edsl_add_memory64_output;
extern void edsl_add_memory64_probe(const unsigned char *);
extern const unsigned char edsl_add_memory64_section_start[], edsl_add_memory64_section_end[];
struct contract {
    const char *name;
    const unsigned char *code, *end;
    unsigned int destination, base;
    int index;
    unsigned int scale;
};
/* Independently requested operands, not decoded from REX/ModRM/SIB bytes. */
#define PLAIN(X) \
    X(plain0,0,1,no_index,0) X(plain1,1,2,no_index,0) \
    X(plain2,2,3,no_index,0) X(plain3,3,6,no_index,0) \
    X(plain4,4,7,no_index,0) X(plain5,5,8,no_index,0) \
    X(plain6,6,9,no_index,0) X(plain7,7,10,no_index,0) \
    X(plain8,8,11,no_index,0) X(plain9,9,14,no_index,0) \
    X(plain10,10,15,no_index,0) X(plain11,11,0,no_index,0) \
    X(plain12,12,1,no_index,0) X(plain13,13,2,no_index,0) \
    X(plain14,14,3,no_index,0) X(plain15,15,6,no_index,0) \
    X(ignored_x0,0,3,no_index,0) X(ignored_x1,0,11,no_index,0) \
    X(ignored_x2,8,3,no_index,0) X(ignored_x3,8,11,no_index,0)
#define SCALED(X,S) \
    X(scale##S##_0,2,0,1,S) X(scale##S##_1,2,8,1,S) \
    X(scale##S##_2,2,0,9,S) X(scale##S##_3,2,8,9,S) \
    X(scale##S##_4,10,0,1,S) X(scale##S##_5,10,8,1,S) \
    X(scale##S##_6,10,0,9,S) X(scale##S##_7,10,8,9,S)
#define EXTRAS(X) \
    X(alias_base,8,8,9,1) X(alias_index,9,8,9,1) \
    X(same_address,10,9,9,2) X(alias_all,9,9,9,3) \
    X(rsp_base,4,4,5,1) X(r12_base,4,12,13,1) \
    X(r12_index,12,4,12,2) X(r12_all,12,12,12,0) \
    X(plain_alias,0,0,1,0) X(plain_self,15,15,no_index,0) \
    X(gcc_sum,2,7,0,3) X(clang_sum,0,7,1,3)
#define POSITIVES(X) PLAIN(X) SCALED(X,0) SCALED(X,1) SCALED(X,2) SCALED(X,3) EXTRAS(X)
#define MUTANTS(X) \
    X(narrow32_sum_load,0,7,no_index,0) X(narrow32_load,0,7,no_index,0) \
    X(wrong_operation,0,7,no_index,0) X(wrong_destination,0,7,no_index,0) \
    X(wrong_scale,0,7,1,1) X(wrong_ea,0,7,no_index,0) \
    X(omitted_flags,0,7,no_index,0) X(cleared_carry,0,7,no_index,0) \
    X(changed_nonarith,0,7,no_index,0)
#define DECLARE(name,d,b,i,s) \
    extern const unsigned char edsl_add_memory64_##name[], edsl_add_memory64_##name##_end[];
POSITIVES(DECLARE) MUTANTS(DECLARE)
#define ENTRY(name,d,b,i,s) {#name,edsl_add_memory64_##name,edsl_add_memory64_##name##_end,d,b,i,s},
static const struct contract contracts[] = { POSITIVES(ENTRY) };
static const struct contract mutants[] = { MUTANTS(ENTRY) };

/* Independent mathematical definitions: unsigned 65-bit sum, nibble carry,
 * signs and low-byte population. Preserve every other effective flag bit. */
static uint64_t addition_flags(uint64_t old, uint64_t left, uint64_t right)
{
    __uint128_t wide = (__uint128_t)left + (__uint128_t)right;
    uint64_t result = (uint64_t)wide, flags = old & ~arithmetic;
    unsigned int population = 0;
    for (unsigned int bit = 0; bit < 8; ++bit) population += (unsigned int)((result >> bit) & 1);
    int left_negative = left > INT64_MAX, right_negative = right > INT64_MAX;
    int result_negative = result > INT64_MAX;
    if (wide > UINT64_MAX) flags |= 1;
    if (population % 2 == 0) flags |= 4;
    if (left % 16 + right % 16 > 15) flags |= 0x10;
    if (result == 0) flags |= 0x40;
    if (result_negative) flags |= 0x80;
    if (left_negative == right_negative && left_negative != result_negative) flags |= 0x800;
    return flags;
}
static uint64_t effective_address(const struct contract *c, const struct snapshot *s)
{
    uint64_t address = s->registers[c->base];
    if (c->index != no_index) address += s->registers[c->index] * (UINT64_C(1) << c->scale);
    return address;
}
static void print_words(const uint64_t *values)
{
    putchar('[');
    for (unsigned int i = 0; i < register_count; ++i) printf("%s%" PRIu64, i ? "," : "", values[i]);
    putchar(']');
}
static void print_bytes(const unsigned char *values, size_t count)
{
    putchar('[');
    for (size_t i = 0; i < count; ++i) printf("%s%u", i ? "," : "", (unsigned int)values[i]);
    putchar(']');
}
static uint64_t seen_set, seen_clear;
static unsigned int high_index_cases, unaligned_cases, guard_end_cases;

/* Returns a mismatch category mask, or -1 for harness/environment failure.
 * Negative windows use only small indices and padded targets. A fault, signal
 * or timeout cannot produce a successful semantic-mutant rejection. */
static int run_case(const struct contract *c, unsigned char *memory, size_t page,
    unsigned char *before, unsigned int vector, int emit)
{
    static const uint64_t left[vectors] = {
        0, UINT64_MAX, INT64_MAX, UINT64_C(0x8000000000000000), 0xf, 0x10,
        0x80, UINT64_C(0x100000000), UINT64_C(0xfeedface89abcdef), 1,
        UINT64_C(0xfffffffffffffffe), UINT64_C(0xfffffffffffffff0)
    };
    static const unsigned char source[vectors][8] = {
        {0,0,0,0,0,0,0,0}, {1,0,0,0,0,0,0,0}, {1,0,0,0,0,0,0,0},
        {0,0,0,0,0,0,0,0x80}, {1,0,0,0,0,0,0,0}, {0xf,0,0,0,0,0,0,0},
        {0x80,0,0,0,0,0,0,0}, {0xff,0xff,0xff,0xff,0,0,0,0},
        {0x88,0x77,0x66,0x55,0x44,0x33,0x22,0x11}, {2,0,0,0,0,0,0,0},
        {0,0,0,0,0,0,0,0}, {0x10,0,0,0,0,0,0,0}
    };
    size_t offset = !emit ? 128 : vector % 3 == 2 ? page - 8 : vector % 3 == 0 ? 2 : 3;
    if (c->index == (int)c->base && c->scale == 0) offset &= ~(size_t)1;
    if (mprotect(memory, page, PROT_READ | PROT_WRITE)) return -1;
    for (size_t i = 0; i < page; ++i) memory[i] = (unsigned char)(0x81u + i * 37u + vector * 29u);
    memcpy(memory + offset, source[vector], 8);
    memcpy(before, memory, page);
    if (mprotect(memory, page, PROT_READ)) return -1;
    for (unsigned int i = 0; i < register_count; ++i)
        edsl_add_memory64_input.registers[i] = UINT64_C(0xabc1000000000000) +
            (uint64_t)(i + 1) * UINT64_C(0x0101000020304051) + vector * UINT64_C(0x1122334455667788);
    edsl_add_memory64_input.registers[c->destination] = left[vector];
    edsl_add_memory64_input.flags = vector % 2 ? UINT64_C(0x200ed7) : UINT64_C(0x202);
    uint64_t address = (uint64_t)(uintptr_t)(memory + offset);
    if (c->index == no_index) {
        edsl_add_memory64_input.registers[c->base] = address;
    } else if ((unsigned int)c->index == c->base) {
        uint64_t factor = 1 + (UINT64_C(1) << c->scale), inverse = 1;
        if (factor == 2) {
            if (address % 2) return -1;
            edsl_add_memory64_input.registers[c->base] = address / 2;
        } else {
            /* Odd factors are invertible modulo 2^64. Choose a real mapped
             * target first, then solve (1 + scale) * register = target. */
            for (unsigned int i = 0; i < 6; ++i) inverse *= 2 - factor * inverse;
            edsl_add_memory64_input.registers[c->base] = address * inverse;
        }
    } else {
        static const uint64_t high_indices[] = {
            UINT64_C(0x100000003), UINT64_C(0x8000000100000003), UINT64_C(0xfffffffffffffffd)
        };
        uint64_t index = emit ? high_indices[vector % 3] : 3;
        edsl_add_memory64_input.registers[c->index] = index;
        edsl_add_memory64_input.registers[c->base] = address - index * (UINT64_C(1) << c->scale);
    }
    /* Padded alternative for the wrong-EA mutant; never dereference an
     * arbitrary register or a truncated high-index address. */
    if (!emit) edsl_add_memory64_input.registers[6] = address + 16;
    if (effective_address(c, &edsl_add_memory64_input) != address) return -1;
    edsl_add_memory64_probe(c->code);
    if (memcmp(edsl_add_memory64_input.registers, edsl_add_memory64_initial.registers,
            sizeof edsl_add_memory64_initial.registers) ||
        ((edsl_add_memory64_initial.flags ^ edsl_add_memory64_input.flags) & varied_flags)) return -1;
    /* Oracle inputs are the actual installed GPRs/flags and pre-probe bytes.
     * Aliasing address registers can constrain the pre-destination value. */
    struct snapshot expected = edsl_add_memory64_initial;
    uint64_t actual_address = effective_address(c, &edsl_add_memory64_initial);
    if (actual_address != address) return -1;
    uint64_t right = 0;
    for (unsigned int i = 0; i < 8; ++i) right += (uint64_t)before[offset + i] * (UINT64_C(1) << (8 * i));
    uint64_t actual_left = edsl_add_memory64_initial.registers[c->destination];
    expected.registers[c->destination] = (uint64_t)((__uint128_t)actual_left + right);
    expected.flags = addition_flags(edsl_add_memory64_initial.flags, actual_left, right);
    int mismatch = 0;
    if (memcmp(expected.registers, edsl_add_memory64_output.registers, sizeof expected.registers))
        mismatch |= changed_register;
    uint64_t different_flags = expected.flags ^ edsl_add_memory64_output.flags;
    if (different_flags & arithmetic) mismatch |= changed_arithmetic;
    if (different_flags & ~arithmetic) mismatch |= changed_nonarith;
    if (memcmp(memory, before, page)) mismatch |= changed_memory;
    if (mismatch || !emit) return mismatch;
    seen_set |= edsl_add_memory64_output.flags;
    seen_clear |= ~edsl_add_memory64_output.flags;
    if (c->index != no_index && edsl_add_memory64_initial.registers[c->index] > UINT32_MAX) ++high_index_cases;
    if (offset % 8) ++unaligned_cases;
    if (offset == page - 8) ++guard_end_cases;
    size_t length = (size_t)((uintptr_t)c->end - (uintptr_t)c->code);
    printf("-- CPU %s/%u: page offset %zu; all %zu owned bytes unchanged; source qword %" PRIu64 ".\n",
        c->name, vector, offset, page, right);
    printf("def initial_%s_%u : State := entry ", c->name, vector);
    print_bytes(c->code, length);
    printf(" %" PRIuPTR " ", (uintptr_t)c->code);
    print_words(edsl_add_memory64_initial.registers);
    printf(" %" PRIu64 " %" PRIu64 " ", edsl_add_memory64_initial.flags, actual_address);
    /* Literal bytes come from the actual page snapshot, not a model writer. */
    print_bytes(before + offset, 8);
    printf("\ntheorem observed_%s_%u (af : Bool) : observe af initial_%s_%u = some (",
        c->name, vector, c->name, vector);
    print_words(edsl_add_memory64_output.registers);
    printf(",%" PRIu64 ",%" PRIuPTR ",initial_%s_%u.memory,[⟨.data,%" PRIu64 ",8⟩]) := by cases af <;> rfl\n",
        edsl_add_memory64_output.flags, (uintptr_t)c->end, c->name, vector, actual_address);
    return 0;
}

static int authenticate(const char *path)
{
    FILE *file = fopen(path, "rb");
    if (!file) return 0;
    size_t size = (size_t)((uintptr_t)edsl_add_memory64_section_end - (uintptr_t)edsl_add_memory64_section_start);
    unsigned char *bytes = malloc(size + 1);
    if (!bytes) { fclose(file); return 0; }
    size_t count = fread(bytes, 1, size + 1, file);
    int matches = !ferror(file) && count == size && !memcmp(bytes, edsl_add_memory64_section_start, size);
    if (fclose(file)) matches = 0;
    free(bytes);
    return matches;
}
int main(int argc, char **argv)
{
    /* No probe, stdout, mmap or execution derived from an input file precedes
     * full-section authentication. Only compiled-in owned windows can run. */
    if (argc != 2 || !authenticate(argv[1])) {
        fputs("Final ELF section extraction differs from executed bytes\n", stderr);
        return 2;
    }
    long page_size = sysconf(_SC_PAGESIZE);
    if (page_size < 4096 || (uint64_t)page_size > SIZE_MAX / 3) return 2;
    size_t page = (size_t)page_size;
    unsigned char *mapping = mmap(NULL, page * 3, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    unsigned char *before = malloc(page);
    if (mapping == MAP_FAILED || !before) return 2;
    unsigned char *memory = mapping + page;
    if ((uintptr_t)memory <= UINT32_MAX) return 2;
    puts("/- Finite owned Linux x86-64 memory-source ADD64 CPU observations.\n"
         "C checked all 16 GPRs, complete effective RFLAGS and the entire RO page.\n"
         "Replay models the observed eight source bytes and exact instruction\n"
         "bytes as separate accessible regions, with no writable addresses.\n"
         "Memory equality checks the entire modeled RAM and permission maps.\n"
         "The DATA8 footprint is an independent contract, not a CPU access trace.\n"
         "Both AF choices are checked. No universal ISA/CPU/OS, fault-delivery,\n"
         "timing, speculation, concurrency or source-preservation claim. -/\n"
         "import EDSL.X86.Sequential.Machine\nimport EDSL.Audit\n"
         "namespace EDSL.Tests.NativeSequentialAddMemory64\nopen EDSL.X86\n"
         "def allRegisters : List Register := [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,"
         ".r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]\n"
         "def entry (code : List Byte) (pc : Word) (registers : List Word)\n"
         "    (flags address : Word) (bytes : List Byte) : State where\n"
         "  registers r := registers.getD (allRegisters.idxOf r) 0\n"
         "  rip := pc\n  flags := flags\n"
         "  memory := {\n"
         "    read := fun a => if pc.toNat ≤ a.toNat ∧ a.toNat < pc.toNat + code.length\n"
         "      then code[a.toNat - pc.toNat]?\n"
         "      else if address.toNat ≤ a.toNat ∧ a.toNat < address.toNat + bytes.length\n"
         "      then bytes[a.toNat - address.toNat]? else none\n"
         "    executable := fun a => decide (pc.toNat ≤ a.toNat ∧ a.toNat < pc.toNat + code.length)\n"
         "    writable := fun _ => false }\n"
         "def observe (af : Bool) (initial : State) :\n"
         "    Option (List Word × Word × Word × Memory × List Sequential.Read) := do\n"
         "  let observation ← (Sequential.step af initial).toOption\n"
         "  match observation.result with\n"
         "  | .next final => return (allRegisters.map final.registers,final.flags,final.rip,\n"
         "      final.memory,observation.reads)\n"
         "  | _ => none");
    unsigned int observations = 0;
    for (size_t i = 0; i < sizeof contracts / sizeof contracts[0]; ++i) {
        for (unsigned int vector = 0; vector < vectors; ++vector) {
            int mismatch = run_case(&contracts[i], memory, page, before, vector, 1);
            if (mismatch) {
                fprintf(stderr, "Independent native contract failed: %s/%u category-mask=%d\n",
                    contracts[i].name, vector, mismatch);
                return 1;
            }
            ++observations;
        }
    }
    if ((seen_set & seen_clear & varied_flags) != varied_flags ||
        !high_index_cases || !unaligned_cases || !guard_end_cases) {
        fputs("Native value/flag/address coverage incomplete\n", stderr);
        return 1;
    }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        /* Value/address mutants must change a GPR and may change arithmetic
         * flags. Flag-only mutants must fail ONLY their named flag category. */
        unsigned int vector = i == 6 || i == 7 ? 1 : 8;
        int required = i < 6 ? changed_register : i < 8 ? changed_arithmetic : changed_nonarith;
        int allowed = i < 6 ? changed_register | changed_arithmetic : required;
        int mismatch = run_case(&mutants[i], memory, page, before, vector, 0);
        if (mismatch < 0 || !(mismatch & required) || (mismatch & ~allowed)) {
            fprintf(stderr, "Owned mutant did not fail its required category: %s mask=%d required=%d allowed=%d\n",
                mutants[i].name, mismatch, required, allowed);
            return 1;
        }
        fprintf(stderr, "Rejected owned mutant %s: category-mask=%d\n", mutants[i].name, mismatch);
    }
    puts("end EDSL.Tests.NativeSequentialAddMemory64\n#audit_edsl");
    fprintf(stderr, "Checked %u native ADD64 memory observations across %zu windows; "
        "%u high-index, %u unaligned, %u last-qword guard-edge; "
        "all 16 GPRs, complete flags and %zu-byte RO-page snapshots; "
        "rejected %zu owned semantic mutants; final ELF section bytes matched\n",
        observations, sizeof contracts / sizeof contracts[0], high_index_cases,
        unaligned_cases, guard_end_cases, page, sizeof mutants / sizeof mutants[0]);
    free(before);
    if (munmap(mapping, page * 3) || fflush(stdout) || ferror(stdout)) return 2;
    return 0;
}
