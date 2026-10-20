/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

enum { register_count = 16, memory_size = 32, no_index = -1 };
struct snapshot { uint64_t registers[register_count]; uint64_t flags; };
_Static_assert(offsetof(struct snapshot, flags) == 128 && sizeof(struct snapshot) == 136,
    "Assembly snapshot ABI changed");
struct snapshot edsl_moves_input, edsl_moves_output;
uint64_t edsl_moves_effective_flags;
extern void edsl_moves_probe(const unsigned char *);
extern const unsigned char edsl_moves_section_start[], edsl_moves_section_end[];

enum kind { register_copy, register_copy64, register_exchange64, load, store, load64, store64 };
struct contract {
    const char *name;
    const unsigned char *code, *end;
    enum kind kind;
    unsigned int destination, source, base;
    int index;
    unsigned int scale;
};
/* These contracts specify the requested operation independently of its bytes:
 * the C observer contains no opcode, ModRM or SIB decoder. */
#define CONTRACTS(X) \
    X(r89_0, register_copy, 0,1,0,no_index,0) \
    X(r89_1, register_copy, 1,2,0,no_index,0) \
    X(r89_2, register_copy, 2,3,0,no_index,0) \
    X(r89_3, register_copy, 3,4,0,no_index,0) \
    X(r89_4, register_copy, 4,5,0,no_index,0) \
    X(r89_5, register_copy, 5,6,0,no_index,0) \
    X(r89_6, register_copy, 6,7,0,no_index,0) \
    X(r89_7, register_copy, 7,0,0,no_index,0) \
    X(r8b_0, register_copy, 0,7,0,no_index,0) \
    X(r8b_1, register_copy, 1,0,0,no_index,0) \
    X(r8b_2, register_copy, 2,1,0,no_index,0) \
    X(r8b_3, register_copy, 3,2,0,no_index,0) \
    X(r8b_4, register_copy, 4,3,0,no_index,0) \
    X(r8b_5, register_copy, 5,4,0,no_index,0) \
    X(r8b_6, register_copy, 6,5,0,no_index,0) \
    X(r8b_7, register_copy, 7,6,0,no_index,0) \
    X(self_0, register_copy, 0,0,0,no_index,0) \
    X(self_1, register_copy, 1,1,0,no_index,0) \
    X(self_2, register_copy, 2,2,0,no_index,0) \
    X(self_3, register_copy, 3,3,0,no_index,0) \
    X(self_4, register_copy, 4,4,0,no_index,0) \
    X(self_5, register_copy, 5,5,0,no_index,0) \
    X(self_6, register_copy, 6,6,0,no_index,0) \
    X(self_7, register_copy, 7,7,0,no_index,0) \
    X(load_0, load, 0,0,0,no_index,0) \
    X(load_1, load, 1,0,1,no_index,0) \
    X(load_2, load, 2,0,2,no_index,0) \
    X(load_3, load, 3,0,3,no_index,0) \
    X(load_6, load, 6,0,6,no_index,0) \
    X(load_7, load, 7,0,7,no_index,0) \
    X(store_0, store, 0,0,0,no_index,0) \
    X(store_1, store, 0,1,1,no_index,0) \
    X(store_2, store, 0,2,2,no_index,0) \
    X(store_3, store, 0,3,3,no_index,0) \
    X(store_6, store, 0,6,6,no_index,0) \
    X(store_7, store, 0,7,7,no_index,0) \
    X(legacy_load, load, 0,0,7,no_index,0) \
    X(legacy_store, store, 0,6,7,no_index,0) \
    X(sibload_0, load, 1,0,7,1,0) \
    X(sibload_1, load, 1,0,7,1,1) \
    X(sibload_2, load, 1,0,7,1,2) \
    X(sibload_3, load, 1,0,7,1,3) \
    X(sibstore_0, store, 0,7,7,1,0) \
    X(sibstore_1, store, 0,7,7,1,1) \
    X(sibstore_2, store, 0,7,7,1,2) \
    X(sibstore_3, store, 0,7,7,1,3) \
    X(sib_rsp_load, load, 4,0,4,5,1) \
    X(sib_rsp_store, store, 0,5,4,5,1) \
    X(sib_same_load, load, 1,0,1,1,0) \
    X(sib_same_store, store, 0,1,1,1,0) \
    X(q89_0, register_copy64, 0,1,0,no_index,0) \
    X(q89_1, register_copy64, 1,10,0,no_index,0) \
    X(q89_2, register_copy64, 2,3,0,no_index,0) \
    X(q89_3, register_copy64, 3,12,0,no_index,0) \
    X(q89_4, register_copy64, 4,5,0,no_index,0) \
    X(q89_5, register_copy64, 5,14,0,no_index,0) \
    X(q89_6, register_copy64, 6,7,0,no_index,0) \
    X(q89_7, register_copy64, 7,8,0,no_index,0) \
    X(q89_8, register_copy64, 8,9,0,no_index,0) \
    X(q89_9, register_copy64, 9,2,0,no_index,0) \
    X(q89_10, register_copy64, 10,11,0,no_index,0) \
    X(q89_11, register_copy64, 11,4,0,no_index,0) \
    X(q89_12, register_copy64, 12,13,0,no_index,0) \
    X(q89_13, register_copy64, 13,6,0,no_index,0) \
    X(q89_14, register_copy64, 14,15,0,no_index,0) \
    X(q89_15, register_copy64, 15,0,0,no_index,0) \
    X(q8b_0, register_copy64, 0,15,0,no_index,0) \
    X(q8b_1, register_copy64, 1,0,0,no_index,0) \
    X(q8b_2, register_copy64, 2,9,0,no_index,0) \
    X(q8b_3, register_copy64, 3,2,0,no_index,0) \
    X(q8b_4, register_copy64, 4,11,0,no_index,0) \
    X(q8b_5, register_copy64, 5,4,0,no_index,0) \
    X(q8b_6, register_copy64, 6,13,0,no_index,0) \
    X(q8b_7, register_copy64, 7,6,0,no_index,0) \
    X(q8b_8, register_copy64, 8,7,0,no_index,0) \
    X(q8b_9, register_copy64, 9,8,0,no_index,0) \
    X(q8b_10, register_copy64, 10,1,0,no_index,0) \
    X(q8b_11, register_copy64, 11,10,0,no_index,0) \
    X(q8b_12, register_copy64, 12,3,0,no_index,0) \
    X(q8b_13, register_copy64, 13,12,0,no_index,0) \
    X(q8b_14, register_copy64, 14,5,0,no_index,0) \
    X(q8b_15, register_copy64, 15,14,0,no_index,0) \
    X(qself_0, register_copy64, 0,0,0,no_index,0) \
    X(qself_1, register_copy64, 1,1,0,no_index,0) \
    X(qself_2, register_copy64, 2,2,0,no_index,0) \
    X(qself_3, register_copy64, 3,3,0,no_index,0) \
    X(qself_4, register_copy64, 4,4,0,no_index,0) \
    X(qself_5, register_copy64, 5,5,0,no_index,0) \
    X(qself_6, register_copy64, 6,6,0,no_index,0) \
    X(qself_7, register_copy64, 7,7,0,no_index,0) \
    X(qself_8, register_copy64, 8,8,0,no_index,0) \
    X(qself_9, register_copy64, 9,9,0,no_index,0) \
    X(qself_10, register_copy64, 10,10,0,no_index,0) \
    X(qself_11, register_copy64, 11,11,0,no_index,0) \
    X(qself_12, register_copy64, 12,12,0,no_index,0) \
    X(qself_13, register_copy64, 13,13,0,no_index,0) \
    X(qself_14, register_copy64, 14,14,0,no_index,0) \
    X(qself_15, register_copy64, 15,15,0,no_index,0) \
    X(qx89_low, register_copy64, 0,3,0,no_index,0) \
    X(qx89_b, register_copy64, 8,3,0,no_index,0) \
    X(qx89_r, register_copy64, 0,11,0,no_index,0) \
    X(qx89_rb, register_copy64, 8,11,0,no_index,0) \
    X(qx8b_low, register_copy64, 3,0,0,no_index,0) \
    X(qx8b_b, register_copy64, 3,8,0,no_index,0) \
    X(qx8b_r, register_copy64, 11,0,0,no_index,0) \
    X(qx8b_rb, register_copy64, 11,8,0,no_index,0)
#define MUTANTS(X) \
    X(mutant_width, register_copy, 0,3,0,no_index,0) \
    X(mutant_direction, register_copy, 0,3,0,no_index,0) \
    X(mutant_omitted, store, 0,6,7,no_index,0) \
    X(mutant_neighbor, store, 0,6,7,no_index,0) \
    X(mutant_narrow, register_copy64, 0,3,0,no_index,0) \
    X(mutant_exchange_copy, register_exchange64, 0,7,0,no_index,0) \
    X(mutant_exchange_wrong, register_exchange64, 0,7,0,no_index,0) \
    X(mutant_exchange_omitted, register_exchange64, 0,7,0,no_index,0) \
    X(mutant_exchange_narrow, register_exchange64, 0,7,0,no_index,0) \
    X(mutant_exchange_flags, register_exchange64, 0,7,0,no_index,0) \
    X(mutant_load64_narrow, load64, 0,0,7,no_index,0) \
    X(mutant_store64_narrow, store64, 0,6,7,no_index,0) \
    X(mutant_store64_source, store64, 0,6,7,no_index,0) \
    X(mutant_store64_address, store64, 0,6,7,no_index,0) \
    X(mutant_store64_endian, store64, 0,6,7,no_index,0) \
    X(mutant_store64_neighbor, store64, 0,6,7,no_index,0)
/* Independent requested operands; the C oracle does not decode instruction
 * bytes. Every GPR is a load destination and a store source. */
#define MEMORY64_CONTRACTS(X) \
    X(load64_0, load64, 0,0,7,no_index,0) \
    X(load64_1, load64, 1,0,8,no_index,0) \
    X(load64_2, load64, 2,0,1,no_index,0) \
    X(load64_3, load64, 3,0,10,no_index,0) \
    X(load64_4, load64, 4,0,3,no_index,0) \
    X(load64_5, load64, 5,0,14,no_index,0) \
    X(load64_6, load64, 6,0,7,no_index,0) \
    X(load64_7, load64, 7,0,0,no_index,0) \
    X(load64_8, load64, 8,0,9,no_index,0) \
    X(load64_9, load64, 9,0,2,no_index,0) \
    X(load64_10, load64, 10,0,11,no_index,0) \
    X(load64_11, load64, 11,0,6,no_index,0) \
    X(load64_12, load64, 12,0,15,no_index,0) \
    X(load64_13, load64, 13,0,0,no_index,0) \
    X(load64_14, load64, 14,0,1,no_index,0) \
    X(load64_15, load64, 15,0,8,no_index,0) \
    X(store64_0, store64, 0,0,0,no_index,0) \
    X(store64_1, store64, 0,1,1,no_index,0) \
    X(store64_2, store64, 0,2,2,no_index,0) \
    X(store64_3, store64, 0,3,3,no_index,0) \
    X(store64_4, store64, 0,4,6,no_index,0) \
    X(store64_5, store64, 0,5,7,no_index,0) \
    X(store64_6, store64, 0,6,6,no_index,0) \
    X(store64_7, store64, 0,7,7,no_index,0) \
    X(store64_8, store64, 0,8,8,no_index,0) \
    X(store64_9, store64, 0,9,9,no_index,0) \
    X(store64_10, store64, 0,10,10,no_index,0) \
    X(store64_11, store64, 0,11,11,no_index,0) \
    X(store64_12, store64, 0,12,14,no_index,0) \
    X(store64_13, store64, 0,13,15,no_index,0) \
    X(store64_14, store64, 0,14,14,no_index,0) \
    X(store64_15, store64, 0,15,15,no_index,0) \
    X(load64_x0, load64, 0,0,7,no_index,0) \
    X(load64_x1, load64, 0,0,15,no_index,0) \
    X(load64_x2, load64, 8,0,7,no_index,0) \
    X(load64_x3, load64, 8,0,15,no_index,0) \
    X(store64_x0, store64, 0,6,7,no_index,0) \
    X(store64_x1, store64, 0,6,15,no_index,0) \
    X(store64_x2, store64, 0,14,7,no_index,0) \
    X(store64_x3, store64, 0,14,15,no_index,0) \
    X(load64_scale0, load64, 10,0,8,9,0) \
    X(load64_scale1, load64, 10,0,8,9,1) \
    X(load64_scale2, load64, 10,0,8,9,2) \
    X(load64_scale3, load64, 10,0,8,9,3) \
    X(store64_scale0, store64, 0,11,8,9,0) \
    X(store64_scale1, store64, 0,11,8,9,1) \
    X(store64_scale2, store64, 0,11,8,9,2) \
    X(store64_scale3, store64, 0,11,8,9,3) \
    X(load64_alias_base, load64, 8,0,8,9,0) \
    X(load64_alias_index, load64, 9,0,8,9,0) \
    X(store64_alias_base, store64, 0,8,8,9,0) \
    X(store64_alias_index, store64, 0,9,8,9,0) \
    X(load64_r12_index, load64, 12,0,4,12,1) \
    X(store64_r12_index, store64, 0,13,4,12,1) \
    X(load64_r12_base, load64, 4,0,12,13,0) \
    X(store64_r12_base, store64, 0,5,12,13,0) \
    X(load64_same_address, load64, 9,0,9,9,0) \
    X(store64_same_address, store64, 0,9,9,9,0)
/* Requested Cartesian register pairs. These macros name mathematical swap
 * contracts; the independent assembler windows supply the bytes. */
#define EXCHANGE_PAIR(X,left,right) \
    X(exchange_##left##_##right, register_exchange64, left,right,0,no_index,0)
#define EXCHANGE_ROW(X,left) \
    EXCHANGE_PAIR(X,left,0) EXCHANGE_PAIR(X,left,1) \
    EXCHANGE_PAIR(X,left,2) EXCHANGE_PAIR(X,left,3) \
    EXCHANGE_PAIR(X,left,4) EXCHANGE_PAIR(X,left,5) \
    EXCHANGE_PAIR(X,left,6) EXCHANGE_PAIR(X,left,7) \
    EXCHANGE_PAIR(X,left,8) EXCHANGE_PAIR(X,left,9) \
    EXCHANGE_PAIR(X,left,10) EXCHANGE_PAIR(X,left,11) \
    EXCHANGE_PAIR(X,left,12) EXCHANGE_PAIR(X,left,13) \
    EXCHANGE_PAIR(X,left,14) EXCHANGE_PAIR(X,left,15)
#define SHORT_PAIR(X,other) \
    X(short_##other##_0, register_exchange64, 0,other,0,no_index,0) \
    X(short_##other##_1, register_exchange64, 0,other,0,no_index,0) \
    X(short_##other##_2, register_exchange64, 0,other,0,no_index,0) \
    X(short_##other##_3, register_exchange64, 0,other,0,no_index,0)
#define EXCHANGE_CONTRACTS(X) \
    EXCHANGE_ROW(X,0) EXCHANGE_ROW(X,1) EXCHANGE_ROW(X,2) EXCHANGE_ROW(X,3) \
    EXCHANGE_ROW(X,4) EXCHANGE_ROW(X,5) EXCHANGE_ROW(X,6) EXCHANGE_ROW(X,7) \
    EXCHANGE_ROW(X,8) EXCHANGE_ROW(X,9) EXCHANGE_ROW(X,10) EXCHANGE_ROW(X,11) \
    EXCHANGE_ROW(X,12) EXCHANGE_ROW(X,13) EXCHANGE_ROW(X,14) EXCHANGE_ROW(X,15) \
    SHORT_PAIR(X,0) SHORT_PAIR(X,1) SHORT_PAIR(X,2) SHORT_PAIR(X,3) \
    SHORT_PAIR(X,4) SHORT_PAIR(X,5) SHORT_PAIR(X,6) SHORT_PAIR(X,7) \
    SHORT_PAIR(X,8) SHORT_PAIR(X,9) SHORT_PAIR(X,10) SHORT_PAIR(X,11) \
    SHORT_PAIR(X,12) SHORT_PAIR(X,13) SHORT_PAIR(X,14) SHORT_PAIR(X,15) \
    X(exchange_x_0, register_exchange64, 3,1,0,no_index,0) \
    X(exchange_x_1, register_exchange64, 3,9,0,no_index,0) \
    X(exchange_x_2, register_exchange64, 11,1,0,no_index,0) \
    X(exchange_x_3, register_exchange64, 11,9,0,no_index,0)
#define DECLARE(name,k,d,s,b,i,c) \
    extern const unsigned char edsl_move_##name[], edsl_move_##name##_end[];
CONTRACTS(DECLARE)
EXCHANGE_CONTRACTS(DECLARE)
MEMORY64_CONTRACTS(DECLARE)
MUTANTS(DECLARE)
#define ENTRY(name,k,d,s,b,i,c) \
    {#name,edsl_move_##name,edsl_move_##name##_end,k,d,s,b,i,c},
static const struct contract contracts[] = {
    CONTRACTS(ENTRY) EXCHANGE_CONTRACTS(ENTRY) MEMORY64_CONTRACTS(ENTRY)
};
static const struct contract mutants[] = { MUTANTS(ENTRY) };

static void print_words(const uint64_t *values, size_t count)
{
    putchar('[');
    for (size_t i = 0; i < count; ++i) printf("%s%" PRIu64, i ? "," : "", values[i]);
    putchar(']');
}
static void print_bytes(const unsigned char *values, size_t count, int options)
{
    putchar('[');
    for (size_t i = 0; i < count; ++i)
        printf("%s%s%u", i ? "," : "", options ? "some " : "", (unsigned int)values[i]);
    putchar(']');
}

static int run_case(const struct contract *contract, unsigned char *memory,
    size_t offset, unsigned int vector, int emit)
{
    unsigned char before[memory_size], expected_memory[memory_size];
    for (unsigned int i = 0; i < memory_size; ++i)
        before[i] = (unsigned char)(0x81u + i * 37u + vector * 29u);
    memcpy(memory, before, memory_size);
    memcpy(expected_memory, before, memory_size);
    for (unsigned int i = 0; i < register_count; ++i)
        edsl_moves_input.registers[i] = UINT64_C(0xabc1000000000000) +
            (uint64_t)(i + 1) * UINT64_C(0x0101000020304051) + vector * UINT64_C(0x1122334455667788);
    static const uint64_t flags[] = { 0x202, 0xad7 };
    edsl_moves_input.flags = flags[vector];
    uint64_t address = (uint64_t)(uintptr_t)(memory + offset);
    unsigned int width = contract->kind == load64 || contract->kind == store64 ? 8 : 4;
    if (contract->kind == load || contract->kind == store ||
        contract->kind == load64 || contract->kind == store64) {
        if (contract->index == no_index) {
            edsl_moves_input.registers[contract->base] = address;
        } else if ((unsigned int)contract->index == contract->base) {
            if (address % 2 != 0 || contract->scale != 0) return -1;
            edsl_moves_input.registers[contract->base] = address / 2;
        } else {
            uint64_t index = UINT64_C(0x100000003) + vector;
            edsl_moves_input.registers[contract->index] = index;
            edsl_moves_input.registers[contract->base] = address - index * (UINT64_C(1) << contract->scale);
        }
        uint64_t evaluated = edsl_moves_input.registers[contract->base];
        if (contract->index != no_index)
            evaluated += edsl_moves_input.registers[contract->index] * (UINT64_C(1) << contract->scale);
        if (evaluated != address || edsl_moves_input.registers[contract->base] <= UINT32_MAX ||
            (contract->index != no_index && edsl_moves_input.registers[contract->index] <= UINT32_MAX))
            return -1;
    }
    struct snapshot expected = edsl_moves_input;
    if (contract->kind == register_copy) {
        expected.registers[contract->destination] = (uint32_t)edsl_moves_input.registers[contract->source];
    } else if (contract->kind == register_copy64) {
        expected.registers[contract->destination] = edsl_moves_input.registers[contract->source];
    } else if (contract->kind == register_exchange64) {
        /* Both values come from the untouched input snapshot, including
         * aliases. Reusing the first updated value would lose half the swap. */
        expected.registers[contract->destination] = edsl_moves_input.registers[contract->source];
        expected.registers[contract->source] = edsl_moves_input.registers[contract->destination];
    } else if (contract->kind == load || contract->kind == load64) {
        uint64_t value = 0;
        for (unsigned int i = 0; i < width; ++i)
            value += (uint64_t)before[offset + i] * (UINT64_C(1) << (8 * i));
        expected.registers[contract->destination] = value;
    } else {
        uint64_t value = edsl_moves_input.registers[contract->source];
        for (unsigned int i = 0; i < width; ++i)
            expected_memory[offset + i] = (unsigned char)(value >> (8 * i));
    }
    edsl_moves_probe(contract->code);
    expected.flags = edsl_moves_effective_flags;
    int matches = memcmp(expected.registers, edsl_moves_output.registers, sizeof expected.registers) == 0 &&
        expected.flags == edsl_moves_output.flags && memcmp(memory, expected_memory, memory_size) == 0;
    if (!matches || !emit) return matches;

    size_t length = (size_t)((uintptr_t)contract->end - (uintptr_t)contract->code);
    printf("-- Native case %s, flags vector %u, target offset %zu.\n", contract->name, vector, offset);
    printf("theorem observed_%s_%u_%zu (af : Bool) : observe af (entry ",
        contract->name, vector, offset);
    print_bytes(contract->code, length, 0);
    printf(" %" PRIuPTR " ", (uintptr_t)contract->code);
    print_words(edsl_moves_input.registers, register_count);
    printf(" %" PRIu64 " %" PRIuPTR " ", edsl_moves_effective_flags, (uintptr_t)memory);
    print_bytes(before, memory_size, 0);
    printf(") %" PRIuPTR " = some (", (uintptr_t)memory);
    print_words(edsl_moves_output.registers, register_count);
    printf(",%" PRIu64 ",%" PRIuPTR ",", edsl_moves_output.flags, (uintptr_t)contract->end);
    print_bytes(memory, memory_size, 1);
    if (contract->kind == load || contract->kind == load64)
        printf(",[⟨.data,%" PRIu64 ",%u⟩]) := by cases af <;> rfl\n", address, width);
    else puts(",[]) := by cases af <;> rfl");
    return 1;
}

int main(int argc, char **argv)
{
    if (argc != 2) return 2;
    FILE *file = fopen(argv[1], "rb");
    if (!file) return 2;
    size_t section_size = (size_t)((uintptr_t)edsl_moves_section_end - (uintptr_t)edsl_moves_section_start);
    unsigned char *file_bytes = malloc(section_size + 1);
    if (!file_bytes) return 2;
    size_t file_size = fread(file_bytes, 1, section_size + 1, file);
    int failed = ferror(file);
    fclose(file);
    if (failed || file_size != section_size ||
        memcmp(file_bytes, edsl_moves_section_start, section_size) != 0) {
        fputs("Final ELF section extraction differs from executed bytes\n", stderr);
        return 2;
    }
    free(file_bytes);
    long page = sysconf(_SC_PAGESIZE);
    if (page < memory_size * 2) return 2;
    unsigned char *mapping = mmap(NULL, (size_t)page * 3, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED || mprotect(mapping + page, (size_t)page, PROT_READ | PROT_WRITE)) return 2;
    unsigned char *memory = mapping + page;
    if ((uintptr_t)memory <= UINT32_MAX) return 2;
    puts("/- Native observations of owned MOV32/MOV64 register/memory and XCHG64 register\n"
         "windows; finite conformance evidence for two captured flags profiles.\n"
         "The C mathematical observer independently checked full GPRs, flags and\n"
         "all 32 data bytes. RIP is the extracted instruction end label; the read\n"
         "footprint is the independent requested contract, not a CPU trace. -/\n"
         "import EDSL.X86.Sequential.Machine\nimport EDSL.Audit\n"
         "namespace EDSL.Tests.NativeSequentialMoves\nopen EDSL.X86\n"
         "def allRegisters : List Register := [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,"
         ".r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]\n"
         "def entry (code : List Byte) (pc : Word) (registers : List Word)\n"
         "    (flags dataBase : Word) (bytes : List Byte) : State where\n"
         "  registers r := registers.getD (allRegisters.idxOf r) 0\n"
         "  rip := pc\n  flags := flags\n"
         "  memory := {\n"
         "    read := fun a => if pc.toNat ≤ a.toNat ∧ a.toNat < pc.toNat + code.length\n"
         "      then code[a.toNat - pc.toNat]?\n"
         "      else if dataBase.toNat ≤ a.toNat ∧ a.toNat < dataBase.toNat + bytes.length\n"
         "      then bytes[a.toNat - dataBase.toNat]? else none\n"
         "    executable := fun a => decide (pc.toNat ≤ a.toNat ∧ a.toNat < pc.toNat + code.length)\n"
         "    writable := fun a => decide (dataBase.toNat ≤ a.toNat ∧ a.toNat < dataBase.toNat + bytes.length) }\n"
         "def observe (af : Bool) (initial : State) (dataBase : Word) :\n"
         "    Option (List Word × Word × Word × List (Option Byte) × List Sequential.Read) := do\n"
         "  let observation ← (Sequential.step af initial).toOption\n"
         "  match observation.result with\n"
         "  | .next final => return (allRegisters.map final.registers,final.flags,final.rip,\n"
         "      (List.range 32).map (fun i => final.memory.read (dataBase + BitVec.ofNat 64 i)),observation.reads)\n"
         "  | _ => none");
    unsigned int observations32 = 0, observations64 = 0, exchanges64 = 0, memory64 = 0;
    for (size_t i = 0; i < sizeof contracts / sizeof contracts[0]; ++i) {
        for (unsigned int vector = 0; vector < 2; ++vector) {
            /* Even offsets also permit the base=index alias. The offset 28
             * cases exercise the last four observed bytes without risking an
             * actual hardware fault for the separate eight-byte mutant. */
            size_t width = contracts[i].kind == load64 || contracts[i].kind == store64 ? 8 : 4;
            const size_t offsets[] = { 2, memory_size - width };
            unsigned int offset_count = contracts[i].kind == load || contracts[i].kind == store ||
                contracts[i].kind == load64 || contracts[i].kind == store64 ? 2 : 1;
            for (unsigned int j = 0; j < offset_count; ++j) {
                if (run_case(&contracts[i], memory, offsets[j], vector, 1) != 1) {
                    fprintf(stderr, "Independent native contract failed: %s/%u/%zu\n", contracts[i].name, vector, offsets[j]);
                    return 1;
                }
                if (contracts[i].kind == register_copy64) ++observations64;
                else if (contracts[i].kind == register_exchange64) ++exchanges64;
                else if (contracts[i].kind == load64 || contracts[i].kind == store64) ++memory64;
                else ++observations32;
            }
        }
    }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        if (run_case(&mutants[i], memory, 2, 0, 0) != 0) {
            fprintf(stderr, "Independent observer failed to reject owned mutant: %s\n", mutants[i].name);
            return 1;
        }
    }
    puts("end EDSL.Tests.NativeSequentialMoves\n#audit_edsl");
    fprintf(stderr, "Checked %u native observations (%u MOV32 register/memory, %u MOV64 register, "
        "%u XCHG64 register, %u MOV64 memory); "
        "rejected %zu owned semantic mutants; final ELF bytes matched\n",
        observations32 + observations64 + exchanges64 + memory64,
        observations32, observations64, exchanges64, memory64,
        sizeof mutants / sizeof mutants[0]);
    if (munmap(mapping, (size_t)page * 3)) return 2;
    return 0;
}
