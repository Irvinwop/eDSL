/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

/* Linux x86-64 finite CPU observations, not an ISA proof or a flags formula.
 * Build using GNU23 (-std=gnu2x on GCC 13), -O2 -Wall -Wextra -Werror
 * -Wpedantic -mno-red-zone. PUSHFQ uses the stack; every probe restores DF
 * with CLD before returning to C. Only ordinary RAM and user-visible RFLAGS
 * are observed. Signal interference, MMIO and privileged flags are outside
 * this fixture's scope.
 *
 * Stream v1 (all integers little endian): 8-byte "SSNAT01\n", then six u32:
 * version=1, CMP8 count=131072, CMP32 count=1024, MOV count=56, record size=31,
 * reserved=0. CMP records: linked code[3], before RFLAGS:u64, after RFLAGS:u64,
 * after RDX:u64, after memory operand:u32 (zero-padded for CMP8).
 * MOV records: linked code[7], before RFLAGS:u64, after RFLAGS:u64, result:u64.
 * CMP8 order: encoding (GCC, Clang), left byte, right byte. CMP32 order:
 * encoding, variant, left corner index, right corner index. MOV order:
 * destination (RAX, R8), immediate index, incoming flag pattern index.
 * No pointer values, environmental metadata or real findings are emitted.
 * The Lean consumer fixes this schema, order, counts and exact encodings.
 */

enum { CMP8_COUNT = 2 * 256 * 256, CMP32_COUNT = 2 * 2 * 16 * 16,
       MOV_COUNT = 2 * 7 * 4, RECORD_SIZE = 31 };

static const uint32_t corners32[16] = {
    0, 1, 0xf, 0x10, 0x7f, 0x80, 0xff, 0x100,
    0xffff, 0x10000, 0x1000000, 0x7fffffff,
    0x80000000, 0x80000001, 0xfffffffe, 0xffffffff
};
static const uint32_t immediates[7] = {
    0, 1, 0x80, 0xffff, 0x7fffffff, 0x80000000, 0xffffffff
};
static const uint64_t flag_patterns[4] = { 0, 0x8d5, 0x891, 0x44 };

struct compare_sample {
    const uint8_t *code;
    uint64_t before, after, source;
};
struct move_sample {
    const uint8_t *code;
    uint64_t before, after, value;
};

static void fail(const char *message)
{
    fputs(message, stderr);
    fputc('\n', stderr);
    exit(1);
}

/* These bytes are the frozen compiler forms. Address registers deliberately
 * exceed 4 GiB even on the host. Arithmetic used to set up the address occurs
 * before POPFQ, so the before/after snapshots bracket only the instruction.
 * The + constraints capture the real post-instruction address/source GPRs. */
#define DEFINE_COMPARE(NAME, OPCODE, SIB, INDEX_CONSTRAINT) \
static __attribute__((noinline)) struct compare_sample NAME( \
    uintptr_t address, uint64_t index, uint64_t source, uint64_t seed, \
    unsigned int scale) \
{ \
    uintptr_t base = address - (index << scale); \
    const uintptr_t original_base = base; \
    const uint64_t original_index = index, original_source = source; \
    struct compare_sample sample; \
    __asm__ volatile( \
        "leaq 1f(%%rip), %[code]\n\t" \
        "pushq %[seed]\n\tpopfq\n\tstd\n\t" \
        "pushfq\n\tpopq %[before]\n\t" \
        "1: .byte " OPCODE ", 0x14, " SIB "\n\t" \
        "pushfq\n\tpopq %[after]\n\tcld" \
        : [code] "=&r" (sample.code), [before] "=&r" (sample.before), \
          [after] "=&r" (sample.after), "+D" (base), \
          "+" INDEX_CONSTRAINT (index), "+d" (source) \
        : [seed] "r" (seed) : "cc", "memory"); \
    if (base != original_base || index != original_index || source != original_source) \
        fail("CMP changed an address/source register"); \
    if (((sample.before ^ sample.after) & ~UINT64_C(0x8d5)) != 0 || \
        (sample.before & UINT64_C(0x400)) == 0) \
        fail("CMP changed nonarithmetic flags or failed to capture set DF"); \
    sample.source = source; \
    return sample; \
}

DEFINE_COMPARE(cmp8_gcc, "0x38", "0x07", "a")
DEFINE_COMPARE(cmp8_clang, "0x38", "0x0f", "c")
DEFINE_COMPARE(cmp32_gcc, "0x39", "0x87", "a")
DEFINE_COMPARE(cmp32_clang, "0x39", "0x8f", "c")
#undef DEFINE_COMPARE

/* C7 must be encoded literally: an assembler may choose B8 imm64 instead.
 * R8 additionally exercises the REX.B destination bank. The immediate is an
 * assembly constant, not a generated/executable data buffer. */
static __attribute__((noinline)) struct move_sample move(unsigned int destination,
    unsigned int immediate, uint64_t seed)
{
    struct move_sample sample;
    uint64_t value = UINT64_C(0x123456789abcdef0);
    register uint64_t extended __asm__("r8") = value;
#define MOV_CASE(N, B0, B1, B2, B3) case N: \
    if (destination == 0) { \
        __asm__ volatile("leaq 1f(%%rip), %[code]\n\t" \
            "pushq %[seed]\n\tpopfq\n\tstd\n\tpushfq\n\tpopq %[before]\n\t" \
            "1: .byte 0x48,0xc7,0xc0," B0 "," B1 "," B2 "," B3 "\n\t" \
            "pushfq\n\tpopq %[after]\n\tcld" \
            : [code] "=&r" (sample.code), [before] "=&r" (sample.before), \
              [after] "=&r" (sample.after), "+a" (value) \
            : [seed] "r" (seed) : "cc", "memory"); \
    } else { \
        __asm__ volatile("leaq 1f(%%rip), %[code]\n\t" \
            "pushq %[seed]\n\tpopfq\n\tstd\n\tpushfq\n\tpopq %[before]\n\t" \
            "1: .byte 0x49,0xc7,0xc0," B0 "," B1 "," B2 "," B3 "\n\t" \
            "pushfq\n\tpopq %[after]\n\tcld" \
            : [code] "=&r" (sample.code), [before] "=&r" (sample.before), \
              [after] "=&r" (sample.after), "+r" (extended) \
            : [seed] "r" (seed) : "cc", "memory"); \
        value = extended; \
    } \
    break;
    switch (immediate) {
    MOV_CASE(0, "0x00", "0x00", "0x00", "0x00")
    MOV_CASE(1, "0x01", "0x00", "0x00", "0x00")
    MOV_CASE(2, "0x80", "0x00", "0x00", "0x00")
    MOV_CASE(3, "0xff", "0xff", "0x00", "0x00")
    MOV_CASE(4, "0xff", "0xff", "0xff", "0x7f")
    MOV_CASE(5, "0x00", "0x00", "0x00", "0x80")
    MOV_CASE(6, "0xff", "0xff", "0xff", "0xff")
    default: abort();
    }
#undef MOV_CASE
    if (sample.before != sample.after || (sample.before & UINT64_C(0x400)) == 0)
        fail("MOV changed flags or failed to capture set DF");
    sample.value = value;
    return sample;
}

static void bytes(FILE *output, const uint8_t *data, size_t length)
{
    if (fwrite(data, 1, length, output) != length) { perror("write"); exit(2); }
}

static void integer(FILE *output, uint64_t value, unsigned int width)
{
    for (unsigned int i = 0; i < width; ++i)
        if (fputc((int)((value >> (8 * i)) & 255), output) == EOF) {
            perror("write"); exit(2);
        }
}

static void emit_compare(FILE *output, struct compare_sample sample, uint32_t memory)
{
    bytes(output, sample.code, 3);
    integer(output, sample.before, 8);
    integer(output, sample.after, 8);
    integer(output, sample.source, 8);
    integer(output, memory, 4);
}

static void protect(uint8_t *mapping, size_t length, int permission)
{
    if (mprotect(mapping, length, permission) != 0) { perror("mprotect"); exit(2); }
}

int main(int argc, char **argv)
{
    if (argc != 2) { fprintf(stderr, "usage: %s CAPTURE.bin\n", argv[0]); return 2; }
    long page = sysconf(_SC_PAGESIZE);
    if (page < 8) return 2;
    uint8_t *mapping = mmap(NULL, (size_t)page * 2, PROT_NONE,
        MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED) { perror("mmap"); return 2; }
    FILE *output = fopen(argv[1], "wb");
    if (output == NULL) { perror("fopen"); return 2; }
    bytes(output, (const uint8_t *)"SSNAT01\n", 8);
    const uint32_t header[] = { 1, CMP8_COUNT, CMP32_COUNT, MOV_COUNT, RECORD_SIZE, 0 };
    for (size_t i = 0; i < sizeof header / sizeof *header; ++i) integer(output, header[i], 4);

    uint8_t *byte = mapping + page - 1;
    for (unsigned int encoding = 0; encoding < 2; ++encoding)
        for (unsigned int left = 0; left < 256; ++left) {
            protect(mapping, (size_t)page, PROT_READ | PROT_WRITE);
            *byte = (uint8_t)left;
            protect(mapping, (size_t)page, PROT_READ);
            for (unsigned int right = 0; right < 256; ++right) {
                uint64_t source = UINT64_C(0xa5c3d2e1b7f90000) | right;
                uint64_t seed = UINT64_C(0x602) | flag_patterns[(left + right) % 4];
                struct compare_sample sample = encoding == 0
                    ? cmp8_gcc((uintptr_t)byte, UINT64_C(0x100000003), source, seed, 0)
                    : cmp8_clang((uintptr_t)byte, UINT64_C(0x100000003), source, seed, 0);
                if (*byte != left) fail("CMP8 changed read-only data");
                emit_compare(output, sample, *byte);
            }
        }

    for (unsigned int encoding = 0; encoding < 2; ++encoding)
        for (unsigned int variant = 0; variant < 2; ++variant)
            for (unsigned int li = 0; li < 16; ++li)
                for (unsigned int ri = 0; ri < 16; ++ri) {
                    /* variant 0 ends exactly at the guard; variant 1 is unaligned. */
                    uint8_t *operand = mapping + page - 4 - variant;
                    uint32_t left = corners32[li], right = corners32[ri];
                    protect(mapping, (size_t)page, PROT_READ | PROT_WRITE);
                    for (unsigned int i = 0; i < 4; ++i) operand[i] = (uint8_t)(left >> (8 * i));
                    protect(mapping, (size_t)page, PROT_READ);
                    uint64_t high = variant == 0 ? UINT64_C(0xa5c3d2e100000000) : 0;
                    uint64_t source = high | right;
                    uint64_t index = variant == 0 ? UINT64_C(0x100000003) : UINT64_C(0x300000005);
                    uint64_t seed = UINT64_C(0x602) | flag_patterns[(li + ri + variant) % 4];
                    struct compare_sample sample = encoding == 0
                        ? cmp32_gcc((uintptr_t)operand, index, source, seed, 2)
                        : cmp32_clang((uintptr_t)operand, index, source, seed, 2);
                    uint32_t observed = 0;
                    for (unsigned int i = 0; i < 4; ++i) observed |= (uint32_t)operand[i] << (8 * i);
                    if (observed != left) fail("CMP32 changed read-only data");
                    emit_compare(output, sample, observed);
                }

    for (unsigned int destination = 0; destination < 2; ++destination)
        for (unsigned int immediate = 0; immediate < sizeof immediates / sizeof *immediates; ++immediate)
            for (unsigned int pattern = 0; pattern < 4; ++pattern) {
                struct move_sample sample = move(destination, immediate,
                    UINT64_C(0x602) | flag_patterns[pattern]);
                bytes(output, sample.code, 7);
                integer(output, sample.before, 8);
                integer(output, sample.after, 8);
                integer(output, sample.value, 8);
            }
    if (fclose(output) != 0) { perror("fclose"); return 2; }
    if (munmap(mapping, (size_t)page * 2) != 0) { perror("munmap"); return 2; }
    puts("131072 CMP8 + 1024 CMP32 + 56 C7 native records; guard/RO/GPR/flags/DF checks passed");
    return 0;
}
