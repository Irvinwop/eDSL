/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

/* Each case executes an actual memory/immediate CMP8. Build with
 * -mno-red-zone because the inline probe uses PUSHFQ. DF is set only within
 * the asm and cleared before returning to C. The before/after captures check
 * every nonarithmetic flag that user mode exposes, including set DF. */
struct sample { uint64_t flags; const uint8_t *code; };

static struct sample compare(const uint8_t *byte, unsigned int immediate)
{
    uint64_t before = 0, after = 0;
    const uint8_t *code = NULL;
#define CASE(N) case (N): \
    __asm__ volatile("leaq 1f(%%rip), %[code]\n\tstd\n\tpushfq\n\tpopq %[before]\n\t" \
        "1: cmpb %[immediate], (%%rbx)\n\tpushfq\n\tpopq %[after]\n\tcld" \
        : [code] "=&r" (code), [before] "=&r" (before), [after] "=&r" (after) \
        : [base] "b" (byte), [byte] "m" (*byte), [immediate] "i" (N) : "cc"); break;
#define ROW(N) CASE(N) CASE(N+1) CASE(N+2) CASE(N+3) \
    CASE(N+4) CASE(N+5) CASE(N+6) CASE(N+7) \
    CASE(N+8) CASE(N+9) CASE(N+10) CASE(N+11) \
    CASE(N+12) CASE(N+13) CASE(N+14) CASE(N+15)
    switch (immediate) {
    ROW(0) ROW(16) ROW(32) ROW(48) ROW(64) ROW(80) ROW(96) ROW(112)
    ROW(128) ROW(144) ROW(160) ROW(176) ROW(192) ROW(208) ROW(224) ROW(240)
    default: abort();
    }
#undef ROW
#undef CASE
    if (((before ^ after) & ~UINT64_C(0x8d5)) != 0) {
        fprintf(stderr, "nonarithmetic flags changed: %" PRIx64 " -> %" PRIx64 "\n", before, after);
        exit(1);
    }
    return (struct sample){after & UINT64_C(0x8d5), code};
}

static int check_nop9(void)
{
    uint64_t apparent_address = UINT64_C(0x800000000000), before, after;
    __asm__ volatile("std\n\tpushfq\n\tpopq %[before]\n\t"
        ".byte 0x66,0x0f,0x1f,0x84,0,0,0,0,0\n\t"
        "pushfq\n\tpopq %[after]\n\tcld"
        : "+a" (apparent_address), [before] "=&r" (before), [after] "=&r" (after) : : "cc");
    return apparent_address == UINT64_C(0x800000000000) && before == after;
}

/* The native oracle is the CPU, not a duplicate flags formula. Its data byte
 * is read-only at the end of a page; writing or reading wider must fault.
 * The binary stream is left-major, right-minor: three bytes read from the
 * actual linked CMP instruction followed by two little-endian flag bytes.
 * tests/SequentialByteNative.lean compares it with public Sequential.step. */
int main(int argc, char **argv)
{
    if (argc != 2) {
        fprintf(stderr, "usage: %s FLAGS.bin\n", argv[0]);
        return 2;
    }
    if (!check_nop9()) { fputs("NOP9 changed RAX/flags\n", stderr); return 1; }
    long page = sysconf(_SC_PAGESIZE);
    if (page <= 0) return 2;
    uint8_t *mapping = mmap(NULL, (size_t)page * 2, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED) { perror("mmap"); return 2; }
    uint8_t *byte = mapping + page - 1;
    FILE *output = fopen(argv[1], "wb");
    if (!output) { perror("fopen"); return 2; }
    for (unsigned int left = 0; left < 256; ++left) {
        if (mprotect(mapping, (size_t)page, PROT_READ | PROT_WRITE) != 0) { perror("mprotect"); return 2; }
        *byte = (uint8_t)left;
        if (mprotect(mapping, (size_t)page, PROT_READ) != 0) { perror("mprotect"); return 2; }
        for (unsigned int right = 0; right < 256; ++right) {
            struct sample sample = compare(byte, right);
            if (*byte != left) { fputs("CMP changed operand\n", stderr); return 1; }
            if (fwrite(sample.code, 1, 3, output) != 3 ||
                fputc((int)(sample.flags & 255), output) == EOF ||
                fputc((int)(sample.flags >> 8), output) == EOF) { perror("write"); return 2; }
        }
    }
    if (fclose(output) != 0) { perror("fclose"); return 2; }
    if (munmap(mapping, (size_t)page * 2) != 0) { perror("munmap"); return 2; }
    puts("65536 actual CMP8 memory/immediate pairs, read-only guard boundary and nonarithmetic flags passed");
    return 0;
}
