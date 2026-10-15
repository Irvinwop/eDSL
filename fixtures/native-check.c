/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

/* Execute only the owned fixture after its Lean certificate passes. Boundary
   outcomes are independently specified constants, not a copy of the function. */
int main(int argc, char **argv)
{
    if (argc != 2)
        return 2;
    FILE *file = fopen(argv[1], "rb");
    if (!file)
        return 2;
    unsigned char bytes[16];
    size_t size = fread(bytes, 1, sizeof bytes, file);
    int extra = fgetc(file);
    int failed = ferror(file);
    fclose(file);
    if (failed || size != 4 || extra != EOF)
        return 2;
    long page_size = sysconf(_SC_PAGESIZE);
    if (page_size <= 0)
        return 2;
    void *mapping = mmap(NULL, (size_t)page_size, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED)
        return 2;
    memcpy(mapping, bytes, size);
    if (mprotect(mapping, (size_t)page_size, PROT_READ | PROT_EXEC) != 0) {
        munmap(mapping, (size_t)page_size);
        return 2;
    }
    uint32_t (*function)(uint32_t) = (uint32_t (*)(uint32_t))mapping;
    static const struct { uint32_t input, output; } cases[] = {
        {0x00000000u, 0x00000001u},
        {0x7fffffffu, 0x80000000u},
        {0xfffffffeu, 0xffffffffu},
        {0xffffffffu, 0x00000000u},
    };
    int result = 0;
    for (size_t i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
        if (function(cases[i].input) != cases[i].output) {
            fprintf(stderr, "native boundary mismatch at input 0x%08x\n", cases[i].input);
            result = 1;
            break;
        }
    }
    if (munmap(mapping, (size_t)page_size) != 0)
        return 2;
    return result;
}
