/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

/* Execute only owned fixtures after their Lean certificates pass. */
static int check_increment(void *mapping)
{
    uint32_t (*function)(uint32_t) = (uint32_t (*)(uint32_t))mapping;
    static const struct { uint32_t input, output; } cases[] = {
        {0x00000000u, 0x00000001u},
        {0x7fffffffu, 0x80000000u},
        {0xfffffffeu, 0xffffffffu},
        {0xffffffffu, 0x00000000u},
    };
    for (size_t i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
        if (function(cases[i].input) != cases[i].output) {
            fprintf(stderr, "native increment mismatch at input 0x%08x\n", cases[i].input);
            return 1;
        }
    }
    return 0;
}

static int check_memory(void *mapping, int store, size_t page_size)
{
    unsigned char *data = mmap(NULL, page_size, PROT_READ | PROT_WRITE,
                               MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (data == MAP_FAILED)
        return 2;
    static const struct { uint32_t word; unsigned char bytes[4]; } cases[] = {
        {0x11223344u, {0x44, 0x33, 0x22, 0x11}},
        {0x89abcdefu, {0xef, 0xcd, 0xab, 0x89}},
        {0x00000000u, {0x00, 0x00, 0x00, 0x00}},
        {0xffffffffu, {0xff, 0xff, 0xff, 0xff}},
    };
    uint32_t (*load_function)(const uint32_t *) =
        (uint32_t (*)(const uint32_t *))mapping;
    void (*store_function)(uint32_t *, uint32_t) =
        (void (*)(uint32_t *, uint32_t))mapping;
    int result = 0;
    for (size_t i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
        if (mprotect(data, page_size, PROT_READ | PROT_WRITE) != 0) {
            result = 2;
            break;
        }
        memset(data, 0xa5, 16);
        if (store) {
            store_function((uint32_t *)(data + 8), cases[i].word);
        } else {
            memcpy(data + 8, cases[i].bytes, 4);
            if (mprotect(data, page_size, PROT_READ) != 0) {
                result = 2;
                break;
            }
            if (load_function((const uint32_t *)(data + 8)) != cases[i].word) {
                fprintf(stderr, "native load byte-order/value mismatch\n");
                result = 1;
                break;
            }
        }
        for (size_t byte = 0; byte < 16; ++byte) {
            unsigned char expected = byte >= 8 && byte < 12 ? cases[i].bytes[byte - 8] : 0xa5;
            if (data[byte] != expected) {
                fprintf(stderr, "native %s memory footprint mismatch at byte %zu\n",
                        store ? "store" : "load", byte);
                result = 1;
                break;
            }
        }
        if (result != 0)
            break;
    }
    if (munmap(data, page_size) != 0)
        return 2;
    return result;
}

int main(int argc, char **argv)
{
    const char *profile = argc == 3 ? argv[1] : "increment";
    if ((argc != 2 && argc != 3) ||
        (strcmp(profile, "increment") != 0 && strcmp(profile, "load32") != 0 &&
         strcmp(profile, "store32") != 0))
        return 2;
    int memory_profile = strcmp(profile, "increment") != 0;
    size_t expected_size = memory_profile ? 3 : 4;
    FILE *file = fopen(argv[argc - 1], "rb");
    if (!file)
        return 2;
    unsigned char bytes[16];
    size_t size = fread(bytes, 1, sizeof bytes, file);
    int extra = fgetc(file);
    int failed = ferror(file);
    fclose(file);
    if (failed || size != expected_size || extra != EOF)
        return 2;
    long page_size = sysconf(_SC_PAGESIZE);
    if (page_size < 16)
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
    int result = memory_profile
        ? check_memory(mapping, strcmp(profile, "store32") == 0, (size_t)page_size)
        : check_increment(mapping);
    if (munmap(mapping, (size_t)page_size) != 0)
        return 2;
    return result;
}
