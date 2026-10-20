/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <elf.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

static void fail(const char *message)
{
    fprintf(stderr, "atomic set grading observer: %s\n", message);
    exit(1);
}

static unsigned char *read_file(const char *path, size_t limit, size_t *size)
{
    FILE *file = fopen(path, "rb");
    if (!file) fail("input open failed");
    unsigned char *bytes = malloc(limit + 1);
    if (!bytes) fail("allocation failed");
    *size = fread(bytes, 1, limit + 1, file);
    if (ferror(file) || *size > limit || fclose(file)) fail("bounded input failed");
    return bytes;
}

/* Independent natural-bit set specification, selected by the requested task.
 * It never consults decoded instructions or intermediate machine updates. */
static uint64_t expected(unsigned task, uint64_t old, uint64_t mask)
{
    uint64_t result = 0;
    for (unsigned bit = 0; bit < 64; ++bit) {
        bool left = (old >> bit) % 2;
        bool right = (mask >> bit) % 2;
        bool member = task == 0 ? left && right : task == 1 ? left || right : left != right;
        if (member) result += UINT64_C(1) << bit;
    }
    return result;
}

static uint64_t next_word(uint64_t *seed)
{
    *seed = *seed * UINT64_C(6364136223846793005) + UINT64_C(1442695040888963407);
    return *seed;
}

int main(int argc, char **argv)
{
    if (argc != 4) fail("usage: TASK RAW ELF");
    unsigned task;
    if (!strcmp(argv[1], "intersection")) task = 0;
    else if (!strcmp(argv[1], "union")) task = 1;
    else if (!strcmp(argv[1], "symmetricDifference")) task = 2;
    else fail("unknown task");
    size_t raw_size, elf_size;
    unsigned char *raw = read_file(argv[2], 4096, &raw_size);
    unsigned char *elf = read_file(argv[3], 65536, &elf_size);
    if (!raw_size || elf_size < sizeof(Elf64_Ehdr)) fail("empty or truncated input");
    Elf64_Ehdr header;
    memcpy(&header, elf, sizeof(header));
    if (memcmp(header.e_ident, ELFMAG, SELFMAG) || header.e_ident[EI_CLASS] != ELFCLASS64 ||
        header.e_ident[EI_DATA] != ELFDATA2LSB || header.e_machine != EM_X86_64 ||
        header.e_type != ET_EXEC || header.e_phentsize != sizeof(Elf64_Phdr) ||
        header.e_phoff > elf_size || header.e_phnum > (elf_size - header.e_phoff) / sizeof(Elf64_Phdr))
        fail("unsupported ELF header");
    size_t offset = 0;
    unsigned mappings = 0;
    for (unsigned index = 0; index < header.e_phnum; ++index) {
        Elf64_Phdr segment;
        memcpy(&segment, elf + header.e_phoff + index * sizeof(segment), sizeof(segment));
        if (segment.p_type != PT_LOAD || !(segment.p_flags & PF_X) ||
            header.e_entry < segment.p_vaddr) continue;
        uint64_t delta = header.e_entry - segment.p_vaddr;
        if (delta > segment.p_filesz || raw_size > segment.p_filesz - delta) continue;
        if (segment.p_offset > elf_size || delta > elf_size - segment.p_offset ||
            raw_size > elf_size - segment.p_offset - delta || segment.p_flags & PF_W)
            fail("invalid executable backing");
        offset = (size_t)(segment.p_offset + delta);
        ++mappings;
    }
    if (mappings != 1 || memcmp(raw, elf + offset, raw_size)) fail("raw/ELF entry identity failed");
    /* Only the owned strict logical/RET profile may execute in this observer. */
    size_t cursor = 0;
    while (cursor + 1 < raw_size) {
        if (raw_size - cursor < 5 || raw[cursor] != 0xf0 || raw[cursor + 1] != 0x48 ||
            (raw[cursor + 2] != 0x21 && raw[cursor + 2] != 0x09 && raw[cursor + 2] != 0x31) ||
            raw[cursor + 3] != 0x37) fail("unsupported owned profile");
        cursor += 4;
    }
    if (cursor + 1 != raw_size || raw[cursor] != 0xc3) fail("missing terminal RET");
    void *slot = mmap(NULL, raw_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (slot == MAP_FAILED) fail("code allocation failed");
    memcpy(slot, elf + offset, raw_size);
    if (memcmp(slot, raw, raw_size) || mprotect(slot, raw_size, PROT_READ | PROT_EXEC))
        fail("loaded code binding failed");
    void (*function)(uint64_t *, uint64_t);
    _Static_assert(sizeof(function) == sizeof(slot), "Linux x86-64 function pointer representation");
    memcpy(&function, &slot, sizeof(function));
    static const uint64_t edges[] = {0, 1, 2, UINT64_C(1) << 63, UINT64_MAX,
        UINT64_C(0xaaaaaaaaaaaaaaaa), UINT64_C(0x5555555555555555)};
    uint64_t seed = UINT64_C(0xced5a764);
    size_t calls = 0;
    for (size_t index = 0; index < 4145; ++index) {
        uint64_t old = index < 49 ? edges[index / 7] : next_word(&seed);
        uint64_t mask = index < 49 ? edges[index % 7] : next_word(&seed);
        _Alignas(64) uint64_t cells[8] = {UINT64_C(0x13579bdf), old, UINT64_C(0x2468ace0)};
        uint64_t saved[8];
        memcpy(saved, cells, sizeof(saved));
        function(&cells[1], mask);
        if (cells[1] != expected(task, old, mask)) fail("independent set result mismatch");
        for (unsigned cell = 0; cell < 8; ++cell)
            if (cell != 1 && cells[cell] != saved[cell]) fail("neighbor frame mismatch");
        ++calls;
    }
    if (munmap(slot, raw_size)) fail("code release failed");
    printf("PASS task=%s: %zu exact-entry calls, independent set result and neighbor frame\n", argv[1], calls);
    free(raw);
    free(elf);
    return 0;
}
