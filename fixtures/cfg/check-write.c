/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

extern uint64_t edsl_cfg_call(const void *, const uint32_t *, size_t,
                             const uint32_t *, size_t, uint64_t *);

static void system_error(const char *operation)
{
    perror(operation);
    exit(2);
}

/* A byte-level memory oracle observes the specified four-byte footprint and
   every other byte of the data page, without executing another store-word
   implementation as its expected result. The trampoline independently checks
   all six callee-saved GPRs, stack balance, a stack canary, and DF. RAX is void. */
static int suite(const void *code, size_t page)
{
    unsigned char *mapping = mmap(NULL, 3 * page, PROT_NONE,
                                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED)
        system_error("mmap data guards");
    unsigned char *data = mapping + page;
    if (mprotect(data, page, PROT_READ | PROT_WRITE) != 0)
        system_error("mprotect data");
    static const uint64_t arguments[] = {
        0, UINT64_MAX, UINT64_C(0xfeedface89abcdef),
        UINT64_C(0x100000000), UINT64_C(0x80000000),
        UINT64_C(0x0123456789abcdef), UINT64_C(0xaaaaaaaa55555555)
    };
    const size_t offsets[] = {0, 1, 3, 16, page - 5, page - 4};
    for (size_t a = 0; a < sizeof arguments / sizeof arguments[0]; ++a) {
        for (size_t p = 0; p < sizeof offsets / sizeof offsets[0]; ++p) {
            for (unsigned fill = 0; fill < 2; ++fill) {
                unsigned char sentinel = fill == 0 ? 0xa5 : 0x5a;
                memset(data, sentinel, page);
                uint64_t violations = UINT64_MAX;
                (void)edsl_cfg_call(code, (const uint32_t *)(data + offsets[p]),
                                   (size_t)arguments[a], NULL, 0, &violations);
                if (violations != 0) {
                    fprintf(stderr, "write ABI violations=%" PRIx64 "\n", violations);
                    return 1;
                }
                for (size_t q = 0; q < page; ++q) {
                    unsigned char expected = q >= offsets[p] && q - offsets[p] < 4
                        ? (unsigned char)(arguments[a] >> (8 * (q - offsets[p])))
                        : sentinel;
                    if (data[q] != expected) {
                        fprintf(stderr, "write argument=%016" PRIx64
                                " target=%zu query=%zu actual=%02x expected=%02x\n",
                                arguments[a], offsets[p], q, data[q], expected);
                        return 1;
                    }
                }
            }
        }
    }
    if (munmap(mapping, 3 * page) != 0)
        system_error("munmap data guards");
    return 0;
}

static int isolated(const void *code, size_t page, int negative, const char *name)
{
    fflush(NULL);
    pid_t child = fork();
    if (child < 0)
        system_error("fork observer");
    if (child == 0)
        exit(suite(code, page));
    int status;
    while (waitpid(child, &status, 0) < 0) {
        if (errno != EINTR)
            system_error("waitpid observer");
    }
    int passed = WIFEXITED(status) && WEXITSTATUS(status) == 0;
    int rejected = (WIFEXITED(status) && WEXITSTATUS(status) == 1)
        || (WIFSIGNALED(status) && (WTERMSIG(status) == SIGSEGV || WTERMSIG(status) == SIGBUS));
    if (negative ? rejected : passed) {
        printf("NATIVE write32 %s: %s\n", negative ? "rejected owned mutant" : "passed", name);
        return 0;
    }
    fprintf(stderr, "%s: unexpected observer status %d\n", name, status);
    return 1;
}

int main(int argc, char **argv)
{
    if (argc != 2) {
        fprintf(stderr, "usage: %s final-linked.bin\n", argv[0]);
        return 2;
    }
    struct rlimit no_core = {0, 0};
    if (setrlimit(RLIMIT_CORE, &no_core) != 0)
        system_error("setrlimit");
    long page_value = sysconf(_SC_PAGESIZE);
    if (page_value < 32)
        system_error("sysconf page size");
    size_t page = (size_t)page_value;
    int fd = open(argv[1], O_RDONLY | O_CLOEXEC);
    if (fd < 0)
        system_error("open linked bytes");
    struct stat info;
    if (fstat(fd, &info) != 0)
        system_error("fstat linked bytes");
    if (info.st_size <= 0 || (uint64_t)info.st_size > page)
        return 2;
    void *code = mmap(NULL, page, PROT_READ | PROT_EXEC, MAP_PRIVATE, fd, 0);
    if (code == MAP_FAILED)
        system_error("mmap linked bytes");
    if (close(fd) != 0)
        system_error("close linked bytes");
    int result = isolated(code, page, 0, argv[1]);
    if (munmap(code, page) != 0)
        system_error("munmap linked bytes");

    /* Owned mutations demonstrate detection of missing/wrong-width stores,
       a shifted footprint, wrong source, callee-saved clobber and DF damage. */
    static const struct {
        const char *name;
        unsigned char bytes[6];
    } mutants[] = {
        {"no store", {0xc3}},
        {"eight-byte store", {0x48, 0x89, 0x37, 0xc3}},
        {"wrong target", {0x89, 0x77, 0x04, 0xc3}},
        {"wrong source", {0x89, 0x07, 0xc3}},
        {"callee-saved R12", {0x89, 0x37, 0x45, 0x31, 0xe4, 0xc3}},
        {"direction flag", {0x89, 0x37, 0xfd, 0xc3}}
    };
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        code = mmap(NULL, page, PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (code == MAP_FAILED)
            system_error("mmap owned mutant");
        memcpy(code, mutants[i].bytes, sizeof mutants[i].bytes);
        if (mprotect(code, page, PROT_READ | PROT_EXEC) != 0)
            system_error("mprotect owned mutant RX");
        result |= isolated(code, page, 1, mutants[i].name);
        if (munmap(code, page) != 0)
            system_error("munmap owned mutant");
    }
    return result;
}
