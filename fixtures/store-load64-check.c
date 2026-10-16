/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
 * Independent full-value, complete data-page and external SysV ABI oracle. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

extern uint64_t edsl_cfg_call(const void *, const void *, size_t,
                             const void *, size_t, uint64_t *);
_Static_assert(sizeof(size_t) == sizeof(uint64_t), "64-bit trampoline argument ABI");

static void fail(const char *message) { perror(message); exit(2); }

static int suite(const void *code, size_t page)
{
    unsigned char *mapping = mmap(NULL, 3 * page, PROT_NONE,
        MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED) fail("mmap guards");
    unsigned char *data = mapping + page;
    if (mprotect(data, page, PROT_READ | PROT_WRITE)) fail("mprotect data");
    if ((uintptr_t)data <= UINT32_MAX) {
        fputs("Full-width address evidence requires an owned pointer above4GiB\n", stderr);
        return 2;
    }
    const uint64_t arguments[] = {0, UINT64_MAX, UINT64_C(0xfeedface89abcdef),
        UINT64_C(0x100000000), UINT64_C(0x8000000000000000),
        UINT64_C(0x0123456789abcdef), UINT64_C(0xaaaaaaaa55555555)};
    const size_t offsets[] = {0, 1, 8, 16, page - 9, page - 8};
    for (size_t a = 0; a < sizeof arguments / sizeof arguments[0]; ++a)
    for (size_t i = 0; i < sizeof offsets / sizeof offsets[0]; ++i)
    for (unsigned int fill = 0; fill < 2; ++fill) {
        unsigned char sentinel = fill ? 0x5a : 0xa5;
        memset(data, sentinel, page);
        unsigned char *pointer = data + offsets[i];
        uint64_t violations = UINT64_MAX;
        uint64_t actual = edsl_cfg_call(code, pointer, (size_t)arguments[a], NULL, 0, &violations);
        if (actual != arguments[a] || violations) {
            fprintf(stderr, "value or ABI mismatch: requested=%016" PRIx64
                " actual=%016" PRIx64 " ABI=%" PRIx64 "\n", arguments[a], actual, violations);
            return 1;
        }
        for (size_t query = 0; query < page; ++query) {
            unsigned char expected = query >= offsets[i] && query - offsets[i] < 8
                ? (unsigned char)(arguments[a] >> (8 * (query - offsets[i]))) : sentinel;
            if (data[query] != expected) {
                fprintf(stderr, "footprint mismatch: requested=%016" PRIx64
                    " target=%zu query=%zu actual=%02x expected=%02x\n",
                    arguments[a], offsets[i], query, data[query], expected);
                return 1;
            }
        }
    }
    if (munmap(mapping, 3 * page)) fail("munmap data");
    return 0;
}

static int check(const void *code, size_t page, int negative, const char *name)
{
    fflush(NULL);
    pid_t child = fork();
    if (child < 0) fail("fork");
    if (child == 0) { alarm(3); exit(suite(code, page)); }
    int status;
    while (waitpid(child, &status, 0) < 0) if (errno != EINTR) fail("waitpid");
    int passed = WIFEXITED(status) && WEXITSTATUS(status) == 0;
    int rejected = (WIFEXITED(status) && WEXITSTATUS(status) == 1) ||
        (WIFSIGNALED(status) && (WTERMSIG(status) == SIGSEGV || WTERMSIG(status) == SIGBUS));
    if (negative ? rejected : passed) {
        printf("%s %s%s\n", negative ? "REJECTED owned mutant:" : "PASSED", name,
            negative ? "" : " (84 full64-value/page-frame/ABI calls)");
        return 0;
    }
    fprintf(stderr, "unexpected status %d: %s\n", status, name);
    return 1;
}

int main(int argc, char **argv)
{
    if (argc < 2) return 2;
    const struct rlimit no_core = {0, 0};
    if (setrlimit(RLIMIT_CORE, &no_core)) fail("setrlimit");
    long page_size = sysconf(_SC_PAGESIZE);
    if (page_size < 64) return 2;
    size_t page = (size_t)page_size;
    int result = 0;
    for (int i = 1; i < argc; ++i) {
        int descriptor = open(argv[i], O_RDONLY | O_CLOEXEC);
        if (descriptor < 0) fail("open final bytes");
        struct stat status;
        if (fstat(descriptor, &status)) fail("fstat");
        if (status.st_size <= 0 || (uint64_t)status.st_size > page) return 2;
        void *code = mmap(NULL, page, PROT_READ | PROT_EXEC, MAP_PRIVATE, descriptor, 0);
        if (code == MAP_FAILED) fail("mmap exact final bytes");
        if (close(descriptor)) fail("close");
        result |= check(code, page, 0, argv[i]);
        if (munmap(code, page)) fail("munmap code");
    }
    const struct { const char *name; unsigned char bytes[16]; } mutants[] = {
        {"32-bit store", {0x89,0x37,0x48,0x8b,0x07,0xc3}},
        {"32-bit load", {0x48,0x89,0x37,0x8b,0x07,0xc3}},
        {"missing store", {0x48,0x89,0xf0,0xc3}},
        {"wrong source", {0x48,0x89,0x07,0x48,0x8b,0x07,0xc3}},
        {"reversed stored bytes", {0x48,0x0f,0xce,0x48,0x89,0x37,0x48,0x8b,0x07,0xc3}},
        {"neighbor overwrite", {0x48,0x89,0x37,0xc6,0x47,0x08,0x00,0x48,0x8b,0x07,0xc3}}
    };
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        void *code = mmap(NULL, page, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (code == MAP_FAILED) fail("mmap mutant");
        memcpy(code, mutants[i].bytes, sizeof mutants[i].bytes);
        if (mprotect(code, page, PROT_READ | PROT_EXEC)) fail("mprotect mutant");
        result |= check(code, page, 1, mutants[i].name);
        if (munmap(code, page)) fail("munmap mutant");
    }
    return result;
}
