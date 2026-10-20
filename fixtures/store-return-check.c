/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
 * Independent oracle for exact final callable bytes, including full returned
 * pointers, every data-page byte, and the external SysV ABI observation. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>
extern uint64_t edsl_cfg_call(const void *, const void *, size_t,
                             const void *, size_t, uint64_t *);
static void fail(const char *s) { perror(s); exit(2); }
static int suite(const void *code, size_t page)
{
    unsigned char *map = mmap(NULL, 3 * page, PROT_NONE,
                             MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (map == MAP_FAILED) fail("mmap guards");
    unsigned char *data = map + page;
    if (mprotect(data, page, PROT_READ | PROT_WRITE)) fail("mprotect data");
    if ((uintptr_t)data <= UINT32_MAX) {
        fputs("Cannot test full pointer preservation below 4GiB\n", stderr);
        return 2;
    }
    const uint64_t arguments[] = {0, UINT64_MAX, UINT64_C(0xfeedface89abcdef),
        UINT64_C(0x100000000), UINT64_C(0x80000000),
        UINT64_C(0x0123456789abcdef), UINT64_C(0xaaaaaaaa55555555)};
    const size_t offsets[] = {0, 2, 4, 16, page - 5, page - 4};
    for (size_t a = 0; a < sizeof arguments / sizeof arguments[0]; ++a)
    for (size_t i = 0; i < sizeof offsets / sizeof offsets[0]; ++i)
    for (unsigned fill = 0; fill < 2; ++fill) {
        unsigned char sentinel = fill ? 0x5a : 0xa5;
        memset(data, sentinel, page);
        unsigned char *pointer = data + offsets[i];
        uint64_t violations = UINT64_MAX;
        uint64_t actual = edsl_cfg_call(code, pointer, (size_t)arguments[a], NULL, 0, &violations);
        if (actual != (uintptr_t)pointer || violations) {
            fprintf(stderr, "pointer or ABI mismatch: target=%016" PRIxPTR
                " actual=%016" PRIx64 " ABI=%" PRIx64 "\n",
                (uintptr_t)pointer, actual, violations);
            return 1;
        }
        for (size_t q = 0; q < page; ++q) {
            unsigned char expected = q >= offsets[i] && q - offsets[i] < 4
                ? (unsigned char)(arguments[a] >> (8 * (q - offsets[i]))) : sentinel;
            if (data[q] != expected) {
                fprintf(stderr, "footprint mismatch argument=%016" PRIx64
                    " target=%zu query=%zu actual=%02x expected=%02x\n",
                    arguments[a], offsets[i], q, data[q], expected);
                return 1;
            }
        }
    }
    if (munmap(map, 3 * page)) fail("munmap data");
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
    int rejected = (WIFEXITED(status) && WEXITSTATUS(status) == 1)
        || (WIFSIGNALED(status) && (WTERMSIG(status) == SIGSEGV || WTERMSIG(status) == SIGBUS));
    if (negative ? rejected : passed) {
        printf("%s %s%s\n", negative ? "REJECTED owned mutant:" : "PASSED", name,
               negative ? "" : " (84 full-pointer/page-frame/ABI calls)");
        return 0;
    }
    fprintf(stderr, "unexpected status %d: %s\n", status, name);
    return 1;
}
int main(int argc, char **argv)
{
    if (argc < 2) return 2;
    struct rlimit no_core = {0, 0};
    if (setrlimit(RLIMIT_CORE, &no_core)) fail("setrlimit");
    long ps = sysconf(_SC_PAGESIZE);
    if (ps < 64) return 2;
    size_t page = (size_t)ps;
    int result = 0;
    for (int i = 1; i < argc; ++i) {
        int fd = open(argv[i], O_RDONLY | O_CLOEXEC);
        if (fd < 0) fail("open final bytes");
        struct stat st;
        if (fstat(fd, &st)) fail("fstat");
        if (st.st_size <= 0 || (uint64_t)st.st_size > page) return 2;
        void *code = mmap(NULL, page, PROT_READ | PROT_EXEC, MAP_PRIVATE, fd, 0);
        if (code == MAP_FAILED) fail("mmap exact final bytes");
        if (close(fd)) fail("close");
        result |= check(code, page, 0, argv[i]);
        if (munmap(code, page)) fail("munmap code");
    }
    const struct { const char *name; unsigned char bytes[8]; } mutants[] = {
        {"truncated returned pointer", {0x89, 0xf8, 0x89, 0x37, 0xc3}},
        {"no store", {0x48, 0x89, 0xf8, 0xc3}},
        {"eight-byte store", {0x48, 0x89, 0xf8, 0x48, 0x89, 0x37, 0xc3}},
        {"wrong source", {0x48, 0x89, 0xf8, 0x89, 0x07, 0xc3}},
        {"wrong target", {0x48, 0x89, 0xf8, 0x89, 0x77, 0x04, 0xc3}},
        {"wrong returned pointer", {0x89, 0x37, 0x48, 0x8d, 0x47, 0x04, 0xc3}}
    };
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        void *code = mmap(NULL, page, PROT_READ | PROT_WRITE,
                          MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (code == MAP_FAILED) fail("mmap mutant");
        memcpy(code, mutants[i].bytes, sizeof mutants[i].bytes);
        if (mprotect(code, page, PROT_READ | PROT_EXEC)) fail("mprotect mutant");
        result |= check(code, page, 1, mutants[i].name);
        if (munmap(code, page)) fail("munmap mutant");
    }
    return result;
}
