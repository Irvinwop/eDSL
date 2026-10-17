/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
 * Independent closed-form result, complete data-page frame and SysV ABI oracle.
 * The C harness never dereferences an unaligned uint64_t pointer. */
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
_Static_assert(UINTPTR_MAX == UINT64_MAX, "64-bit trampoline count argument ABI");

static void fail(const char *message) { perror(message); exit(2); }

static int suite(const void *code, size_t page)
{
    unsigned char *mapping = mmap(NULL, 3 * page, PROT_NONE,
        MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED) fail("mmap data guards");
    unsigned char *data = mapping + page;
    if (mprotect(data, page, PROT_READ | PROT_WRITE)) fail("mprotect data");
    if ((uintptr_t)data <= UINT32_MAX) {
        fputs("Full-width address evidence requires an owned pointer above4GiB\n", stderr);
        return 2;
    }
    unsigned char *expected = malloc(page);
    if (!expected) fail("malloc expected page");
    const uint64_t arguments[] = {0, UINT64_MAX, UINT64_C(0xfeedface89abcdef),
        UINT64_C(0xffffffff), UINT64_C(0x100000000),
        UINT64_C(0x8000000000000000), UINT64_C(0xfffffffffffffff0)};
    const uint64_t counts[] = {0, 1, 2, 3, 31, 257};
    const uint64_t old_values[] = {UINT64_C(0x1234567887654321), UINT64_C(0xa5a55a5af00f0ff0)};
    const size_t offsets[] = {0, 1, 8, 16, page - 9, page - 8};
    for (size_t a = 0; a < sizeof arguments / sizeof arguments[0]; ++a)
    for (size_t c = 0; c < sizeof counts / sizeof counts[0]; ++c)
    for (size_t i = 0; i < sizeof offsets / sizeof offsets[0]; ++i)
    for (size_t o = 0; o < sizeof old_values / sizeof old_values[0]; ++o) {
        for (size_t query = 0; query < page; ++query)
            data[query] = (unsigned char)(query * 29 + 0x5a + o);
        unsigned char *pointer = data + offsets[i];
        memcpy(pointer, &old_values[o], sizeof old_values[o]);
        memcpy(expected, data, page);
        /* Closed-form contract, independent of the implementation's loop. */
        uint64_t returned = arguments[a] + counts[c];
        uint64_t stored = counts[c] == 0 ? old_values[o] : returned;
        memcpy(expected + offsets[i], &stored, sizeof stored);
        uint64_t violations = UINT64_MAX;
        uint64_t actual = edsl_cfg_call(code, pointer, (size_t)arguments[a],
            (const void *)(uintptr_t)counts[c], 0, &violations);
        if (actual != returned || violations) {
            fprintf(stderr, "value or ABI mismatch: argument=%016" PRIx64
                " count=%" PRIu64 " expected=%016" PRIx64 " actual=%016" PRIx64
                " ABI=%" PRIx64 "\n", arguments[a], counts[c], returned, actual, violations);
            return 1;
        }
        for (size_t query = 0; query < page; ++query) {
            if (data[query] != expected[query]) {
                fprintf(stderr, "page-frame mismatch: argument=%016" PRIx64
                    " count=%" PRIu64 " target=%zu query=%zu actual=%02x expected=%02x\n",
                    arguments[a], counts[c], offsets[i], query, data[query], expected[query]);
                return 1;
            }
        }
    }
    free(expected);
    if (munmap(mapping, 3 * page)) fail("munmap data");
    return 0;
}

static int check(const void *code, size_t page, int negative, const char *name)
{
    fflush(NULL);
    pid_t child = fork();
    if (child < 0) fail("fork");
    if (child == 0) { alarm(5); exit(suite(code, page)); }
    int status;
    while (waitpid(child, &status, 0) < 0) if (errno != EINTR) fail("waitpid");
    int passed = WIFEXITED(status) && WEXITSTATUS(status) == 0;
    int rejected = (WIFEXITED(status) && WEXITSTATUS(status) == 1) ||
        (WIFSIGNALED(status) && (WTERMSIG(status) == SIGSEGV || WTERMSIG(status) == SIGBUS));
    if (negative ? rejected : passed) {
        printf("%s %s%s\n", negative ? "REJECTED owned mutant:" : "PASSED", name,
            negative ? "" : " (504 closed-form/full64/page-frame/ABI calls)");
        return 0;
    }
    /* An alarm, unexpected signal, or harness setup failure is inconclusive. */
    fprintf(stderr, "inconclusive or unexpected status %d: %s\n", status, name);
    return 2;
}

static void *copy_code(const unsigned char *bytes, size_t length, size_t page)
{
    unsigned char *mapping = mmap(NULL, 3 * page, PROT_NONE,
        MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED) fail("mmap code guards");
    unsigned char *code = mapping + page;
    if (mprotect(code, page, PROT_READ | PROT_WRITE)) fail("mprotect code write");
    memcpy(code, bytes, length);
    if (mprotect(code, page, PROT_READ | PROT_EXEC)) fail("mprotect code execute");
    return code;
}

static void release_code(void *code, size_t page)
{
    if (munmap((unsigned char *)code - page, 3 * page)) fail("munmap code");
}

int main(int argc, char **argv)
{
    if (argc < 2) return 2;
    const struct rlimit no_core = {0, 0};
    if (setrlimit(RLIMIT_CORE, &no_core)) fail("setrlimit");
    long page_size = sysconf(_SC_PAGESIZE);
    if (page_size < 64) return 2;
    size_t page = (size_t)page_size;
    unsigned char *bytes = malloc(page);
    if (!bytes) fail("malloc code bytes");
    int result = 0;
    for (int i = 1; i < argc; ++i) {
        int descriptor = open(argv[i], O_RDONLY | O_CLOEXEC);
        if (descriptor < 0) fail("open final bytes");
        struct stat status;
        if (fstat(descriptor, &status)) fail("fstat");
        if (status.st_size <= 0 || (uint64_t)status.st_size > page) return 2;
        size_t length = (size_t)status.st_size;
        for (size_t offset = 0; offset < length;) {
            ssize_t amount = read(descriptor, bytes + offset, length - offset);
            if (amount < 0 && errno == EINTR) continue;
            if (amount <= 0) fail("read final bytes");
            offset += (size_t)amount;
        }
        if (close(descriptor)) fail("close");
        void *code = copy_code(bytes, length, page);
        result |= check(code, page, 0, argv[i]);
        release_code(code, page);
    }
    free(bytes);
    const struct { const char *name; size_t length; unsigned char bytes[32]; } mutants[] = {
        {"missing store", 20,
            {0x48,0x89,0xf0,0x48,0x85,0xd2,0x74,0x0b,0x48,0xff,0xc0,0x48,0xff,0xca,
             0x90,0x90,0x90,0xeb,0xf0,0xc3}},
        {"32-bit store", 20,
            {0x48,0x89,0xf0,0x48,0x85,0xd2,0x74,0x0b,0x48,0xff,0xc0,0x48,0xff,0xca,
             0x90,0x89,0x07,0xeb,0xf0,0xc3}},
        {"only one iteration", 20,
            {0x48,0x89,0xf0,0x48,0x85,0xd2,0x74,0x0b,0x48,0xff,0xc0,0x48,0x31,0xd2,
             0x48,0x89,0x07,0xeb,0xf0,0xc3}},
        {"decrement value", 20,
            {0x48,0x89,0xf0,0x48,0x85,0xd2,0x74,0x0b,0x48,0xff,0xc8,0x48,0xff,0xca,
             0x48,0x89,0x07,0xeb,0xf0,0xc3}},
        {"neighbor overwrite", 24,
            {0x48,0x89,0xf0,0x48,0x85,0xd2,0x74,0x0f,0x48,0xff,0xc0,0x48,0xff,0xca,
             0x48,0x89,0x07,0xc6,0x47,0x08,0x00,0xeb,0xec,0xc3}},
        {"clobber saved R12", 23,
            {0x45,0x31,0xe4,0x48,0x89,0xf0,0x48,0x85,0xd2,0x74,0x0b,0x48,0xff,0xc0,
             0x48,0xff,0xca,0x48,0x89,0x07,0xeb,0xf0,0xc3}}
    };
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        void *code = copy_code(mutants[i].bytes, mutants[i].length, page);
        result |= check(code, page, 1, mutants[i].name);
        release_code(code, page);
    }
    return result;
}
