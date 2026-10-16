/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
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

typedef uint32_t (*sum_function)(const uint32_t *, size_t);
extern uint64_t edsl_sum32_call(sum_function, const uint32_t *, size_t, uint64_t *);
extern uint32_t edsl_sum32_bad_high(const uint32_t *, size_t);
extern uint32_t edsl_sum32_bad_saved(const uint32_t *, size_t);

static void fail_system(const char *operation)
{
    perror(operation);
    exit(2);
}

static void observe(sum_function function, const uint32_t *p, size_t n,
                    uint32_t expected, const char *label)
{
    uint64_t violations = UINT64_MAX;
    uint64_t actual = edsl_sum32_call(function, p, n, &violations);
    if (actual != (uint64_t)expected || violations != 0) {
        fprintf(stderr, "%s n=%zu: RAX=%016" PRIx64 " expected=%08" PRIx32
                " ABI=%" PRIx64 "\n", label, n, actual, expected, violations);
        exit(1);
    }
}

/* The oracle is algebraic. No second summation loop computes an expectation.
   Each nonempty input ends exactly at an unreadable page; its preceding page
   becomes read-only before invocation. A nonzero prefix sentinel exposes
   wrong-base/stride errors even if an erroneous read stays in the page. */
static void suite(sum_function function, size_t page)
{
    unsigned char *mapping = mmap(NULL, 3 * page, PROT_NONE,
                                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED)
        fail_system("mmap guard pages");
    unsigned char *data = mapping + page;
    observe(function, NULL, 0, 0, "zero/null");
    observe(function, (const uint32_t *)(mapping + 2 * page), 0, 0, "zero/guard");

    static const size_t counts[] = {1, 2, 3, 7, 17, 63, 127, 255};
    for (size_t c = 0; c < sizeof counts / sizeof counts[0]; ++c) {
        size_t n = counts[c];
        if ((n + 1) * sizeof(uint32_t) > page)
            fail_system("page too small");
        uint32_t *p = (uint32_t *)(data + page) - n;
        for (unsigned pattern = 0; pattern < 4; ++pattern) {
            if (mprotect(data, page, PROT_READ | PROT_WRITE) != 0)
                fail_system("mprotect initialize");
            p[-1] = UINT32_C(0xdeadbeef);
            for (size_t i = 0; i < n; ++i) {
                switch (pattern) {
                case 0: p[i] = UINT32_C(0xf1234567); break;
                case 1: p[i] = UINT32_MAX; break;
                case 2: p[i] = (uint32_t)(19 + 37 * i); break;
                default: p[i] = i % 2 == 0 ? UINT32_C(0x87654321) : UINT32_C(0xfedcba98); break;
                }
            }
            uint32_t expected;
            const char *label;
            switch (pattern) {
            case 0:
                expected = (uint32_t)((uint64_t)n * UINT32_C(0xf1234567));
                label = "constant product";
                break;
            case 1:
                expected = (uint32_t)(UINT64_C(0x100000000) - n);
                label = "all ones wrap";
                break;
            case 2:
                expected = (uint32_t)(19 * n + 37 * (n * (n - 1) / 2));
                label = "arithmetic progression";
                break;
            default:
                expected = (uint32_t)(((n + 1) / 2) * (uint64_t)UINT32_C(0x87654321)
                            + (n / 2) * (uint64_t)UINT32_C(0xfedcba98));
                label = "alternating multiplicities";
                break;
            }
            if (mprotect(data, page, PROT_READ) != 0)
                fail_system("mprotect readonly");
            observe(function, p, n, expected, label);
        }
    }
    if (mprotect(data, page, PROT_READ | PROT_WRITE) != 0)
        fail_system("mprotect fixed fixture");
    uint32_t *fixed = (uint32_t *)(data + page) - 4;
    fixed[-1] = UINT32_C(0xdeadbeef);
    fixed[0] = UINT32_C(0xffffffff);
    fixed[1] = 2;
    fixed[2] = UINT32_C(0x80000000);
    fixed[3] = UINT32_C(0x80000001);
    if (mprotect(data, page, PROT_READ) != 0)
        fail_system("mprotect readonly fixed fixture");
    observe(function, fixed, 4, 2, "fixed modular identity");
    if (munmap(mapping, 3 * page) != 0)
        fail_system("munmap guards");
}

static int run_isolated(sum_function function, size_t page, int negative, const char *name)
{
    fflush(NULL);
    pid_t child = fork();
    if (child < 0)
        fail_system("fork");
    if (child == 0) {
        alarm(5);
        suite(function, page);
        exit(0);
    }
    int status;
    while (waitpid(child, &status, 0) < 0) {
        if (errno != EINTR)
            fail_system("waitpid");
    }
    int passed = WIFEXITED(status) && WEXITSTATUS(status) == 0;
    int rejected = (WIFEXITED(status) && WEXITSTATUS(status) == 1)
        || (WIFSIGNALED(status) && (WTERMSIG(status) == SIGSEGV || WTERMSIG(status) == SIGBUS));
    if (negative ? rejected : passed) {
        printf("NATIVE %s: %s", negative ? "rejected owned mutant" : "observations passed", name);
        if (WIFSIGNALED(status))
            printf(" (guard fault signal %d)", WTERMSIG(status));
        else if (!negative)
            printf(" (35 calls, full RAX and ABI)");
        putchar('\n');
        return 0;
    }
    fprintf(stderr, "%s: unexpected native child status %d\n", name, status);
    return 1;
}

int main(int argc, char **argv)
{
    int negative = argc == 3 && strcmp(argv[1], "--expect-reject") == 0;
    if ((!negative && argc != 2) || (argc == 3 && !negative)) {
        fprintf(stderr, "usage: %s [--expect-reject] final-linked.bin\n", argv[0]);
        return 2;
    }
    struct rlimit no_core = {0, 0};
    if (setrlimit(RLIMIT_CORE, &no_core) != 0)
        fail_system("setrlimit");
    long page_value = sysconf(_SC_PAGESIZE);
    if (page_value <= 0)
        fail_system("sysconf page size");
    size_t page = (size_t)page_value;
    const char *path = argv[negative ? 2 : 1];
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0)
        fail_system("open final linked bytes");
    struct stat info;
    if (fstat(fd, &info) != 0)
        fail_system("fstat final linked bytes");
    if (info.st_size <= 0 || (uint64_t)info.st_size > page) {
        fprintf(stderr, "native mapping requires 1..%zu bytes\n", page);
        return 2;
    }
    void *code = mmap(NULL, page, PROT_READ | PROT_EXEC, MAP_PRIVATE, fd, 0);
    if (code == MAP_FAILED)
        fail_system("mmap final linked bytes RX");
    if (close(fd) != 0)
        fail_system("close final linked bytes");
    int result = run_isolated((sum_function)code, page, negative, path);
    if (!negative) {
        result |= run_isolated(edsl_sum32_bad_high, page, 1, "nonzero upper RAX");
        result |= run_isolated(edsl_sum32_bad_saved, page, 1, "clobbered callee-saved R12");
    }
    if (munmap(code, page) != 0)
        fail_system("munmap final linked bytes");
    return result;
}
