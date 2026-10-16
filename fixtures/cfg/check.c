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

extern uint64_t edsl_cfg_call(const void *, const uint32_t *, size_t,
                              const uint32_t *, size_t, uint64_t *);
extern void edsl_cfg_bad_high(void);
extern void edsl_cfg_bad_saved(void);

static void fail_system(const char *operation)
{
    perror(operation);
    exit(2);
}

static void observe(const void *code, const uint32_t *a, size_t na,
                    const uint32_t *b, size_t nb, uint32_t expected,
                    const char *label)
{
    uint64_t violations = UINT64_MAX;
    uint64_t actual = edsl_cfg_call(code, a, na, b, nb, &violations);
    if (actual != (uint64_t)expected || violations != 0) {
        fprintf(stderr, "%s counts=%zu,%zu: RAX=%016" PRIx64
                " expected=%08" PRIx32 " ABI=%" PRIx64 "\n",
                label, na, nb, actual, expected, violations);
        exit(1);
    }
}

struct guarded {
    unsigned char *mapping;
    unsigned char *data;
    size_t page;
};

static struct guarded allocate_guarded(size_t page)
{
    unsigned char *mapping = mmap(NULL, 3 * page, PROT_NONE,
                                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED)
        fail_system("mmap guard pages");
    return (struct guarded){mapping, mapping + page, page};
}

static uint32_t pattern_value(unsigned pattern, size_t i)
{
    switch (pattern) {
    case 0: return UINT32_C(0xf1234567);
    case 1: return UINT32_MAX;
    case 2: return (uint32_t)(19 + 37 * i);
    default: return i % 2 == 0 ? UINT32_C(0x87654321) : UINT32_C(0xfedcba98);
    }
}

/* Closed mathematical sums independently define the expected answers; the
   tested accumulation algorithm is not reused as an oracle. */
static uint32_t pattern_sum(unsigned pattern, size_t n)
{
    switch (pattern) {
    case 0: return (uint32_t)((uint64_t)n * UINT32_C(0xf1234567));
    case 1: return (uint32_t)(UINT64_C(0x100000000) - n);
    case 2: return (uint32_t)(19 * n + 37 * (n * (n - 1) / 2));
    default:
        return (uint32_t)(((n + 1) / 2) * (uint64_t)UINT32_C(0x87654321)
                          + (n / 2) * (uint64_t)UINT32_C(0xfedcba98));
    }
}

/* The complete input ends at a guard page and is read-only at the call. For
   stride=2, only even entries belong to the answer; odd entries vary while
   even entries and the independent mathematical answer stay fixed. */
static const uint32_t *prepare(struct guarded *area, size_t n, size_t stride,
                               unsigned pattern, unsigned odd)
{
    if (n == 0)
        return (const uint32_t *)(area->data + area->page);
    if ((stride * n + 1) * sizeof(uint32_t) > area->page) {
        fprintf(stderr, "page too small for fixture\n");
        exit(2);
    }
    if (mprotect(area->data, area->page, PROT_READ | PROT_WRITE) != 0)
        fail_system("mprotect initialize");
    uint32_t *p = (uint32_t *)(area->data + area->page) - stride * n;
    p[-1] = UINT32_C(0xdeadbeef);
    for (size_t i = 0; i < n; ++i) {
        p[stride * i] = pattern_value(pattern, i);
        if (stride == 2) {
            switch (odd) {
            case 0: p[2 * i + 1] = 0; break;
            case 1: p[2 * i + 1] = UINT32_MAX; break;
            default: p[2 * i + 1] = (uint32_t)(UINT32_C(0x52abcd19) + 109 * i); break;
            }
        }
    }
    if (mprotect(area->data, area->page, PROT_READ) != 0)
        fail_system("mprotect readonly");
    return p;
}

static void release_guarded(struct guarded *area)
{
    if (munmap(area->mapping, 3 * area->page) != 0)
        fail_system("munmap guards");
}

static void suite(const void *code, const char *mode, size_t page)
{
    observe(code, NULL, 0, NULL, 0, 0, "zero/null");
    if (strcmp(mode, "early") == 0) {
        observe(code, NULL, 1, NULL, 0, 1, "first RET/nonzero");
        observe(code, NULL, SIZE_MAX, NULL, 0, 1, "first RET/full-width count");
        return;
    }
    struct guarded a = allocate_guarded(page);
    struct guarded b = allocate_guarded(page);
    const uint32_t *zero_a = prepare(&a, 0, 1, 0, 0);
    const uint32_t *zero_b = prepare(&b, 0, 1, 0, 0);
    observe(code, zero_a, 0, zero_b, 0, 0, "zero/guard");
    if (strcmp(mode, "stride") == 0) {
        static const size_t counts[] = {1, 2, 3, 7, 17, 63, 127, 255};
        for (size_t c = 0; c < sizeof counts / sizeof counts[0]; ++c) {
            size_t n = counts[c];
            for (unsigned pattern = 0; pattern < 4; ++pattern) {
                for (unsigned odd = 0; odd < 3; ++odd) {
                    const uint32_t *p = prepare(&a, n, 2, pattern, odd);
                    observe(code, p, n, zero_b, 0, pattern_sum(pattern, n),
                            "even-index sum/odd-word independence");
                }
            }
        }
    } else {
        static const size_t counts[] = {0, 1, 3, 17, 127, 255};
        for (size_t ca = 0; ca < sizeof counts / sizeof counts[0]; ++ca) {
            for (size_t cb = 0; cb < sizeof counts / sizeof counts[0]; ++cb) {
                size_t na = counts[ca], nb = counts[cb];
                for (unsigned pattern = 0; pattern < 4; ++pattern) {
                    unsigned other = (pattern + 1) % 4;
                    const uint32_t *pa = prepare(&a, na, 1, pattern, 0);
                    const uint32_t *pb = prepare(&b, nb, 1, other, 0);
                    uint32_t expected = (uint32_t)(pattern_sum(pattern, na)
                                                   + pattern_sum(other, nb));
                    observe(code, pa, na, pb, nb, expected, "two independent sums");
                }
            }
        }
        const uint32_t *pa = prepare(&a, 3, 1, 2, 0);
        observe(code, pa, 3, NULL, 0, 168, "second null/empty");
        const uint32_t *pb = prepare(&b, 3, 1, 2, 0);
        observe(code, NULL, 0, pb, 3, 168, "first null/empty");
    }
    release_guarded(&a);
    release_guarded(&b);
}

static int run_isolated(const void *code, const char *mode, size_t page,
                        int negative, const char *name)
{
    fflush(NULL);
    pid_t child = fork();
    if (child < 0)
        fail_system("fork");
    if (child == 0) {
        alarm(5);
        suite(code, mode, page);
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
        printf("NATIVE %s (%s): %s\n", negative ? "rejected owned mutant" : "observations passed",
               mode, name);
        return 0;
    }
    fprintf(stderr, "%s: unexpected native child status %d\n", name, status);
    return 1;
}

int main(int argc, char **argv)
{
    int negative = argc == 4 && strcmp(argv[1], "--expect-reject") == 0;
    if (negative) {
        --argc;
        ++argv;
    }
    if (argc != 3 || (strcmp(argv[1], "stride") != 0 && strcmp(argv[1], "pair") != 0
                     && strcmp(argv[1], "early") != 0)) {
        fprintf(stderr, "usage: %s [--expect-reject] stride|pair|early final-linked.bin\n", argv[0]);
        return 2;
    }
    struct rlimit no_core = {0, 0};
    if (setrlimit(RLIMIT_CORE, &no_core) != 0)
        fail_system("setrlimit");
    long page_value = sysconf(_SC_PAGESIZE);
    if (page_value <= 0)
        fail_system("sysconf page size");
    size_t page = (size_t)page_value;
    int fd = open(argv[2], O_RDONLY | O_CLOEXEC);
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
    int result = run_isolated(code, argv[1], page, negative, argv[2]);
    if (!negative) {
        result |= run_isolated((const void *)edsl_cfg_bad_high, argv[1], page, 1,
                               "nonzero upper RAX");
        result |= run_isolated((const void *)edsl_cfg_bad_saved, argv[1], page, 1,
                               "clobbered callee-saved R12");
    }
    if (munmap(code, page) != 0)
        fail_system("munmap final linked bytes");
    return result;
}
