/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

typedef uint32_t (*operation)(_Atomic uint32_t *, uint32_t);
extern uint32_t edsl_observe_fetch_add(operation, _Atomic uint32_t *, uint32_t, uint64_t *);
enum { workers = 8, iterations = 100000, total = workers * iterations };
struct worker { operation function; _Atomic uint32_t *cell; _Atomic unsigned char *seen; int failed; };

static void *run_worker(void *argument)
{
    struct worker *worker = argument;
    for (unsigned int index = 0; index < iterations; ++index) {
        uint32_t old = worker->function(worker->cell, 1);
        if (old >= total || atomic_fetch_add_explicit(&worker->seen[old], 1, memory_order_relaxed) != 0) {
            worker->failed = 1;
            break;
        }
    }
    return NULL;
}

int main(int argc, char **argv)
{
    if (argc != 2) return 2;
    FILE *file = fopen(argv[1], "rb");
    if (!file) return 2;
    unsigned char bytes[8];
    size_t size = fread(bytes, 1, sizeof bytes, file);
    int failed = ferror(file);
    fclose(file);
    if (failed || size != 7) return 2;
    long page = sysconf(_SC_PAGESIZE);
    if (page < 64) return 2;
    void *code = mmap(NULL, (size_t)page, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (code == MAP_FAILED) return 2;
    memcpy(code, bytes, size);
    if (mprotect(code, (size_t)page, PROT_READ | PROT_EXEC)) return 2;
    operation function = (operation)code;
    struct { _Atomic uint32_t cell; uint32_t guard; } data;
    atomic_init(&data.cell, 0);
    data.guard = 0xa5b6c7d8;
    /* Hardware observations become independent expected values for Lean.
     * This probe contains no implementation of the modeled flag formulas. */
    puts("import EDSL.X86.Flags\nimport EDSL.Audit\nopen EDSL.X86\nnamespace EDSL.Tests.NativeFetchAdd");
    static const uint32_t boundaries[] = {0, 1, 0xf, 0x10, 0x7f, 0x80, 0xff, 0x100,
        0x7fffffff, 0x80000000, 0xfffffff0, 0xffffffff};
    for (size_t a = 0; a < sizeof boundaries / sizeof boundaries[0]; ++a) {
        for (size_t b = 0; b < sizeof boundaries / sizeof boundaries[0]; ++b) {
            uint32_t before = boundaries[a], delta = boundaries[b];
            atomic_store(&data.cell, before);
            uint64_t flags = 0;
            uint32_t old = edsl_observe_fetch_add(function, &data.cell, delta, &flags);
            uint32_t after = atomic_load(&data.cell);
            if (old != before || after != (uint32_t)((uint64_t)before + delta) || data.guard != 0xa5b6c7d8)
                return 1;
            printf("example : addFlags32 0 %u %u &&& arithmeticFlagMask = %llu := by decide\n",
                   before, delta, (unsigned long long)(flags & 0x8d5));
        }
    }
    puts("end EDSL.Tests.NativeFetchAdd\n#audit_edsl");
    _Atomic unsigned char *seen = calloc(total, sizeof *seen);
    if (!seen) return 2;
    for (unsigned int index = 0; index < total; ++index) atomic_init(&seen[index], 0);
    pthread_t threads[workers];
    struct worker state[workers];
    atomic_store(&data.cell, 0);
    for (unsigned int index = 0; index < workers; ++index) {
        state[index] = (struct worker){function, &data.cell, seen, 0};
        if (pthread_create(&threads[index], NULL, run_worker, &state[index])) _exit(2);
    }
    int result = 0;
    for (unsigned int index = 0; index < workers; ++index) {
        if (pthread_join(threads[index], NULL)) _exit(2);
        if (state[index].failed) result = 1;
    }
    if (atomic_load(&data.cell) != total || data.guard != 0xa5b6c7d8) result = 1;
    for (unsigned int index = 0; index < total; ++index)
        if (atomic_load_explicit(&seen[index], memory_order_relaxed) != 1) result = 1;
    free(seen);
    if (munmap(code, (size_t)page)) return 2;
    return result;
}
