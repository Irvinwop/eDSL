/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

typedef void (*operation)(void);
extern uint32_t edsl_run_counter(operation, _Atomic uint32_t *, uint64_t, uint64_t *);

struct guarded_counter {
    uint32_t before;
    _Atomic uint32_t cell;
    uint32_t after;
};
_Static_assert(sizeof(_Atomic uint32_t) == 4, "native profile needs a four-byte atomic word");
_Static_assert(offsetof(struct guarded_counter, cell) == 4, "preceding guard must be adjacent");
_Static_assert(offsetof(struct guarded_counter, after) == 8, "following guard must be adjacent");

static const uint32_t before_guard = 0x18d75b6a;
static const uint32_t after_guard = 0xa5b6c7d8;

static int observe(operation function, uint32_t initial, uint64_t count)
{
    struct guarded_counter data = {.before = before_guard, .after = after_guard};
    atomic_init(&data.cell, initial);
    uint64_t remaining = UINT64_MAX;
    uint32_t result = edsl_run_counter(function, &data.cell, count, &remaining);
    /* The expected result comes from the published count, rather than machine
     * events or a simulation of the instruction sequence. */
    uint32_t expected = (uint32_t)((uint64_t)initial + count);
    if (result || remaining || atomic_load(&data.cell) != expected ||
        data.before != before_guard || data.after != after_guard) {
        fprintf(stderr, "Sequential counter contract failed: initial=%u count=%llu\n",
                initial, (unsigned long long)count);
        return 1;
    }
    return 0;
}

struct worker {
    operation function;
    _Atomic uint32_t *cell;
    _Atomic int *start;
    uint64_t count;
    uint64_t remaining;
    uint32_t result;
};

static void *run_worker(void *argument)
{
    struct worker *worker = argument;
    while (!atomic_load_explicit(worker->start, memory_order_acquire)) sched_yield();
    worker->result = edsl_run_counter(worker->function, worker->cell,
                                      worker->count, &worker->remaining);
    return NULL;
}

static int contended(operation function, uint32_t initial)
{
    static const uint64_t requests[] = {0, 1, 2, 17, 1024, 32769, 100003, 262147};
    enum { workers = sizeof requests / sizeof requests[0] };
    struct guarded_counter data = {.before = before_guard, .after = after_guard};
    atomic_init(&data.cell, initial);
    _Atomic int start = 0;
    pthread_t threads[workers];
    struct worker state[workers];
    uint64_t expected = initial;
    for (size_t index = 0; index < workers; ++index) {
        expected += requests[index];
        state[index] = (struct worker){function, &data.cell, &start, requests[index], UINT64_MAX, UINT32_MAX};
        if (pthread_create(&threads[index], NULL, run_worker, &state[index])) _exit(2);
    }
    atomic_store_explicit(&start, 1, memory_order_release);
    int failed = 0;
    for (size_t index = 0; index < workers; ++index) {
        if (pthread_join(threads[index], NULL)) _exit(2);
        if (state[index].result || state[index].remaining) failed = 1;
    }
    if (atomic_load(&data.cell) != (uint32_t)expected ||
        data.before != before_guard || data.after != after_guard) failed = 1;
    if (failed) fprintf(stderr, "Contended counter contract failed: initial=%u\n", initial);
    return failed;
}

int main(int argc, char **argv)
{
    if (argc != 2) return 2;
    FILE *file = fopen(argv[1], "rb");
    if (!file) return 2;
    unsigned char bytes[64];
    size_t size = fread(bytes, 1, sizeof bytes, file);
    int failed = ferror(file);
    fclose(file);
    if (failed || size != 19) return 2;
    long page = sysconf(_SC_PAGESIZE);
    if (page < 64) return 2;
    void *code = mmap(NULL, (size_t)page, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (code == MAP_FAILED) return 2;
    memcpy(code, bytes, size);
    if (mprotect(code, (size_t)page, PROT_READ | PROT_EXEC)) return 2;
    operation function = (operation)code;

    static const uint32_t initials[] = {0, 1, 0x7fffffff, 0xffff0000, 0xfffffffe, 0xffffffff};
    static const uint64_t counts[] = {0, 1, 2, 3, 17, 256, 65537};
    for (size_t a = 0; a < sizeof initials / sizeof initials[0]; ++a)
        for (size_t b = 0; b < sizeof counts / sizeof counts[0]; ++b)
            if (observe(function, initials[a], counts[b])) return 1;
    for (unsigned int round = 0; round < 4; ++round)
        if (contended(function, round % 2 ? 0xffffff00 : 0)) return 1;

    if (munmap(code, (size_t)page)) return 2;
    puts("Native counter observations passed: 42 sequential requests, four eight-thread workloads, guards, zero returns and exhausted RCX");
    return 0;
}
