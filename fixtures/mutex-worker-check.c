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

typedef uint32_t (*operation)(_Atomic uint32_t *, uint32_t *);

struct guarded_lock {
    uint32_t before;
    _Atomic uint32_t value;
    uint32_t after;
};
struct guarded_payload { uint32_t before, value, after; };
_Static_assert(sizeof(_Atomic uint32_t) == 4, "native profile needs four-byte atomics");
_Static_assert(offsetof(struct guarded_lock, value) == 4 &&
               offsetof(struct guarded_lock, after) == 8,
               "both lock guards must be adjacent");
_Static_assert(offsetof(struct guarded_payload, value) == 4 &&
               offsetof(struct guarded_payload, after) == 8,
               "both payload guards must be adjacent");

static const uint32_t guard_before = 0x18d75b6a, guard_after = 0xa5b6c7d8;

static int observe(operation function, uint32_t initial, uint64_t requests)
{
    struct guarded_lock lock = {.before = guard_before, .after = guard_after};
    atomic_init(&lock.value, 0);
    struct guarded_payload payload = {guard_before, initial, guard_after};
    for (uint64_t request = 0; request < requests; ++request) {
        if (function(&lock.value, &payload.value) || atomic_load(&lock.value)) {
            fputs("Sequential mutex worker did not return zero with an unlocked lock\n", stderr);
            return 1;
        }
        /* This is the public request contract, independent of the body, its
         * intermediate store values, and any machine event log. */
        uint32_t expected = (uint32_t)((uint64_t)initial + 2 * (request + 1));
        if (payload.value != expected || (payload.value & 1) ||
            lock.before != guard_before || lock.after != guard_after ||
            payload.before != guard_before || payload.after != guard_after) {
            fprintf(stderr, "Sequential mutex payload contract failed: initial=%u request=%llu\n",
                    initial, (unsigned long long)request);
            return 1;
        }
    }
    return 0;
}

struct worker {
    operation function;
    _Atomic uint32_t *lock;
    uint32_t *payload;
    _Atomic int *start;
    uint64_t requests;
    int failed;
};

static void *run_worker(void *argument)
{
    struct worker *worker = argument;
    while (!atomic_load_explicit(worker->start, memory_order_acquire)) sched_yield();
    for (uint64_t request = 0; request < worker->requests; ++request)
        if (worker->function(worker->lock, worker->payload)) worker->failed = 1;
    return NULL;
}

static int contended(operation function, uint32_t initial)
{
    static const uint64_t requests[] = {0, 1, 2, 17, 128, 1024, 4001, 8192};
    enum { count = sizeof requests / sizeof requests[0] };
    struct guarded_lock lock = {.before = guard_before, .after = guard_after};
    atomic_init(&lock.value, 0);
    struct guarded_payload payload = {guard_before, initial, guard_after};
    _Atomic int start = 0;
    pthread_t threads[count];
    struct worker workers[count];
    uint64_t total = 0;
    for (size_t index = 0; index < count; ++index) {
        total += requests[index];
        workers[index] = (struct worker){function, &lock.value, &payload.value,
                                         &start, requests[index], 0};
        if (pthread_create(&threads[index], NULL, run_worker, &workers[index])) _exit(2);
    }
    atomic_store_explicit(&start, 1, memory_order_release);
    int failed = 0;
    for (size_t index = 0; index < count; ++index) {
        if (pthread_join(threads[index], NULL)) _exit(2);
        if (workers[index].failed) failed = 1;
    }
    uint32_t expected = (uint32_t)((uint64_t)initial + 2 * total);
    if (atomic_load(&lock.value) || payload.value != expected || (payload.value & 1) ||
        lock.before != guard_before || lock.after != guard_after ||
        payload.before != guard_before || payload.after != guard_after) failed = 1;
    if (failed) fprintf(stderr, "Contended mutex payload contract failed: initial=%u\n", initial);
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
    long page = sysconf(_SC_PAGESIZE);
    if (failed || size != 37 || page < 64) return 2;
    void *code = mmap(NULL, (size_t)page, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (code == MAP_FAILED) return 2;
    memcpy(code, bytes, size);
    if (mprotect(code, (size_t)page, PROT_READ | PROT_EXEC)) return 2;
    operation function = (operation)code;
    static const uint32_t initials[] = {0, 2, 0xfffe, 0x7ffffffe, 0xffffff00, 0xfffffffe};
    static const uint64_t requests[] = {1, 2, 17, 256, 1025};
    for (size_t a = 0; a < sizeof initials / sizeof initials[0]; ++a)
        for (size_t b = 0; b < sizeof requests / sizeof requests[0]; ++b)
            if (observe(function, initials[a], requests[b])) return 1;
    for (unsigned int round = 0; round < 4; ++round)
        if (contended(function, round % 2 ? 0xffffff00 : 0)) return 1;
    if (munmap(code, (size_t)page)) return 2;
    puts("Native mutex worker observations passed: 30 sequential workloads, four eight-thread workloads, zero returns, unlocked completion, even closed values, modular totals and adjacent guards");
    return 0;
}
