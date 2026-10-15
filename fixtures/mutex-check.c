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

typedef uint32_t (*exchange_fn)(_Atomic uint32_t *, uint32_t);
typedef uint32_t (*load_fn)(const uint32_t *);
typedef void (*store_fn)(uint32_t *, uint32_t);

struct code { void *base; size_t size; };
static struct code read_code(const char *path, size_t expected)
{
    FILE *file = fopen(path, "rb");
    if (!file) exit(2);
    unsigned char bytes[64];
    size_t count = fread(bytes, 1, sizeof bytes, file);
    int failed = ferror(file);
    fclose(file);
    long page = sysconf(_SC_PAGESIZE);
    if (failed || count != expected || page < 64) exit(2);
    void *base = mmap(NULL, (size_t)page, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (base == MAP_FAILED) exit(2);
    memcpy(base, bytes, count);
    if (mprotect(base, (size_t)page, PROT_READ | PROT_EXEC)) exit(2);
    return (struct code){base, (size_t)page};
}

struct payload { uint32_t before, value, after; };
_Static_assert(offsetof(struct payload, value) == 4 && offsetof(struct payload, after) == 8,
               "both native payload guards must be adjacent");
static const uint32_t guard_before = 0x18d75b6a, guard_after = 0xa5b6c7d8;

struct worker {
    exchange_fn exchange;
    load_fn load;
    store_fn store;
    _Atomic uint32_t *lock;
    struct payload *data;
    _Atomic int *start;
    _Atomic int *inside;
    _Atomic int *failed;
    unsigned int requests;
};

static void *run_worker(void *argument)
{
    struct worker *worker = argument;
    while (!atomic_load_explicit(worker->start, memory_order_acquire)) sched_yield();
    for (unsigned int request = 0; request < worker->requests; ++request) {
        while (worker->exchange(worker->lock, 1) != 0) sched_yield();
        if (atomic_fetch_add(worker->inside, 1) != 0) atomic_store(worker->failed, 1);
        uint32_t old = worker->load(&worker->data->value);
        if (old & 1) atomic_store(worker->failed, 1);
        /* Open the even invariant, yield while holding it open, then restore it.
         * The independent expected total counts two per published request. */
        worker->store(&worker->data->value, old + 1);
        if ((request & 31) == 0) sched_yield();
        worker->store(&worker->data->value, old + 2);
        if (atomic_fetch_sub(worker->inside, 1) != 1) atomic_store(worker->failed, 1);
        if (worker->exchange(worker->lock, 0) != 1) atomic_store(worker->failed, 1);
    }
    return NULL;
}

static int observe(exchange_fn exchange, load_fn load, store_fn store, uint32_t initial)
{
    static const unsigned int requests[] = {0, 1, 2, 17, 128, 1024, 4001, 8192};
    enum { count = sizeof requests / sizeof requests[0] };
    _Alignas(64) _Atomic uint32_t lock = 0;
    struct payload data = {guard_before, initial, guard_after};
    _Atomic int start = 0, inside = 0, failed = 0;
    pthread_t threads[count];
    struct worker workers[count];
    uint64_t expected = initial;
    for (size_t index = 0; index < count; ++index) {
        expected += 2 * (uint64_t)requests[index];
        workers[index] = (struct worker){exchange, load, store, &lock, &data,
                                         &start, &inside, &failed, requests[index]};
        if (pthread_create(&threads[index], NULL, run_worker, &workers[index])) _exit(2);
    }
    atomic_store_explicit(&start, 1, memory_order_release);
    for (size_t index = 0; index < count; ++index)
        if (pthread_join(threads[index], NULL)) _exit(2);
    if (atomic_load(&failed) || atomic_load(&inside) || atomic_load(&lock) ||
        data.value != (uint32_t)expected || data.before != guard_before || data.after != guard_after) {
        fputs("Native protected-payload contract failed\n", stderr);
        return 1;
    }
    return 0;
}

int main(int argc, char **argv)
{
    if (argc != 4) return 2;
    struct code exchange_code = read_code(argv[1], 5);
    struct code load_code = read_code(argv[2], 3);
    struct code store_code = read_code(argv[3], 3);
    exchange_fn exchange = (exchange_fn)exchange_code.base;
    load_fn load = (load_fn)load_code.base;
    store_fn store = (store_fn)store_code.base;
    _Atomic uint32_t lock = 0;
    if (exchange(&lock, 1) != 0 || exchange(&lock, 1) != 1 ||
        exchange(&lock, 0) != 1 || exchange(&lock, 1) != 0 || exchange(&lock, 0) != 1) return 1;
    static const uint32_t initial[] = {0, 2, 0x7ffffffe, 0xfffffffe};
    for (size_t index = 0; index < sizeof initial / sizeof initial[0]; ++index)
        if (observe(exchange, load, store, initial[index])) return 1;
    if (munmap(exchange_code.base, exchange_code.size) || munmap(load_code.base, load_code.size) ||
        munmap(store_code.base, store_code.size)) return 2;
    puts("Native mutex observations passed: busy/reacquire events, four eight-thread workloads, exclusive occupancy, even closed values, modular totals and payload guards");
    return 0;
}
