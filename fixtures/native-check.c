/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <stdint.h>
#include <stdatomic.h>
#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include <sys/mman.h>
#include <unistd.h>

/* Execute only owned fixtures after their Lean certificates pass. */
static int check_increment(void *mapping)
{
    uint32_t (*function)(uint32_t) = (uint32_t (*)(uint32_t))mapping;
    static const struct { uint32_t input, output; } cases[] = {
        {0x00000000u, 0x00000001u},
        {0x7fffffffu, 0x80000000u},
        {0xfffffffeu, 0xffffffffu},
        {0xffffffffu, 0x00000000u},
    };
    for (size_t i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
        if (function(cases[i].input) != cases[i].output) {
            fprintf(stderr, "native increment mismatch at input 0x%08x\n", cases[i].input);
            return 1;
        }
    }
    return 0;
}

static int check_increment_loop(void *mapping)
{
    uint64_t (*function)(uint64_t, uint64_t, uint64_t, uint64_t) =
        (uint64_t (*)(uint64_t, uint64_t, uint64_t, uint64_t))mapping;
    static const struct { uint64_t input, count, output; } cases[] = {
        {0xdeadbeefffffffffull, 0, 0xffffffffull},
        {0x12345678ffffffffull, 1, 0},
        {0xfffffffeull, 2, 0},
        {0xffffff00ull, 257, 1},
        {0x7fffffffull, 1, 0x80000000ull},
        {0xffffffffull, 65537, 65536},
    };
    for (size_t i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
        if (function(cases[i].input, 0xbad, 0xfaded, cases[i].count) != cases[i].output) {
            fprintf(stderr, "native counted increment mismatch at case %zu\n", i);
            return 1;
        }
    }
    return 0;
}

static int check_memory(void *mapping, int store, size_t page_size)
{
    unsigned char *data = mmap(NULL, page_size, PROT_READ | PROT_WRITE,
                               MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (data == MAP_FAILED)
        return 2;
    static const struct { uint32_t word; unsigned char bytes[4]; } cases[] = {
        {0x11223344u, {0x44, 0x33, 0x22, 0x11}},
        {0x89abcdefu, {0xef, 0xcd, 0xab, 0x89}},
        {0x00000000u, {0x00, 0x00, 0x00, 0x00}},
        {0xffffffffu, {0xff, 0xff, 0xff, 0xff}},
    };
    uint32_t (*load_function)(const uint32_t *) =
        (uint32_t (*)(const uint32_t *))mapping;
    void (*store_function)(uint32_t *, uint32_t) =
        (void (*)(uint32_t *, uint32_t))mapping;
    int result = 0;
    for (size_t i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
        if (mprotect(data, page_size, PROT_READ | PROT_WRITE) != 0) {
            result = 2;
            break;
        }
        memset(data, 0xa5, 16);
        if (store) {
            store_function((uint32_t *)(data + 8), cases[i].word);
        } else {
            memcpy(data + 8, cases[i].bytes, 4);
            if (mprotect(data, page_size, PROT_READ) != 0) {
                result = 2;
                break;
            }
            if (load_function((const uint32_t *)(data + 8)) != cases[i].word) {
                fprintf(stderr, "native load byte-order/value mismatch\n");
                result = 1;
                break;
            }
        }
        for (size_t byte = 0; byte < 16; ++byte) {
            unsigned char expected = byte >= 8 && byte < 12 ? cases[i].bytes[byte - 8] : 0xa5;
            if (data[byte] != expected) {
                fprintf(stderr, "native %s memory footprint mismatch at byte %zu\n",
                        store ? "store" : "load", byte);
                result = 1;
                break;
            }
        }
        if (result != 0)
            break;
    }
    if (munmap(data, page_size) != 0)
        return 2;
    return result;
}

typedef uint32_t (*exchange_function)(_Atomic uint32_t *, uint32_t);

enum { exchange_workers = 8, exchange_iterations = 100000 };

struct exchange_worker {
    exchange_function function;
    _Atomic uint32_t *cell;
    pthread_barrier_t *start;
    uint32_t token;
    int status;
};

static void *exchange_worker_main(void *argument)
{
    struct exchange_worker *worker = argument;
    int status = pthread_barrier_wait(worker->start);
    if (status != 0 && status != PTHREAD_BARRIER_SERIAL_THREAD) {
        worker->status = status;
        return NULL;
    }
    for (unsigned int iteration = 0; iteration < exchange_iterations; ++iteration)
        worker->token = worker->function(worker->cell, worker->token);
    return NULL;
}

/* Every swap moves one token between a thread and the shared cell. Once all
 * threads join, tokens 0..exchange_workers must still occur exactly once. A
 * separate load followed by a store can lose a token under this contention. */
static int check_exchange_concurrency(exchange_function function,
                                      _Atomic uint32_t *cell)
{
    pthread_t threads[exchange_workers];
    struct exchange_worker workers[exchange_workers];
    pthread_barrier_t start;
    if (pthread_barrier_init(&start, NULL, exchange_workers + 1) != 0)
        return 2;
    atomic_store_explicit(cell, 0, memory_order_seq_cst);
    for (unsigned int index = 0; index < exchange_workers; ++index) {
        workers[index] = (struct exchange_worker){function, cell, &start, index + 1, 0};
        if (pthread_create(&threads[index], NULL, exchange_worker_main, &workers[index]) != 0) {
            /* Created workers are waiting at the barrier. Process termination
             * releases their resources; do not return to unmap their cell. */
            fprintf(stderr, "native exchange worker creation failed\n");
            _exit(2);
        }
    }
    int status = pthread_barrier_wait(&start);
    if (status != 0 && status != PTHREAD_BARRIER_SERIAL_THREAD)
        _exit(2);
    int worker_failed = 0;
    for (unsigned int index = 0; index < exchange_workers; ++index) {
        if (pthread_join(threads[index], NULL) != 0)
            _exit(2);
        if (workers[index].status != 0)
            worker_failed = 1;
    }
    if (pthread_barrier_destroy(&start) != 0 || worker_failed)
        return 2;
    unsigned int counts[exchange_workers + 1] = {0};
    uint32_t final = atomic_load_explicit(cell, memory_order_seq_cst);
    if (final > exchange_workers) {
        fprintf(stderr, "native exchange produced an invalid shared token\n");
        return 1;
    }
    ++counts[final];
    for (unsigned int index = 0; index < exchange_workers; ++index) {
        if (workers[index].token > exchange_workers) {
            fprintf(stderr, "native exchange produced an invalid worker token\n");
            return 1;
        }
        ++counts[workers[index].token];
    }
    for (unsigned int token = 0; token <= exchange_workers; ++token) {
        if (counts[token] != 1) {
            fprintf(stderr, "native exchange lost or duplicated token %u\n", token);
            return 1;
        }
    }
    return 0;
}

static int check_exchange(void *mapping, size_t page_size)
{
    unsigned char *data = mmap(NULL, page_size, PROT_READ | PROT_WRITE,
                               MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (data == MAP_FAILED)
        return 2;
    _Atomic uint32_t *cell = (_Atomic uint32_t *)(data + 8);
    exchange_function function = (exchange_function)mapping;
    static const struct {
        uint32_t before, after;
        unsigned char after_bytes[4];
    } cases[] = {
        {0x11223344u, 0x89abcdefu, {0xef, 0xcd, 0xab, 0x89}},
        {0x80000000u, 0x00000000u, {0x00, 0x00, 0x00, 0x00}},
        {0x00000000u, 0xffffffffu, {0xff, 0xff, 0xff, 0xff}},
        {0xffffffffu, 0x10203040u, {0x40, 0x30, 0x20, 0x10}},
    };
    int result = 0;
    for (size_t index = 0; index < sizeof cases / sizeof cases[0]; ++index) {
        memset(data, 0xa5, 64);
        atomic_init(cell, cases[index].before);
        if (function(cell, cases[index].after) != cases[index].before) {
            fprintf(stderr, "native exchange returned the wrong old value\n");
            result = 1;
            break;
        }
        for (size_t byte = 0; byte < 64; ++byte) {
            unsigned char expected = byte >= 8 && byte < 12
                ? cases[index].after_bytes[byte - 8] : 0xa5;
            if (data[byte] != expected) {
                fprintf(stderr, "native exchange memory footprint mismatch at byte %zu\n", byte);
                result = 1;
                break;
            }
        }
        if (result != 0)
            break;
    }
    if (result == 0)
        result = check_exchange_concurrency(function, cell);
    if (result == 0) {
        for (size_t byte = 0; byte < 64; ++byte) {
            if ((byte < 8 || byte >= 12) && data[byte] != 0xa5) {
                fprintf(stderr, "native concurrent exchange corrupted guard byte %zu\n", byte);
                result = 1;
                break;
            }
        }
    }
    if (munmap(data, page_size) != 0)
        return 2;
    return result;
}

int main(int argc, char **argv)
{
    const char *profile = argc == 3 ? argv[1] : "increment";
    if ((argc != 2 && argc != 3) ||
        (strcmp(profile, "increment") != 0 && strcmp(profile, "increment-loop") != 0 && strcmp(profile, "load32") != 0 &&
         strcmp(profile, "store32") != 0 && strcmp(profile, "exchange32") != 0))
        return 2;
    int memory_profile = strcmp(profile, "load32") == 0 || strcmp(profile, "store32") == 0;
    int loop_profile = strcmp(profile, "increment-loop") == 0;
    int exchange_profile = strcmp(profile, "exchange32") == 0;
    size_t expected_size = memory_profile ? 3 : loop_profile ? 10 : exchange_profile ? 5 : 4;
    FILE *file = fopen(argv[argc - 1], "rb");
    if (!file)
        return 2;
    unsigned char bytes[16];
    size_t size = fread(bytes, 1, sizeof bytes, file);
    int extra = fgetc(file);
    int failed = ferror(file);
    fclose(file);
    if (failed || size != expected_size || extra != EOF)
        return 2;
    long page_size = sysconf(_SC_PAGESIZE);
    if (page_size < 64)
        return 2;
    void *mapping = mmap(NULL, (size_t)page_size, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED)
        return 2;
    memcpy(mapping, bytes, size);
    if (mprotect(mapping, (size_t)page_size, PROT_READ | PROT_EXEC) != 0) {
        munmap(mapping, (size_t)page_size);
        return 2;
    }
    int result = memory_profile
        ? check_memory(mapping, strcmp(profile, "store32") == 0, (size_t)page_size)
        : exchange_profile ? check_exchange(mapping, (size_t)page_size)
        : loop_profile ? check_increment_loop(mapping) : check_increment(mapping);
    if (munmap(mapping, (size_t)page_size) != 0)
        return 2;
    return result;
}
