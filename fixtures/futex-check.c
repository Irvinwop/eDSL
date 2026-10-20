/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <inttypes.h>
#include <pthread.h>
#include <sched.h>
#include <stdalign.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

/* Assembly wrappers establish all six canonical syscall argument registers.
   The exact certified stubs are linked from the separately certified objects. */
extern long edsl_futex_wait(const volatile void *word, uint32_t expected);
extern long edsl_futex_wake(const volatile void *word);
_Static_assert(sizeof(long) == 8, "full raw Linux x86-64 result required");
_Static_assert(sizeof(atomic_uint) == 4, "four-byte futex storage required");
_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "native word must be lock-free");

static void require_raw(const char *name, long actual, long expected) {
    if (actual != expected) {
        fprintf(stderr, "%s: raw RAX 0x%016lx, expected 0x%016lx\n",
                name, (unsigned long)actual, (unsigned long)expected);
        exit(1);
    }
    printf("%s: raw RAX 0x%016lx\n", name, (unsigned long)actual);
}

struct observation {
    alignas(4) atomic_uint word;
    atomic_uint attempting;
    long raw;
};

static void *wait_thread(void *argument) {
    struct observation *state = argument;
    atomic_store_explicit(&state->attempting, 1, memory_order_release);
    state->raw = edsl_futex_wait(&state->word, 0);
    return NULL;
}

int main(void) {
    alignas(4) uint32_t word = UINT32_C(0xa5a55a5a);
    require_raw("mismatching WAIT_PRIVATE", edsl_futex_wait(&word, UINT32_C(0x12345678)), -11);
    require_raw("empty WAKE_PRIVATE/1", edsl_futex_wake(&word), 0);
    alignas(4) unsigned char unaligned[8] = {0};
    require_raw("misaligned WAIT_PRIVATE", edsl_futex_wait(unaligned + 1, 0), -22);
    require_raw("misaligned WAKE_PRIVATE/1", edsl_futex_wake(unaligned + 1), -22);
    long page_size = sysconf(_SC_PAGESIZE);
    if (page_size <= 0) { perror("sysconf"); return 1; }
    void *unreadable = mmap(NULL, (size_t)page_size, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (unreadable == MAP_FAILED) { perror("mmap"); return 1; }
    require_raw("aligned unreadable WAIT_PRIVATE", edsl_futex_wait(unreadable, 0), -14);
    if (munmap(unreadable, (size_t)page_size) != 0) { perror("munmap"); return 1; }

    /* The handshake identifies an attempt, never kernel queue membership.
       A positive kernel wake count is the independent observation of selection.
       Keep W=0 until that observation; no sleeps establish eligibility. */
    struct observation state = { .word = 0, .attempting = 0, .raw = -999 };
    pthread_t thread;
    if (pthread_create(&thread, NULL, wait_thread, &state) != 0) {
        fputs("pthread_create failed\n", stderr); return 1;
    }
    while (!atomic_load_explicit(&state.attempting, memory_order_acquire)) sched_yield();
    int selected = 0;
    for (unsigned attempt = 0; attempt < 100000; ++attempt) {
        long count = edsl_futex_wake(&state.word);
        if (count == 1) { selected = 1; break; }
        if (count != 0) { fputs("unexpected wake result\n", stderr); exit(1); }
        sched_yield();
    }
    if (!selected) {
        atomic_store_explicit(&state.word, 1, memory_order_relaxed);
        long cleanup_count = edsl_futex_wake(&state.word);
        if (cleanup_count != 0 && cleanup_count != 1) {
            fprintf(stderr, "unexpected cleanup wake count %ld\n", cleanup_count); return 1;
        }
    }
    if (pthread_join(thread, NULL) != 0) { fputs("pthread_join failed\n", stderr); return 1; }
    if (selected) {
        require_raw("selected waiter returns without predicate change", state.raw, 0);
        if (atomic_load_explicit(&state.word, memory_order_relaxed) != 0) {
            fputs("wake changed futex predicate\n", stderr); return 1;
        }
        puts("OBSERVED WAKE_PRIVATE/1 selected one waiter while W remained zero");
    } else {
        if (state.raw != 0 && state.raw != -11) {
            fprintf(stderr, "unexpected bounded-attempt result %ld\n", state.raw); return 1;
        }
        puts("INCONCLUSIVE: bounded scheduling race produced no positive wake observation");
    }
    puts("Native observations are installed-kernel evidence, not kernel or progress proofs");
    return 0;
}
