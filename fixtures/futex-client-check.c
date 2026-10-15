/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <errno.h>
#include <inttypes.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdalign.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern long edsl_futex_client_publish(volatile uint32_t *word,
                                      volatile uint32_t *payload);
extern long edsl_futex_client_wait0(volatile uint32_t *word);
_Static_assert(sizeof(long) == 8, "full raw Linux x86-64 result required");
_Static_assert(sizeof(uint32_t) == 4, "four-byte futex and payload required");

/* Only the assembly writes W/P while a waiter runs. C observes them after
   pthread_join, avoiding an invented C synchronization contract for XCHG. */
struct observation {
    alignas(4) volatile uint32_t word;
    alignas(4) volatile uint32_t payload;
    atomic_uint attempting;
    long wait_raw;
};

static void watchdog(int signal_number) {
    (void)signal_number;
    static const char message[] =
        "INCONCLUSIVE: native publication observer reached its scheduling watchdog\n";
    ssize_t written = write(STDERR_FILENO, message, sizeof(message) - 1);
    (void)written;
    _exit(3);
}

static int final_words(const struct observation *state) {
    if (state->payload != UINT32_C(0x11223344) || state->word != UINT32_C(1)) {
        fprintf(stderr, "publication observation: P=0x%08" PRIx32
                ", W=0x%08" PRIx32 "; expected P=0x11223344, W=1\n",
                state->payload, state->word);
        return 0;
    }
    return 1;
}

static void *wait_thread(void *argument) {
    struct observation *state = argument;
    /* This handshake reports a userspace attempt, never queue membership. */
    atomic_store_explicit(&state->attempting, 1, memory_order_release);
    state->wait_raw = edsl_futex_client_wait0(&state->word);
    return NULL;
}

int main(int argc, char **argv) {
    int race = 1;
    if (argc == 2 && strcmp(argv[1], "--no-race") == 0) race = 0;
    else if (argc != 1) {
        fputs("usage: native-check [--no-race]\n", stderr);
        return 2;
    }
    struct sigaction action = { .sa_handler = watchdog };
    if (sigemptyset(&action.sa_mask) != 0 || sigaction(SIGALRM, &action, NULL) != 0) {
        perror("sigaction");
        return 1;
    }
    alarm(10);

    struct observation empty = { .word = 0, .payload = 0, .attempting = 0 };
    long raw = edsl_futex_client_publish(&empty.word, &empty.payload);
    if (raw != 0 || !final_words(&empty)) {
        fprintf(stderr, "no-waiter publication: raw RAX 0x%016lx, expected zero\n",
                (unsigned long)raw);
        return 1;
    }
    puts("OBSERVED no-waiter publication: P=0x11223344, W=1, raw WAKE count=0");

    if (race) {
        unsigned zero = 0, mismatch = 0, selected = 0;
        for (unsigned attempt = 0; attempt < 32; ++attempt) {
            /* Storage stays at a stable address until the actual join. */
            struct observation state = {
                .word = 0, .payload = 0, .attempting = 0, .wait_raw = -999
            };
            pthread_t waiter;
            int error = pthread_create(&waiter, NULL, wait_thread, &state);
            if (error != 0) {
                fprintf(stderr, "pthread_create: %s\n", strerror(error));
                return 1;
            }
            for (unsigned spin = 0; spin < 10000; ++spin) {
                if (atomic_load_explicit(&state.attempting, memory_order_acquire)) break;
                sched_yield();
            }
            long wake_raw = edsl_futex_client_publish(&state.word, &state.payload);
            error = pthread_join(waiter, NULL);
            if (error != 0) {
                fprintf(stderr, "pthread_join: %s\n", strerror(error));
                return 1;
            }
            /* Independent observable contract: one WAKE, at most one waiter;
               WAIT may have been selected, returned spuriously, or mismatched. */
            if ((wake_raw != 0 && wake_raw != 1) ||
                (state.wait_raw != 0 && state.wait_raw != -EAGAIN) || !final_words(&state)) {
                fprintf(stderr, "race: full raw WAKE=0x%016lx, WAIT=0x%016lx\n",
                        (unsigned long)wake_raw, (unsigned long)state.wait_raw);
                return 1;
            }
            selected += wake_raw == 1;
            zero += state.wait_raw == 0;
            mismatch += state.wait_raw == -EAGAIN;
        }
        printf("OBSERVED 32 bounded races: WAIT zero=%u, -EAGAIN=%u; WAKE one=%u; "
               "P=0x11223344 and W=1 after every join\n", zero, mismatch, selected);
    }
    alarm(0);
    puts("Native trampoline, pthread and installed-kernel conformance are external evidence; "
         "these observations prove no scheduling progress");
    return 0;
}
