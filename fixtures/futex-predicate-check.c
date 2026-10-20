#define _GNU_SOURCE
#include <errno.h>
#include <inttypes.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdalign.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#if defined(__linux__) && defined(__x86_64__)
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/types.h>
#include <sys/user.h>
#include <sys/wait.h>
#endif

struct registers {
    uint64_t rax, rbx, rcx, rdx, rsi, rdi, rbp;
    uint64_t r8, r9, r10, r11, r12, r13, r14, r15;
};

struct frame {
    struct registers returned;
    uint64_t rsp_before, rsp_after, return_before, return_after;
    uint64_t flags_before, flags_after, word, payload;
    uint64_t stack_before[4], stack_after[4];
    uint64_t red_before[4], red_after[4];
    struct registers entered;
};

extern const unsigned char edsl_futex_predicate_wait_stub[];
extern const unsigned char edsl_futex_predicate_no_recheck_stub[];
extern const unsigned char edsl_futex_publish_stub[];
extern void edsl_futex_predicate_probe(const void *function,
                                     volatile uint32_t *word,
                                     volatile uint32_t *payload,
                                     struct frame *frame, uintptr_t input_rsi);
extern long edsl_futex_predicate_wake_one(volatile uint32_t *word);

_Static_assert(sizeof(long) == 8, "full raw result required");
_Static_assert(sizeof(uint32_t) == 4, "four-byte storage required");
_Static_assert(sizeof(struct registers) == 120, "register assembly layout");
_Static_assert(offsetof(struct frame, rsp_before) == 120, "stack assembly layout");
_Static_assert(offsetof(struct frame, flags_before) == 152, "flags assembly layout");
_Static_assert(offsetof(struct frame, stack_before) == 184, "frame assembly layout");
_Static_assert(offsetof(struct frame, red_before) == 248, "red-zone assembly layout");
_Static_assert(offsetof(struct frame, entered) == 312, "entry assembly layout");
_Static_assert(sizeof(struct frame) == 432, "capture assembly layout");

static const uintptr_t wait_input_rsi = UINT64_C(0xdeadbeefcafef00d);
static const uint32_t published_payload = UINT32_C(0x11223344);

struct storage {
    uint64_t guard_before[2];
    alignas(4) volatile uint32_t word;
    alignas(4) volatile uint32_t payload;
    uint64_t guard_after[2];
};

struct waiter {
    struct storage *storage;
    const void *function;
    atomic_uint attempting, done;
    struct frame frame;
};

static void watchdog(int signal_number) {
    (void)signal_number;
    static const char message[] =
        "INCONCLUSIVE: native scheduling/trace watchdog; formal=NOTRUN grading=NOTRUN\n";
    ssize_t written = write(STDERR_FILENO, message, sizeof(message) - 1);
    (void)written;
    _exit(3);
}

static void initialize_storage(struct storage *storage, uint32_t word) {
    *storage = (struct storage){
        .guard_before = { UINT64_C(0x1020304050607080), UINT64_C(0x9182736455463728) },
        .word = word,
        .payload = word ? published_payload : 0,
        .guard_after = { UINT64_C(0xf0e0d0c0b0a09080), UINT64_C(0xabcdefabcdefabcd) }
    };
}

static int storage_frame(const struct storage *before, const struct storage *after) {
    if (memcmp(before->guard_before, after->guard_before, sizeof(before->guard_before)) ||
        memcmp(before->guard_after, after->guard_after, sizeof(before->guard_after))) {
        fputs("CONTRACT-FAIL neighboring RAM changed\n", stderr);
        return 0;
    }
    return 1;
}

static void print_registers(const char *label, const struct registers *registers) {
    printf("%s RAX=%016" PRIx64 " RBX=%016" PRIx64 " RCX=%016" PRIx64
           " RDX=%016" PRIx64 " RSI=%016" PRIx64 " RDI=%016" PRIx64
           " RBP=%016" PRIx64 " R8=%016" PRIx64 " R9=%016" PRIx64
           " R10=%016" PRIx64 " R11=%016" PRIx64 " R12=%016" PRIx64
           " R13=%016" PRIx64 " R14=%016" PRIx64 " R15=%016" PRIx64 "\n",
           label, registers->rax, registers->rbx, registers->rcx, registers->rdx,
           registers->rsi, registers->rdi, registers->rbp, registers->r8, registers->r9,
           registers->r10, registers->r11, registers->r12, registers->r13,
           registers->r14, registers->r15);
}

static void print_frame(const char *label, const struct frame *frame) {
    printf("FRAME %s W=%016" PRIx64 " P=%016" PRIx64
           " RSP=%016" PRIx64 "->%016" PRIx64
           " RET=%016" PRIx64 "->%016" PRIx64
           " RFLAGS=%016" PRIx64 "->%016" PRIx64 "\n", label,
           frame->word, frame->payload, frame->rsp_before, frame->rsp_after,
           frame->return_before, frame->return_after, frame->flags_before, frame->flags_after);
    print_registers("ENTRY", &frame->entered);
    print_registers("RETURN", &frame->returned);
    for (unsigned index = 0; index < 4; ++index) {
        printf("STACK %u upper=%016" PRIx64 "->%016" PRIx64
               " red=%016" PRIx64 "->%016" PRIx64 "\n", index,
               frame->stack_before[index], frame->stack_after[index],
               frame->red_before[index], frame->red_after[index]);
    }
}

static int common_frame(const struct frame *frame, const struct storage *storage) {
    const struct registers *before = &frame->entered;
    const struct registers *after = &frame->returned;
    if (before->rdi != (uintptr_t)&storage->word || before->rdx != 0 || before->r10 != 0 ||
        before->r8 != 0 || before->r9 != 0 ||
        after->rbx != before->rbx || after->rbp != before->rbp ||
        after->rdi != before->rdi || after->r8 != before->r8 || after->r9 != before->r9 ||
        after->r10 != before->r10 || after->r12 != before->r12 ||
        after->r13 != before->r13 || after->r14 != before->r14 || after->r15 != before->r15 ||
        frame->rsp_before != frame->rsp_after || (frame->rsp_before & 15) != 0 ||
        frame->return_before != frame->return_after ||
        memcmp(frame->stack_before, frame->stack_after, sizeof(frame->stack_before)) ||
        memcmp(frame->red_before, frame->red_after, sizeof(frame->red_before)) ||
        (frame->flags_after & UINT64_C(0x400)) != 0) {
        fputs("CONTRACT-FAIL register/return/stack frame\n", stderr);
        return 0;
    }
    return 1;
}

static int waiter_frame(const struct frame *frame, const struct storage *storage,
                        const void *function, int must_wait) {
    if (frame->word == 0) {
        fputs("CONTRACT-FAIL predicate remained zero at loop return\n", stderr);
        return 0;
    }
    if (!common_frame(frame, storage) || frame->returned.rax != 1 ||
        frame->returned.rdx != frame->entered.rdx || frame->word != 1 ||
        frame->payload != published_payload || storage->word != 1 ||
        storage->payload != published_payload || (frame->flags_after & UINT64_C(0x8d5)) != 0) {
        fputs("CONTRACT-FAIL published predicate/payload/full raw return\n", stderr);
        return 0;
    }
    if (frame->returned.rsi == wait_input_rsi) {
        if (must_wait || frame->returned.rcx != frame->entered.rcx ||
            frame->returned.r11 != frame->entered.r11) {
            fputs("CONTRACT-FAIL required WAIT or no-syscall register frame\n", stderr);
            return 0;
        }
    } else if (frame->returned.rsi != 128 ||
               frame->returned.rcx != (uintptr_t)function + 19) {
        fputs("CONTRACT-FAIL WAIT syscall return frame\n", stderr);
        return 0;
    }
    return 1;
}

static int publish(struct storage *storage, const char *label) {
    struct frame frame;
    edsl_futex_predicate_probe(edsl_futex_publish_stub, &storage->word,
                               &storage->payload, &frame, (uintptr_t)&storage->payload);
    print_frame(label, &frame);
    if (!common_frame(&frame, storage) || frame.returned.rax > 1 ||
        frame.returned.rsi != 129 || frame.returned.rdx != 1 ||
        frame.returned.rcx != (uintptr_t)edsl_futex_publish_stub + 31 ||
        frame.word != 1 || frame.payload != published_payload) {
        fputs("CONTRACT-FAIL old publisher frame/raw WAKE count\n", stderr);
        return 1;
    }
    return 0;
}

static void *wait_thread(void *argument) {
    struct waiter *waiter = argument;
    atomic_store_explicit(&waiter->attempting, 1, memory_order_release);
    edsl_futex_predicate_probe(waiter->function, &waiter->storage->word,
                               &waiter->storage->payload, &waiter->frame, wait_input_rsi);
    atomic_store_explicit(&waiter->done, 1, memory_order_release);
    return NULL;
}

static int start_waiter(pthread_t *thread, struct waiter *waiter,
                        struct storage *storage, const void *function) {
    *waiter = (struct waiter){ .storage = storage, .function = function };
    int error = pthread_create(thread, NULL, wait_thread, waiter);
    if (error) fprintf(stderr, "pthread_create: %s\n", strerror(error));
    return error ? 1 : 0;
}

static int join_waiter(pthread_t thread, struct waiter *waiter, const char *label,
                       int must_wait) {
    int error = pthread_join(thread, NULL);
    if (error) {
        fprintf(stderr, "pthread_join: %s\n", strerror(error));
        return 1;
    }
    print_frame(label, &waiter->frame);
    return waiter_frame(&waiter->frame, waiter->storage, waiter->function, must_wait) ? 0 : 1;
}

static int wake_selection(struct storage *storage, unsigned *selected, uint32_t predicate) {
    long raw = edsl_futex_predicate_wake_one(&storage->word);
    if (raw != 0 && raw != 1) {
        fprintf(stderr, "CONTRACT-FAIL WAKE_PRIVATE/1 raw=%016" PRIx64 "\n", (uint64_t)raw);
        return 1;
    }
    if (storage->word != predicate || storage->payload != (predicate ? published_payload : 0)) {
        fputs("CONTRACT-FAIL WAIT/WAKE changed predicate or payload\n", stderr);
        return 1;
    }
    if (raw == 1) {
        ++*selected;
        printf("OBSERVED eligible WAKE_PRIVATE/1 selection: raw=%016" PRIx64
               " W=%08" PRIx32 " P=%08" PRIx32 "\n",
               (uint64_t)raw, storage->word, storage->payload);
    }
    return 0;
}

static int two_wakes_while_zero(const void *function) {
    struct storage storage;
    initialize_storage(&storage, 0);
    struct storage before = storage;
    struct waiter waiter;
    pthread_t thread;
    if (start_waiter(&thread, &waiter, &storage, function)) return 1;
    unsigned selected = 0;
    int failed = 0;
    for (unsigned attempt = 0; attempt < 100000 && selected < 2; ++attempt) {
        if (atomic_load_explicit(&waiter.done, memory_order_acquire)) {
            int result = join_waiter(thread, &waiter, "early-return-W0", 1);
            return result ? result : 1;
        }
        if (wake_selection(&storage, &selected, 0)) { failed = 1; break; }
        sched_yield();
    }
    if (atomic_load_explicit(&waiter.done, memory_order_acquire)) {
        int result = join_waiter(thread, &waiter, "early-return-W0", 1);
        return result ? result : 1;
    }
    printf("OBSERVED W0 eligible WAKE selections=%u; one waiter, no publication yet\n", selected);
    int publisher_result = publish(&storage, "publish-after-W0-wakes");
    int waiter_result = join_waiter(thread, &waiter, "rechecked-after-W0-wakes", 1);
    if (failed || publisher_result || waiter_result || !storage_frame(&before, &storage)) return 1;
    if (selected != 2) {
        fputs("INCONCLUSIVE: two eligible W0 WAKE selections not observed within bound\n", stderr);
        return 3;
    }
    puts("OBSERVED two W0 WAKE selections for one waiter (re-entry witnessed), then return 1 with P/W1");
    return 0;
}

static int late_and_races(void) {
    for (unsigned attempt = 0; attempt < 33; ++attempt) {
        struct storage storage;
        initialize_storage(&storage, 0);
        struct storage before = storage;
        struct waiter waiter;
        pthread_t thread;
        int publisher_result = 0;
        if (attempt == 0) publisher_result = publish(&storage, "late-before-start");
        if (start_waiter(&thread, &waiter, &storage, edsl_futex_predicate_wait_stub)) return 1;
        if (attempt != 0) {
            for (unsigned spin = 0; spin < 1000; ++spin) {
                if (atomic_load_explicit(&waiter.attempting, memory_order_acquire)) break;
                sched_yield();
            }
            publisher_result = publish(&storage, "racing-publisher");
        }
        int waiter_result = join_waiter(thread, &waiter, "late-or-racing-waiter", 0);
        if (publisher_result || waiter_result || !storage_frame(&before, &storage)) return 1;
        if (attempt == 0 && waiter.frame.returned.rsi != wait_input_rsi) {
            fputs("CONTRACT-FAIL late waiter entered WAIT despite W1 before start\n", stderr);
            return 1;
        }
    }
    puts("OBSERVED one published-before-start case and 32 bounded publication races");
    return 0;
}

static int contended(void) {
    struct storage storage;
    initialize_storage(&storage, 0);
    struct storage before = storage;
    struct waiter waiters[2];
    pthread_t threads[2];
    if (start_waiter(&threads[0], &waiters[0], &storage, edsl_futex_predicate_wait_stub)) return 1;
    if (start_waiter(&threads[1], &waiters[1], &storage, edsl_futex_predicate_wait_stub)) {
        (void)publish(&storage, "failed-contender-cleanup");
        (void)join_waiter(threads[0], &waiters[0], "failed-contender-cleanup", 0);
        return 1;
    }
    unsigned selected_before = 0;
    int failed = 0;
    for (unsigned attempt = 0; attempt < 100000 && selected_before < 2; ++attempt) {
        if (atomic_load_explicit(&waiters[0].done, memory_order_acquire) ||
            atomic_load_explicit(&waiters[1].done, memory_order_acquire)) {
            failed = 1;
            break;
        }
        if (wake_selection(&storage, &selected_before, 0)) { failed = 1; break; }
        sched_yield();
    }
    if (publish(&storage, "contended-publisher-WAKE1")) failed = 1;
    unsigned cleanup_selected = 0;
    int both_done = 0;
    for (unsigned attempt = 0; attempt < 100000; ++attempt) {
        if (atomic_load_explicit(&waiters[0].done, memory_order_acquire) &&
            atomic_load_explicit(&waiters[1].done, memory_order_acquire)) {
            both_done = 1;
            break;
        }
        if (wake_selection(&storage, &cleanup_selected, 1)) { failed = 1; break; }
        sched_yield();
    }
    if (!both_done) {
        fputs("INCONCLUSIVE: contended cleanup bounded; no progress/fairness inference\n", stderr);
        exit(3);
    }
    int first_result = join_waiter(threads[0], &waiters[0], "contended-waiter-0", 0);
    int second_result = join_waiter(threads[1], &waiters[1], "contended-waiter-1", 0);
    printf("OBSERVED two contenders: W0 selections=%u, additional post-publication "
           "harness WAKE1 selections=%u; publisher itself remains WAKE1\n",
           selected_before, cleanup_selected);
    if (failed || first_result || second_result || !storage_frame(&before, &storage)) return 1;
    if (selected_before != 2) {
        fputs("INCONCLUSIVE: contended W0 selections not observed within bound\n", stderr);
        return 3;
    }
    return 0;
}

#if defined(__linux__) && defined(__x86_64__)
struct trace_observation {
    struct storage storage;
    struct frame frame;
};

static void stop_tracee(pid_t child) {
    (void)kill(child, SIGKILL);
    while (waitpid(child, NULL, 0) == -1 && errno == EINTR) {}
}

static int traced_case(int mismatch, const void *function) {
    struct trace_observation *observation = mmap(NULL, sizeof(*observation),
        PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (observation == MAP_FAILED) { perror("mmap"); return 1; }
    initialize_storage(&observation->storage, mismatch ? 0 : 1);
    struct storage before = observation->storage;
    pid_t parent = getpid();
    pid_t child = fork();
    if (child == -1) { perror("fork"); (void)munmap(observation, sizeof(*observation)); return 1; }
    if (child == 0) {
        if (prctl(PR_SET_PDEATHSIG, SIGKILL) == -1 || getppid() != parent) _exit(77);
        if (ptrace(PTRACE_TRACEME, 0, NULL, NULL) == -1) _exit(77);
        if (raise(SIGSTOP) != 0) _exit(78);
        edsl_futex_predicate_probe(function, &observation->storage.word,
            &observation->storage.payload, &observation->frame, wait_input_rsi);
        _exit(0);
    }
    int wait_status = 0;
    pid_t waited = waitpid(child, &wait_status, 0);
    if (waited != child || !WIFSTOPPED(wait_status)) {
        if (waited != child) stop_tracee(child);
        (void)munmap(observation, sizeof(*observation));
        fputs("INCONCLUSIVE: ptrace child did not reach initial stop\n", stderr);
        return 3;
    }
    if (ptrace(PTRACE_SETOPTIONS, child, NULL,
               (void *)(uintptr_t)(PTRACE_O_TRACESYSGOOD | PTRACE_O_EXITKILL)) == -1) {
        perror("ptrace options");
        stop_tracee(child);
        (void)munmap(observation, sizeof(*observation));
        return 3;
    }
    unsigned entries = 0, eagains = 0;
    int pending_wait = 0, result = 3, child_exited = 0;
    for (unsigned event = 0; event < 1000; ++event) {
        if (ptrace(PTRACE_SYSCALL, child, NULL, NULL) == -1 ||
            waitpid(child, &wait_status, 0) != child) {
            perror("ptrace/waitpid");
            break;
        }
        if (WIFEXITED(wait_status)) {
            child_exited = 1;
            result = WEXITSTATUS(wait_status) == 0 ? 0 : 1;
            break;
        }
        if (WIFSIGNALED(wait_status)) {
            child_exited = 1;
            fputs("INCONCLUSIVE: trace child terminated by a signal\n", stderr);
            break;
        }
        if (!WIFSTOPPED(wait_status) || WSTOPSIG(wait_status) != (SIGTRAP | 0x80)) {
            fputs("INCONCLUSIVE: unexpected trace signal\n", stderr);
            break;
        }
        struct user_regs_struct registers;
        if (ptrace(PTRACE_GETREGS, child, NULL, &registers) == -1) {
            perror("ptrace registers");
            break;
        }
        if (registers.orig_rax != 202) continue;
        if (registers.rip != (uintptr_t)function + 19 ||
            registers.rdi != (uintptr_t)&observation->storage.word ||
            registers.rsi != 128 || registers.rdx != 0 || registers.r10 != 0 ||
            registers.r8 != 0 || registers.r9 != 0) {
            fputs("CONTRACT-FAIL traced WAIT entry/registers\n", stderr);
            result = 1;
            break;
        }
        if (!pending_wait) {
            ++entries;
            if (!mismatch || entries > 2 || observation->storage.word != 0 ||
                registers.rax != (uint64_t)-(int64_t)ENOSYS) {
                fputs("CONTRACT-FAIL unexpected traced WAIT entry\n", stderr);
                result = 1;
                break;
            }
            if (publish(&observation->storage, "trace-parent-publish-before-WAIT")) {
                result = 1;
                break;
            }
            pending_wait = 1;
        } else {
            printf("OBSERVED actual traced WAIT exit: RAX=%016" PRIx64
                   " RIP=%016" PRIx64 " RCX=%016" PRIx64 " R11=%016" PRIx64
                   " RFLAGS=%016" PRIx64 " W=%08" PRIx32 "\n",
                   (uint64_t)registers.rax, (uint64_t)registers.rip,
                   (uint64_t)registers.rcx, (uint64_t)registers.r11,
                   (uint64_t)registers.eflags, observation->storage.word);
            if (registers.rax != (uint64_t)-(int64_t)EAGAIN) {
                fputs("CONTRACT-FAIL actual mismatching WAIT did not return -EAGAIN\n", stderr);
                result = 1;
                break;
            }
            ++eagains;
            pending_wait = 0;
            if (eagains == 1) {
                observation->storage.word = 0;
                observation->storage.payload = 0;
                puts("TRACE reset synthetic W/P to zero while child stopped after actual -EAGAIN");
            }
        }
    }
    if (!child_exited) stop_tracee(child);
    if (result == 0) {
        print_frame(mismatch ? "traced-EAGAIN-recheck" : "traced-initial-W1", &observation->frame);
        if (!waiter_frame(&observation->frame, &observation->storage, function, mismatch) ||
            !storage_frame(&before, &observation->storage)) result = 1;
        else if (pending_wait || entries != (mismatch ? 2u : 0u) || eagains != entries) {
            fputs("CONTRACT-FAIL traced WAIT event counts\n", stderr);
            result = 1;
        } else {
            printf("OBSERVED syscall trace: WAIT entries=%u, real -EAGAIN exits=%u\n", entries, eagains);
        }
    }
    (void)munmap(observation, sizeof(*observation));
    return result;
}
#else
static int traced_case(int mismatch, const void *function) {
    (void)mismatch;
    (void)function;
    fputs("NOTRUN: syscall tracing requires Linux x86_64\n", stderr);
    return 2;
}
#endif

int main(int argc, char **argv) {
#if !defined(__linux__) || !defined(__x86_64__)
    fputs("NOTRUN: native observer requires Linux x86_64; formal=NOTRUN grading=NOTRUN\n", stderr);
    return 2;
#endif
    int negative_wake = argc == 2 && strcmp(argv[1], "--no-recheck-wake") == 0;
    int negative_eagain = argc == 2 && strcmp(argv[1], "--no-recheck-eagain") == 0;
    if (argc != 1 && !negative_wake && !negative_eagain) {
        fputs("usage: native-check [--no-recheck-wake|--no-recheck-eagain]\n", stderr);
        return 2;
    }
    struct sigaction action = { .sa_handler = watchdog };
    if (sigemptyset(&action.sa_mask) || sigaction(SIGALRM, &action, NULL)) {
        perror("sigaction");
        return 1;
    }
    alarm(12);
    setvbuf(stdout, NULL, _IOLBF, 0);
    puts("Native-only external observations: formal=NOTRUN grading=NOTRUN");
    puts("Assumes Linux x86_64, SysV ABI, available ptrace/futex/pthread, stable aligned storage; "
         "no fairness, scheduling-progress or kernel-refinement claim");
    int result;
    if (negative_wake) result = two_wakes_while_zero(edsl_futex_predicate_no_recheck_stub);
    else if (negative_eagain) result = traced_case(1, edsl_futex_predicate_no_recheck_stub);
    else {
        result = traced_case(0, edsl_futex_predicate_wait_stub);
        if (!result) result = traced_case(1, edsl_futex_predicate_wait_stub);
        if (!result) result = two_wakes_while_zero(edsl_futex_predicate_wait_stub);
        if (!result) result = late_and_races();
        if (!result) result = contended();
    }
    alarm(0);
    if (!result) puts("OBSERVED requested bounded native cases; formal=NOTRUN grading=NOTRUN");
    return result;
}
