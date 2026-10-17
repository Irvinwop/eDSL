/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <openssl/evp.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>

enum { RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI,
       R8, R9, R10, R11, R12, R13, R14, R15, NREG };
enum { RESULT = 1, DATA = 2, STACK = 4, SAVED = 8, FLAGS = 16, MEMORY = 32, ROOT = 64 };
static const uint64_t arithmetic_flags = UINT64_C(0x8d5);
static const unsigned saved[] = {RBX, RBP, R12, R13, R14, R15};
uint64_t cm_requested[NREG], cm_before[NREG], cm_after[NREG];
uint64_t cm_requested_flags, cm_before_flags, cm_after_flags, cm_reached;
uint64_t cm_host_rsp, cm_host_flags, cm_host_saved[6];
uintptr_t cm_target;
extern void cm_run(void), cm_root_capture(void);
#define DECLARE(n) extern const unsigned char n[], n##_end[]
DECLARE(cm_gcc);
DECLARE(cm_clang);
DECLARE(cm_bad_no_store);
DECLARE(cm_bad_stale);
DECLARE(cm_bad_outside);
DECLARE(cm_bad_rbx);

struct profile {
    const char *name;
    const unsigned char *begin, *end;
    unsigned char bytes[18];
};
static const struct profile profiles[] = {
    {"gcc13", cm_gcc, cm_gcc_end,
     {0x50,0xe8,5,0,0,0,0x5a,0x48,0xff,0xc0,0xc3,0x48,0x89,0x37,0x48,0x8b,7,0xc3}},
    {"clang18", cm_clang, cm_clang_end,
     {0x50,0xe8,5,0,0,0,0x48,0xff,0xc0,0x59,0xc3,0x48,0x89,0x37,0x48,0x8b,7,0xc3}}
};
struct mutant {
    const char *name;
    const unsigned char *begin;
    unsigned expected;
};
static const struct mutant mutants[] = {
    {"no-store", cm_bad_no_store, DATA}, {"stale-reload", cm_bad_stale, RESULT},
    {"outside-target", cm_bad_outside, MEMORY}, {"callee-saved", cm_bad_rbx, SAVED}
};

static void die(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(2);
}

/* All files and complete embedded slots are authenticated before output is
 * opened or any candidate is entered. Input files remain non-executable data. */
static void bind_inputs(char **paths) {
    bool valid = true;
    for (size_t i = 0; i < sizeof profiles / sizeof *profiles; ++i) {
        const struct profile *p = &profiles[i];
        unsigned char input[19];
        FILE *file = fopen(paths[i], "rb");
        size_t count = file ? fread(input, 1, sizeof input, file) : 0;
        bool io_ok = file && !ferror(file);
        if (file && fclose(file) != 0) io_ok = false;
        if (!io_ok || count != sizeof p->bytes ||
            (uintptr_t)p->end - (uintptr_t)p->begin != sizeof p->bytes ||
            memcmp(p->begin, p->bytes, sizeof p->bytes) != 0 ||
            memcmp(input, p->bytes, sizeof p->bytes) != 0) valid = false;
    }
    if (!valid) die("Whole callable DATA8 text differs from embedded expected profiles");
}

/* Natural base-256 addition and a discarded final carry, independent of the
 * fixture's machine-word INC. Literal edge vectors check this observer too. */
static uint64_t oracle(uint64_t input) {
    uint64_t output = 0;
    unsigned carry = 1;
    for (unsigned digit = 0; digit < 8; ++digit) {
        unsigned sum = (unsigned)((input >> (digit * 8)) & 255) + carry;
        output |= (uint64_t)(sum % 256) << (digit * 8);
        carry = sum / 256;
    }
    return output;
}
static const struct { uint64_t input, output; } edges[] = {
    {0,1}, {1,2}, {0x7f,0x80}, {0xff,0x100}, {0xffff,0x10000},
    {0xffffff,0x1000000}, {0x7fffffff,0x80000000}, {0xffffffff,0x100000000},
    {0xffffffffff,0x10000000000}, {0xffffffffffff,0x1000000000000},
    {0xffffffffffffff,0x100000000000000},
    {UINT64_C(0x7fffffffffffffff),UINT64_C(0x8000000000000000)},
    {UINT64_C(0x8000000000000000),UINT64_C(0x8000000000000001)},
    {UINT64_C(0xfffffffffffffffe),UINT64_MAX}, {UINT64_MAX,0},
    {UINT64_C(0x123456789abcdeff),UINT64_C(0x123456789abcdf00)}
};
static uint64_t random_state = UINT64_C(0xa29b73e5d1046fc8);
static uint64_t random_word(void) {
    uint64_t z = (random_state += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return z ^ (z >> 31);
}
static uint64_t load64(const unsigned char *bytes) {
    uint64_t value;
    memcpy(&value, bytes, sizeof value);
    return value;
}
static uint64_t read_flags(void) {
    uint64_t flags;
    __asm__ volatile("pushfq; popq %0" : "=r"(flags) : : "memory");
    return flags;
}
static FILE *open_output(const char *directory, const char *name, const char *mode) {
    char path[4096];
    int size = snprintf(path, sizeof path, "%s/%s", directory, name);
    if (size < 0 || (size_t)size >= sizeof path) die("Evidence path too long");
    FILE *file = fopen(path, mode);
    if (!file) die("Cannot open evidence output");
    return file;
}
static void close_output(FILE *file) {
    if (ferror(file) || fclose(file) != 0) die("Evidence output failed");
}
static EVP_MD_CTX *digest_context;
static void sha256(const unsigned char *bytes, size_t length, char hex[65]) {
    unsigned char digest[EVP_MAX_MD_SIZE];
    unsigned size = 0;
    if (EVP_DigestInit_ex(digest_context, EVP_sha256(), NULL) != 1 ||
        EVP_DigestUpdate(digest_context, bytes, length) != 1 ||
        EVP_DigestFinal_ex(digest_context, digest, &size) != 1 || size != 32)
        die("SHA256 computation failed");
    for (unsigned i = 0; i < size; ++i)
        (void)snprintf(hex + i * 2, 3, "%02x", digest[i]);
}
static size_t read_maps(char *buffer, size_t capacity) {
    int fd = open("/proc/self/maps", O_RDONLY | O_CLOEXEC);
    if (fd < 0) die("Cannot read mapping permissions");
    size_t used = 0;
    for (;;) {
        if (used + 1 == capacity) die("Mapping evidence exceeds capacity");
        ssize_t count = read(fd, buffer + used, capacity - used - 1);
        if (count < 0) die("Cannot read mapping permissions");
        if (count == 0) break;
        used += (size_t)count;
    }
    if (close(fd) != 0) die("Cannot close mapping evidence");
    buffer[used] = '\0';
    return used;
}
static void check_permissions(const char *maps, uintptr_t mapping, size_t page_size) {
    unsigned found = 0;
    for (const char *line = maps; line; line = strchr(line, '\n')) {
        if (*line == '\n') ++line;
        uintptr_t begin, end;
        char permissions[5];
        if (sscanf(line, "%" SCNxPTR "-%" SCNxPTR " %4s", &begin, &end, permissions) != 3)
            continue;
        for (unsigned i = 0; i < 3; ++i) {
            uintptr_t address = mapping + i * page_size;
            if (begin <= address && address + page_size <= end) {
                if (strncmp(permissions, i == 1 ? "rw-p" : "---p", 4) != 0)
                    die("Owned RAM or guard mapping permissions differ");
                found |= 1u << i;
            }
        }
    }
    if (found != 7) die("Missing owned RAM or guard mapping");
}
static void write_regs(FILE *out, const uint64_t *registers) {
    fputc('[', out);
    for (unsigned i = 0; i < NREG; ++i)
        fprintf(out, "%s\"%016" PRIx64 "\"", i ? "," : "", registers[i]);
    fputc(']', out);
}

static void record(FILE *json, FILE *pages, uint64_t sequence, const char *name,
                   bool negative, unsigned flag_profile, size_t target_offset,
                   const unsigned char *before, const unsigned char *after,
                   size_t page_size, unsigned failure) {
    /* Each record indexes stack-before, data-before, stack-after, data-after. */
    char hashes[4][65];
    for (unsigned i = 0; i < 4; ++i) {
        const unsigned char *page = i < 2 ? before + i * page_size : after + (i - 2) * page_size;
        sha256(page, page_size, hashes[i]);
        if (fwrite(page, 1, page_size, pages) != page_size) die("Page evidence write failed");
    }
    fprintf(json, "{\"case\":%" PRIu64 ",\"name\":\"%s\",\"negative\":%s,"
            "\"flag_profile\":%u,\"target_offset\":%zu,\"page_size\":%zu,"
            "\"page_offset\":%" PRIu64 ",\"sha256\":[\"%s\",\"%s\",\"%s\",\"%s\"],"
            "\"requested_flags\":\"%016" PRIx64 "\",\"pre_flags\":\"%016" PRIx64 "\","
            "\"post_flags\":\"%016" PRIx64 "\",\"expected_rax\":\"%016" PRIx64 "\","
            "\"expected_data\":\"%016" PRIx64 "\",\"old_data\":\"%016" PRIx64 "\","
            "\"actual_data\":\"%016" PRIx64 "\",\"failure_mask\":%u,\"pre\":",
            sequence, name, negative ? "true" : "false", flag_profile, target_offset, page_size,
            sequence * (uint64_t)page_size * 4, hashes[0], hashes[1], hashes[2], hashes[3],
            cm_requested_flags, cm_before_flags, cm_after_flags, oracle(cm_before[RSI]),
            cm_before[RSI], load64(before + page_size + target_offset),
            load64(after + page_size + target_offset), failure);
    write_regs(json, cm_before);
    fputs(",\"post\":", json);
    write_regs(json, cm_after);
    fprintf(json, ",\"reached_root\":%s}\n", cm_reached == 1 ? "true" : "false");
}

int main(int argc, char **argv) {
    if (argc != 4) die("usage: call-memory64-check OUTPUT_DIRECTORY GCC_TEXT CLANG_TEXT");
    bind_inputs(argv + 2);
    for (size_t i = 0; i < sizeof edges / sizeof *edges; ++i)
        if (oracle(edges[i].input) != edges[i].output) die("Independent carry oracle failed");
    uint64_t initial_flags = read_flags();
    if (initial_flags & ((UINT64_C(1) << 18) | (UINT64_C(1) << 10) |
                         (UINT64_C(1) << 8) | (UINT64_C(1) << 14) | (UINT64_C(1) << 17)))
        die("Requires ordinary flags with AC/DF/TF/NT/VM clear");
    unsigned long cet_status = 0;
    errno = 0;
    long cet_result = syscall(SYS_arch_prctl, 0x5005, &cet_status);
    int cet_errno = errno;
    if ((cet_result == 0 && cet_status != 0) ||
        (cet_result != 0 && cet_errno != EINVAL && cet_errno != ENOSYS))
        die("Requires disabled CET shadow stack");
    if ((uintptr_t)cm_root_capture <= UINT32_MAX) die("Requires PIE root above 4 GiB");
    long page_result = sysconf(_SC_PAGESIZE);
    if (page_result < 4096 || page_result % 8 != 0) die("Unsupported page size");
    size_t page_size = (size_t)page_result;
    unsigned char *mappings[2], *ram[2];
    for (unsigned i = 0; i < 2; ++i) {
        mappings[i] = mmap(NULL, page_size * 3, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (mappings[i] == MAP_FAILED) die("Cannot allocate guarded RAM");
        ram[i] = mappings[i] + page_size;
        if ((uintptr_t)ram[i] <= UINT32_MAX) die("Requires owned RAM above 4 GiB");
        if (mprotect(ram[i], page_size, PROT_READ | PROT_WRITE) != 0)
            die("Cannot initialize guarded RAM permissions");
    }
    unsigned char *before = malloc(page_size * 2), *after = malloc(page_size * 2);
    char *maps_before = malloc(131072), *maps_after = malloc(131072);
    digest_context = EVP_MD_CTX_new();
    if (!before || !after || !maps_before || !maps_after || !digest_context) die("Allocation failed");
    char warm_hash[65];
    sha256((const unsigned char *)"warm", 4, warm_hash);
    FILE *json = open_output(argv[1], "observations.jsonl", "w");
    FILE *pages = open_output(argv[1], "pages.bin", "wb");
    FILE *identity = open_output(argv[1], "identity.txt", "w");
    FILE *mapping_before = open_output(argv[1], "maps-before.txt", "w");
    FILE *mapping_after = open_output(argv[1], "maps-after.txt", "w");
    if (setvbuf(json, NULL, _IONBF, 0) || setvbuf(pages, NULL, _IONBF, 0) ||
        setvbuf(mapping_before, NULL, _IONBF, 0) || setvbuf(mapping_after, NULL, _IONBF, 0))
        die("Cannot configure evidence streams");
    fprintf(identity, "root=%016" PRIxPTR " stack=%016" PRIxPTR " data=%016" PRIxPTR
            " page_size=%zu CET_result=%ld CET_status=%lu CET_errno=%d\n",
            (uintptr_t)cm_root_capture, (uintptr_t)ram[0], (uintptr_t)ram[1],
            page_size, cet_result, cet_status, cet_errno);
    for (size_t i = 0; i < sizeof profiles / sizeof *profiles; ++i) {
        if ((uintptr_t)profiles[i].begin <= UINT32_MAX) die("Requires PIE code above 4 GiB");
        fprintf(identity, "%s entry=%016" PRIxPTR " helper=%016" PRIxPTR " bytes=",
                profiles[i].name, (uintptr_t)profiles[i].begin, (uintptr_t)profiles[i].begin + 11);
        for (size_t j = 0; j < sizeof profiles[i].bytes; ++j) fprintf(identity, "%02x", profiles[i].begin[j]);
        fputc('\n', identity);
    }
    close_output(identity);
    sigset_t blocked, old_signals;
    if (sigfillset(&blocked) != 0 || sigprocmask(SIG_SETMASK, &blocked, &old_signals) != 0)
        die("Cannot block asynchronous signals");
    size_t maps_size = read_maps(maps_before, 131072);
    for (unsigned i = 0; i < 2; ++i) check_permissions(maps_before, (uintptr_t)mappings[i], page_size);
    if (fwrite(maps_before, 1, maps_size, mapping_before) != maps_size) die("Mapping evidence write failed");
    uint64_t sequence = 0, positives = 0, negatives = 0;
    unsigned failures = 0;
    static const unsigned flag_positions[] = {0,2,4,6,7,11};
    for (unsigned profile_flags = 0; profile_flags < 128; ++profile_flags) {
        uint64_t flags = initial_flags & ~(arithmetic_flags | (UINT64_C(1) << 21));
        for (unsigned i = 0; i < 6; ++i)
            if (profile_flags & (1u << i)) flags |= UINT64_C(1) << flag_positions[i];
        if (profile_flags & 64) flags |= UINT64_C(1) << 21;
        for (size_t implementation = 0; implementation < 6; ++implementation) {
            bool negative = implementation >= 2;
            size_t count = negative ? 1 : 32;
            const char *name = negative ? mutants[implementation - 2].name : profiles[implementation].name;
            const unsigned char *code = negative ? mutants[implementation - 2].begin : profiles[implementation].begin;
            for (size_t sample = 0; sample < count; ++sample) {
                uint64_t input = negative ? UINT64_C(0xfedcba9876543210) :
                    (sample < sizeof edges / sizeof *edges ? edges[sample].input : random_word());
                size_t target_offset = negative ? 16 : (sample % 4 == 0 ? 8 :
                    sample % 4 == 1 ? 9 : sample % 4 == 2 ? 15 : page_size - 8);
                for (unsigned region_index = 0; region_index < 2; ++region_index)
                    for (size_t offset = 0; offset < page_size; offset += 8) {
                        uint64_t word = random_word();
                        memcpy(ram[region_index] + offset, &word, 8);
                    }
                uint64_t old = random_word();
                if (old == input) old ^= 1;
                memcpy(ram[1] + target_offset, &old, 8);
                if (negative && implementation == 4) {
                    uint64_t neighbor = ~input;
                    memcpy(ram[1] + target_offset + 8, &neighbor, 8);
                }
                uintptr_t root = (uintptr_t)cm_root_capture;
                memcpy(ram[0] + 24, &root, 8);
                memcpy(before, ram[0], page_size);
                memcpy(before + page_size, ram[1], page_size);
                for (unsigned i = 0; i < NREG; ++i) cm_requested[i] = random_word();
                cm_requested[RAX] |= 1;
                cm_requested[RSP] = (uintptr_t)(ram[0] + 24);
                cm_requested[RDI] = (uintptr_t)(ram[1] + target_offset);
                cm_requested[RSI] = input;
                cm_requested_flags = flags;
                cm_reached = 0;
                cm_target = (uintptr_t)code;
                cm_run();
                if (memcmp(cm_before, cm_requested, sizeof cm_before) != 0 || cm_before_flags != flags)
                    die("Requested register/flag installation was not observed");
                memcpy(after, ram[0], page_size);
                memcpy(after + page_size, ram[1], page_size);
                unsigned failure = 0;
                if (cm_after[RAX] != oracle(input)) failure |= RESULT;
                if (load64(after + page_size + target_offset) != input) failure |= DATA;
                if (cm_after[RSP] != cm_before[RSP] + 8) failure |= STACK;
                if (cm_reached != 1) failure |= ROOT;
                for (size_t i = 0; i < sizeof saved / sizeof *saved; ++i)
                    if (cm_after[saved[i]] != cm_before[saved[i]]) failure |= SAVED;
                if ((cm_after_flags & ~arithmetic_flags) != (cm_before_flags & ~arithmetic_flags)) failure |= FLAGS;
                for (size_t offset = 0; offset < page_size; ++offset) {
                    if ((offset < 8 || offset >= 24) && before[offset] != after[offset]) failure |= MEMORY;
                    if ((offset < target_offset || offset >= target_offset + 8) &&
                        before[page_size + offset] != after[page_size + offset]) failure |= MEMORY;
                }
                if (negative) {
                    ++negatives;
                    if (!(failure & mutants[implementation - 2].expected)) ++failures;
                } else {
                    ++positives;
                    if (failure) ++failures;
                }
                record(json, pages, sequence++, name, negative, profile_flags, target_offset,
                       before, after, page_size, failure);
            }
        }
    }
    size_t after_maps_size = read_maps(maps_after, 131072);
    bool maps_equal = maps_size == after_maps_size && memcmp(maps_before, maps_after, maps_size) == 0;
    if (!maps_equal) ++failures;
    if (fwrite(maps_after, 1, after_maps_size, mapping_after) != after_maps_size) die("Mapping evidence write failed");
    close_output(json);
    close_output(pages);
    close_output(mapping_before);
    close_output(mapping_after);
    if (sigprocmask(SIG_SETMASK, &old_signals, NULL) != 0) die("Cannot restore signal mask");
    for (unsigned i = 0; i < 2; ++i)
        if (munmap(mappings[i], page_size * 3) != 0) die("Cannot release owned RAM");
    free(before);
    free(after);
    free(maps_before);
    free(maps_after);
    EVP_MD_CTX_free(digest_context);
    fprintf(stderr, "native=%s positive=%" PRIu64 " negative=%" PRIu64
            " flag_profiles=128 maps_equal=%s failures=%u formal=NOTRUN\n",
            failures ? "FAIL" : "PASS", positives, negatives, maps_equal ? "true" : "false", failures);
    return failures ? 1 : 0;
}
