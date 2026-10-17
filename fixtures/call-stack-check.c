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
enum { RESULT = 1, STACK = 2, SAVED = 4, FLAGS = 8, MEMORY = 16, RETURN = 32 };
static const uint64_t arithmetic_flags = UINT64_C(0x8d5);
static const uint64_t id_flag = UINT64_C(1) << 21;
static const unsigned saved_registers[] = {RBX, RBP, R12, R13, R14, R15};
uint64_t cs_requested[NREG], cs_before[NREG], cs_after[NREG];
uint64_t cs_requested_flags, cs_before_flags, cs_after_flags, cs_reached;
uint64_t cs_host_rsp, cs_host_flags, cs_host_saved[6];
uintptr_t cs_target;
extern void cs_run(void), cs_root_capture(void);

#define DECLARE_SLOT(n) \
    extern const unsigned char n[], n##_end[], n##_entry[], n##_helper[], n##_cont[]
DECLARE_SLOT(cs_gcc_same);
DECLARE_SLOT(cs_gcc_separate);
DECLARE_SLOT(cs_clang_same);
DECLARE_SLOT(cs_clang_separate);
#define DECLARE_MUTANT(n) extern const unsigned char n[], n##_end[]
DECLARE_MUTANT(cs_bad_missing_helper);
DECLARE_MUTANT(cs_bad_plus_three);
DECLARE_MUTANT(cs_bad_narrow);
DECLARE_MUTANT(cs_bad_rbx);
DECLARE_MUTANT(cs_bad_r12);
DECLARE_MUTANT(cs_bad_outside);
DECLARE_MUTANT(cs_bad_rsp);
DECLARE_MUTANT(cs_bad_df);
DECLARE_MUTANT(cs_bad_id);
extern const unsigned char cs_mutants_begin[], cs_mutants_end[];
extern const unsigned char cs_mutant_good_helper[], cs_mutant_zero_helper[];

struct profile {
    const char *name;
    const unsigned char *begin, *end, *entry, *helper, *continuation;
    size_t length, entry_offset;
    unsigned char expected[16];
};
#define SLOT(n, len, off, ...) \
    {#n, n, n##_end, n##_entry, n##_helper, n##_cont, len, off, {__VA_ARGS__}}
static const struct profile profiles[] = {
    SLOT(cs_gcc_same, 14, 5,
         0x48,0x8d,0x47,0x01,0xc3,0xe8,0xf6,0xff,0xff,0xff,0x48,0xff,0xc0,0xc3),
    SLOT(cs_gcc_separate, 16, 0,
         0x50,0xe8,0x05,0x00,0x00,0x00,0x5a,0x48,0xff,0xc0,0xc3,0x48,0x8d,0x47,0x01,0xc3),
    SLOT(cs_clang_same, 16, 5,
         0x48,0x8d,0x47,0x01,0xc3,0x50,0xe8,0xf5,0xff,0xff,0xff,0x48,0xff,0xc0,0x59,0xc3),
    SLOT(cs_clang_separate, 16, 0,
         0x50,0xe8,0x05,0x00,0x00,0x00,0x48,0xff,0xc0,0x59,0xc3,0x48,0x8d,0x47,0x01,0xc3)
};
struct mutant {
    const char *name;
    const unsigned char *begin, *end;
    unsigned category;
    int damaged_register;
};
#define MUTANT(n, category, reg) {#n, n, n##_end, category, reg}
static const struct mutant mutants[] = {
    MUTANT(cs_bad_missing_helper, RESULT, -1),
    MUTANT(cs_bad_plus_three, RESULT, -1),
    MUTANT(cs_bad_narrow, RESULT, -1),
    MUTANT(cs_bad_rbx, SAVED, RBX),
    MUTANT(cs_bad_r12, SAVED, R12),
    MUTANT(cs_bad_outside, MEMORY, -1),
    MUTANT(cs_bad_rsp, STACK, -1),
    MUTANT(cs_bad_df, FLAGS, -1),
    MUTANT(cs_bad_id, FLAGS, -1)
};

static void die(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(2);
}

/* Compare ALL input files, ALL slot bytes, their end labels and their entries
 * before opening evidence or entering ANY candidate. Files remain data only. */
static void bind_inputs(char **paths) {
    bool valid = true;
    for (size_t i = 0; i < sizeof profiles / sizeof *profiles; ++i) {
        const struct profile *p = &profiles[i];
        unsigned char bytes[17];
        FILE *input = fopen(paths[i], "rb");
        size_t count = input ? fread(bytes, 1, sizeof bytes, input) : 0;
        bool io_ok = input && !ferror(input);
        if (input && fclose(input) != 0) io_ok = false;
        if (!io_ok || count != p->length ||
            (uintptr_t)p->end - (uintptr_t)p->begin != p->length ||
            (uintptr_t)p->entry - (uintptr_t)p->begin != p->entry_offset ||
            memcmp(p->begin, p->expected, p->length) != 0 ||
            memcmp(bytes, p->expected, p->length) != 0)
            valid = false;
    }
    if (!valid)
        die("Final whole-text extraction differs from embedded expected profiles");
}

/* This is natural-number addition of the constant 2 in base 256. It calls no
 * tested helper and does not reuse the fixtures' machine-word addition. */
static uint64_t oracle(uint64_t input) {
    uint64_t answer = 0;
    unsigned carry = 2;
    for (unsigned digit = 0; digit < 8; ++digit) {
        unsigned sum = (unsigned)((input >> (8 * digit)) & 255) + carry;
        answer |= (uint64_t)(sum % 256) << (8 * digit);
        carry = sum / 256;
    }
    return answer;
}

struct edge { uint64_t input, answer; };
static const struct edge edges[] = {
    {0,2}, {1,3}, {2,4}, {0x7e,0x80}, {0xfe,0x100}, {0xff,0x101},
    {0xfffe,0x10000}, {0xffff,0x10001}, {0xfffffe,0x1000000},
    {0xffffff,0x1000001}, {0x7ffffffe,0x80000000},
    {0x7fffffff,0x80000001}, {0xfffffffe,0x100000000},
    {0xffffffff,0x100000001}, {0xfffffffffe,0x10000000000},
    {0xfffffffffffe,0x1000000000000},
    {0xfffffffffffffe,0x100000000000000},
    {UINT64_C(0x7ffffffffffffffe),UINT64_C(0x8000000000000000)},
    {UINT64_C(0x7fffffffffffffff),UINT64_C(0x8000000000000001)},
    {UINT64_C(0x8000000000000000),UINT64_C(0x8000000000000002)},
    {UINT64_C(0xfffffffffffffffd),UINT64_C(0xffffffffffffffff)},
    {UINT64_C(0xfffffffffffffffe),0}, {UINT64_MAX,1},
    {UINT64_C(0x123456789abcdeff),UINT64_C(0x123456789abcdf01)}
};

static uint64_t rng_state = UINT64_C(0xd06fb17a35c290e4);
static uint64_t random_word(void) {
    uint64_t z = (rng_state += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return z ^ (z >> 31);
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
        (void)snprintf(hex + 2 * i, 3, "%02x", digest[i]);
}

static FILE *output_file(const char *directory, const char *name) {
    char path[4096];
    int count = snprintf(path, sizeof path, "%s/%s", directory, name);
    if (count < 0 || (size_t)count >= sizeof path) die("Evidence path too long");
    FILE *out = fopen(path, "wbx");
    if (!out) die("Cannot create fresh evidence file");
    return out;
}

static void checked_close(FILE *out) {
    if (ferror(out) || fclose(out) != 0) die("Evidence write failed");
}

static uint64_t read_flags(void) {
    uint64_t flags;
    __asm__ volatile ("pushfq; popq %0" : "=r" (flags) : : "memory");
    return flags;
}

static uint64_t flag_profile(unsigned index, uint64_t base) {
    static const unsigned bits[] = {0, 2, 4, 6, 7, 11, 21};
    uint64_t result = base & ~(arithmetic_flags | id_flag);
    for (unsigned i = 0; i < sizeof bits / sizeof *bits; ++i)
        if ((index >> i) & 1) result |= UINT64_C(1) << bits[i];
    return result;
}

static uint64_t load64(const unsigned char *p) {
    uint64_t value;
    memcpy(&value, p, sizeof value);
    return value;
}

static unsigned common_contract(const unsigned char *before,
                                const unsigned char *after, size_t page_size) {
    unsigned failure = 0;
    if (cs_after[RAX] != oracle(cs_before[RDI])) failure |= RESULT;
    if (cs_after[RSP] != cs_before[RSP] + 8) failure |= STACK;
    for (size_t i = 0; i < sizeof saved_registers / sizeof *saved_registers; ++i)
        if (cs_before[saved_registers[i]] != cs_after[saved_registers[i]])
            failure |= SAVED;
    if ((cs_before_flags ^ cs_after_flags) & ~arithmetic_flags) failure |= FLAGS;
    for (size_t i = 0; i < page_size; ++i)
        if ((i < 8 || i >= 24) && before[i] != after[i]) failure |= MEMORY;
    if (cs_reached != 1 || load64(after + 24) != (uintptr_t)cs_root_capture)
        failure |= RETURN;
    return failure;
}

static bool private_pattern(size_t profile, const unsigned char *before,
                            const unsigned char *after) {
    const struct profile *p = &profiles[profile];
    if (profile == 0)
        return load64(after + 16) == (uintptr_t)p->continuation &&
               memcmp(before + 8, after + 8, 8) == 0;
    if (load64(after + 16) != cs_before[RAX] ||
        load64(after + 8) != (uintptr_t)p->continuation) return false;
    if (profile == 1) return cs_after[RDX] == cs_before[RAX];
    return cs_after[RCX] == cs_before[RAX];
}

static void write_regs(FILE *out, const uint64_t *registers) {
    fputc('[', out);
    for (unsigned i = 0; i < NREG; ++i)
        fprintf(out, "%s\"%016" PRIx64 "\"", i ? "," : "", registers[i]);
    fputc(']', out);
}

static void record_case(FILE *json, FILE *pages, uint64_t sequence,
                        const char *name, bool negative, unsigned flag_index,
                        const unsigned char *before, const unsigned char *after,
                        size_t page_size, unsigned failure, bool pattern) {
    char before_sha[65], after_sha[65];
    sha256(before, page_size, before_sha);
    sha256(after, page_size, after_sha);
    if (fwrite(before, 1, page_size, pages) != page_size ||
        fwrite(after, 1, page_size, pages) != page_size) die("Page evidence write failed");
    fprintf(json, "{\"case\":%" PRIu64 ",\"name\":\"%s\",\"negative\":%s,"
            "\"flag_profile\":%u,\"page_offset\":%" PRIu64 ",\"page_size\":%zu,"
            "\"pre_sha256\":\"%s\",\"post_sha256\":\"%s\","
            "\"expected_rax\":\"%016" PRIx64 "\",\"requested_flags\":\"%016" PRIx64 "\","
            "\"pre_flags\":\"%016" PRIx64 "\",\"post_flags\":\"%016" PRIx64 "\","
            "\"failure_mask\":%u,\"positive_private_pattern\":%s,\"reached_root\":%s,\"pre\":",
            sequence, name, negative ? "true" : "false", flag_index,
            sequence * (uint64_t)page_size * 2, page_size, before_sha, after_sha,
            oracle(cs_before[RDI]), cs_requested_flags, cs_before_flags,
            cs_after_flags, failure, negative ? "null" : (pattern ? "true" : "false"),
            cs_reached == 1 ? "true" : "false");
    write_regs(json, cs_before);
    fputs(",\"post\":", json);
    write_regs(json, cs_after);
    fprintf(json, ",\"private_before\":\"%016" PRIx64 "%016" PRIx64 "\","
            "\"private_after\":\"%016" PRIx64 "%016" PRIx64 "\","
            "\"root_ra\":\"%016" PRIx64 "\",\"slot_s_minus_16\":\"%016" PRIx64 "\","
            "\"slot_s_minus_8\":\"%016" PRIx64 "\"}\n",
            load64(before + 8), load64(before + 16), load64(after + 8), load64(after + 16),
            load64(after + 24), load64(after + 8), load64(after + 16));
}

/* Linux reports every process mapping and permission. Exact endpoint equality
 * supplements the full-page check; it is not a hardware memory-access trace. */
static size_t read_maps(char *buffer, size_t capacity) {
    int fd = open("/proc/self/maps", O_RDONLY | O_CLOEXEC);
    if (fd < 0) die("Cannot inspect mapping permissions");
    size_t used = 0;
    for (;;) {
        if (used == capacity) die("Mapping evidence exceeds capacity");
        ssize_t count = read(fd, buffer + used, capacity - used);
        if (count < 0) die("Cannot read mapping permissions");
        if (count == 0) break;
        used += (size_t)count;
    }
    if (close(fd) != 0) die("Cannot close mapping evidence");
    return used;
}

static void check_owned_permissions(const char *maps, uintptr_t mapping,
                                     size_t page_size) {
    const char *line = maps;
    unsigned found = 0;
    while (*line) {
        uintptr_t begin, end;
        char permissions[5];
        if (sscanf(line, "%" SCNxPTR "-%" SCNxPTR " %4s", &begin, &end, permissions) == 3) {
            for (unsigned i = 0; i < 3; ++i) {
                uintptr_t address = mapping + i * page_size;
                if (begin <= address && address + page_size <= end) {
                    if (strncmp(permissions, i == 1 ? "rw-p" : "---p", 4) != 0)
                        die("Owned alternate stack/guard permissions differ");
                    found |= 1u << i;
                }
            }
        }
        line = strchr(line, '\n');
        if (!line) break;
        ++line;
    }
    if (found != 7) die("Missing owned stack or guard mapping");
}

static void write_bytes(FILE *out, const unsigned char *begin, size_t length) {
    for (size_t i = 0; i < length; ++i) fprintf(out, "%02x", begin[i]);
}

static void prepare_case(unsigned char *page, unsigned char *before,
                          size_t page_size, uint64_t input, uint64_t flags) {
    for (size_t i = 0; i < page_size; i += 8) {
        uint64_t word = random_word();
        memcpy(page + i, &word, sizeof word);
    }
    uintptr_t root = (uintptr_t)cs_root_capture;
    memcpy(page + 24, &root, sizeof root);
    memcpy(before, page, page_size);
    for (unsigned i = 0; i < NREG; ++i) cs_requested[i] = random_word();
    cs_requested[RAX] |= UINT64_C(1);
    cs_requested[RDI] = input;
    cs_requested[RSP] = (uintptr_t)(page + 24);
    cs_requested_flags = flags;
    cs_reached = 0;
    memset(cs_after, 0, sizeof cs_after);
}

static void validate_installation(void) {
    if (memcmp(cs_before, cs_requested, sizeof cs_before) != 0 ||
        cs_before_flags != cs_requested_flags)
        die("Requested GPR/flag installation was not observed; experiment inconclusive");
}

int main(int argc, char **argv) {
    if (argc != 6) die("usage: call-stack-check OUTPUT_DIRECTORY GCC_SAME GCC_SEPARATE CLANG_SAME CLANG_SEPARATE");
    bind_inputs(argv + 2);
    uint64_t initial_flags = read_flags();
    if (initial_flags & ((UINT64_C(1) << 18) | (UINT64_C(1) << 10) |
                         (UINT64_C(1) << 8) | (UINT64_C(1) << 14) | (UINT64_C(1) << 17)))
        die("Requires ordinary user flags with AC/DF/TF/NT/VM clear");
    unsigned long cet_status = 0;
    errno = 0;
    /* Linux ARCH_SHSTK_STATUS. EINVAL/ENOSYS mean this interface is unavailable. */
    long cet_result = syscall(SYS_arch_prctl, 0x5005, &cet_status);
    int cet_errno = errno;
    if ((cet_result == 0 && cet_status != 0) ||
        (cet_result != 0 && cet_errno != EINVAL && cet_errno != ENOSYS))
        die("Requires disabled CET shadow stack; status unavailable or enabled");
    if ((uintptr_t)cs_root_capture <= UINT32_MAX) die("PIE root address must exceed 4 GiB");
    for (size_t i = 0; i < sizeof profiles / sizeof *profiles; ++i)
        if ((uintptr_t)profiles[i].begin <= UINT32_MAX) die("PIE code address must exceed 4 GiB");
    for (size_t i = 0; i < sizeof edges / sizeof *edges; ++i)
        if (oracle(edges[i].input) != edges[i].answer) die("Byte-carry oracle fails a literal edge vector");

    long page_query = sysconf(_SC_PAGESIZE);
    if (page_query < 64 || page_query > 65536 || page_query % 16 != 0)
        die("Unsupported native page size");
    size_t page_size = (size_t)page_query;
    unsigned char *mapping = mmap(NULL, page_size * 3, PROT_NONE,
                                   MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mapping == MAP_FAILED) die("Cannot allocate guarded owned stack");
    unsigned char *page = mapping + page_size;
    if (mprotect(page, page_size, PROT_READ | PROT_WRITE) != 0)
        die("Cannot make owned middle stack page writable");
    if ((uintptr_t)(page + 24) % 16 != 8) die("Wrong SysV entry stack alignment");
    unsigned char *before = malloc(page_size), *after = malloc(page_size);
    digest_context = EVP_MD_CTX_new();
    if (!before || !after || !digest_context) die("Cannot allocate snapshot storage");
    sigset_t all_signals, old_signals;
    if (sigfillset(&all_signals) != 0 ||
        sigprocmask(SIG_BLOCK, &all_signals, &old_signals) != 0)
        die("Cannot block asynchronous signals during capture");

    FILE *identity = output_file(argv[1], "identity.jsonl");
    fprintf(identity, "{\"scope\":\"native-only\",\"formal\":\"NOTRUN\","
            "\"root_entry\":\"JMP with preinstalled root RA\",\"root_capture\":\"%016" PRIxPTR "\","
            "\"stack_mapping\":\"%016" PRIxPTR "\",\"stack_page\":\"%016" PRIxPTR "\","
            "\"caller_slot_s\":\"%016" PRIxPTR "\",\"page_size\":%zu,"
            "\"private_offsets\":[8,24],\"register_order\":[\"rax\",\"rcx\",\"rdx\",\"rbx\","
            "\"rsp\",\"rbp\",\"rsi\",\"rdi\",\"r8\",\"r9\",\"r10\",\"r11\",\"r12\",\"r13\",\"r14\",\"r15\"],"
            "\"sha256_library\":\"%s\",\"cet_status_result\":%ld,\"cet_status_errno\":%d,"
            "\"cet_status_bits\":%lu,\"rng_seed\":\"d06fb17a35c290e4\","
            "\"arithmetic_flag_mask\":\"00000000000008d5\"}\n",
            (uintptr_t)cs_root_capture, (uintptr_t)mapping, (uintptr_t)page,
            (uintptr_t)(page + 24), page_size, OpenSSL_version(OPENSSL_VERSION),
            cet_result, cet_errno, cet_status);
    for (size_t i = 0; i < sizeof profiles / sizeof *profiles; ++i) {
        const struct profile *p = &profiles[i];
        char hash[65];
        sha256(p->begin, p->length, hash);
        fprintf(identity, "{\"profile\":\"%s\",\"length\":%zu,\"entry_offset\":%zu,"
                "\"text\":\"%016" PRIxPTR "\",\"entry\":\"%016" PRIxPTR "\","
                "\"helper\":\"%016" PRIxPTR "\",\"internal_continuation\":\"%016" PRIxPTR "\","
                "\"sha256\":\"%s\",\"bytes\":\"", p->name, p->length, p->entry_offset,
                (uintptr_t)p->begin, (uintptr_t)p->entry, (uintptr_t)p->helper,
                (uintptr_t)p->continuation, hash);
        write_bytes(identity, p->begin, p->length);
        fputs("\"}\n", identity);
    }
    fprintf(identity, "{\"owned_mutants_text\":\"%016" PRIxPTR "\","
            "\"good_helper\":\"%016" PRIxPTR "\",\"zero_helper\":\"%016" PRIxPTR "\",\"bytes\":\"",
            (uintptr_t)cs_mutants_begin, (uintptr_t)cs_mutant_good_helper,
            (uintptr_t)cs_mutant_zero_helper);
    write_bytes(identity, cs_mutants_begin, (uintptr_t)cs_mutants_end - (uintptr_t)cs_mutants_begin);
    fputs("\"}\n", identity);
    for (size_t i = 0; i < sizeof mutants / sizeof *mutants; ++i) {
        const struct mutant *m = &mutants[i];
        fprintf(identity, "{\"mutant\":\"%s\",\"entry\":\"%016" PRIxPTR "\","
                "\"expected_failure_mask\":%u,\"damaged_register_index\":%d,\"bytes\":\"",
                m->name, (uintptr_t)m->begin, m->category, m->damaged_register);
        write_bytes(identity, m->begin, (uintptr_t)m->end - (uintptr_t)m->begin);
        fputs("\"}\n", identity);
    }
    checked_close(identity);
    FILE *observations = output_file(argv[1], "observations.jsonl");
    FILE *pages = output_file(argv[1], "pages.bin");
    FILE *maps_before_file = output_file(argv[1], "maps-before.txt");
    FILE *maps_after_file = output_file(argv[1], "maps-after.txt");
    static char json_buffer[65536], pages_buffer[65536];
    if (setvbuf(observations, json_buffer, _IOFBF, sizeof json_buffer) != 0 ||
        setvbuf(pages, pages_buffer, _IOFBF, sizeof pages_buffer) != 0)
        die("Cannot buffer evidence");
    char maps_before[65536], maps_after[65536];
    size_t maps_before_size = read_maps(maps_before, sizeof maps_before - 1);
    maps_before[maps_before_size] = '\0';
    check_owned_permissions(maps_before, (uintptr_t)mapping, page_size);
    if (fwrite(maps_before, 1, maps_before_size, maps_before_file) != maps_before_size)
        die("Cannot write map evidence");

    uint64_t positive_count = 0, negative_count = 0, sequence = 0;
    unsigned failed = 0;
    for (size_t p = 0; p < sizeof profiles / sizeof *profiles; ++p) {
        for (unsigned f = 0; f < 128; ++f) {
            for (size_t value = 0; value < sizeof edges / sizeof *edges + 64; ++value) {
                uint64_t input = value < sizeof edges / sizeof *edges ? edges[value].input : random_word();
                prepare_case(page, before, page_size, input, flag_profile(f, initial_flags));
                cs_target = (uintptr_t)profiles[p].entry;
                cs_run();
                memcpy(after, page, page_size);
                validate_installation();
                unsigned failure = common_contract(before, after, page_size);
                bool pattern = private_pattern(p, before, after);
                if (failure || !pattern) ++failed;
                record_case(observations, pages, sequence++, profiles[p].name, false,
                            f, before, after, page_size, failure, pattern);
                ++positive_count;
            }
        }
    }
    for (size_t m = 0; m < sizeof mutants / sizeof *mutants; ++m) {
        for (unsigned f = 0; f < 128; ++f) {
            prepare_case(page, before, page_size, UINT64_C(0xf1234567fffffff0),
                         flag_profile(f, initial_flags));
            cs_target = (uintptr_t)mutants[m].begin;
            cs_run();
            memcpy(after, page, page_size);
            validate_installation();
            unsigned failure = common_contract(before, after, page_size);
            if (failure != mutants[m].category ||
                (mutants[m].damaged_register >= 0 &&
                 cs_before[mutants[m].damaged_register] == cs_after[mutants[m].damaged_register]))
                ++failed;
            record_case(observations, pages, sequence++, mutants[m].name, true,
                        f, before, after, page_size, failure, false);
            ++negative_count;
        }
    }
    size_t maps_after_size = read_maps(maps_after, sizeof maps_after - 1);
    maps_after[maps_after_size] = '\0';
    check_owned_permissions(maps_after, (uintptr_t)mapping, page_size);
    if (fwrite(maps_after, 1, maps_after_size, maps_after_file) != maps_after_size)
        die("Cannot write final map evidence");
    bool maps_equal = maps_before_size == maps_after_size &&
                      memcmp(maps_before, maps_after, maps_before_size) == 0;
    if (!maps_equal) ++failed;
    checked_close(observations);
    checked_close(pages);
    checked_close(maps_before_file);
    checked_close(maps_after_file);
    if (sigprocmask(SIG_SETMASK, &old_signals, NULL) != 0)
        die("Cannot restore signal mask");
    if (munmap(mapping, page_size * 3) != 0) die("Cannot release owned stack");
    free(before);
    free(after);
    EVP_MD_CTX_free(digest_context);
    fprintf(stderr, "native=%s positive=%" PRIu64 " negative=%" PRIu64
            " flag_profiles=128 maps_equal=%s failures=%u formal=NOTRUN\n",
            failed ? "FAIL" : "PASS", positive_count, negative_count,
            maps_equal ? "true" : "false", failed);
    return failed ? 1 : 0;
}
