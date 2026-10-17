/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <dirent.h>
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
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>

enum { RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI,
       R8, R9, R10, R11, R12, R13, R14, R15, NREG };
enum { RESULT = 1, DATA = 2, STACK = 4, SAVED = 8, FLAGS = 16, MEMORY = 32, ROOT = 64 };
enum { NPROFILE = 2, NMUTANT = 5, NIMPL = 7, NFLAG = 128, NCOUNT = 8, NSAMPLE = 8 };
static const uint64_t arithmetic_flags = UINT64_C(0x8d5);
static const unsigned saved[] = {RBX, RBP, R12, R13, R14, R15};
static const unsigned flag_positions[] = {0,2,4,6,7,11,21};
static const uint64_t counts[NCOUNT] = {0,1,2,3,7,31,257,1024};
static const uint64_t inputs[NSAMPLE] = {
    0,1,0xff,0xffffffff,UINT64_C(0x7fffffffffffffff),
    UINT64_C(0x8000000000000000),UINT64_MAX-1,UINT64_MAX
};
uint64_t cm_requested[NREG], cm_before[NREG], cm_after[NREG];
uint64_t cm_requested_flags, cm_before_flags, cm_after_flags, cm_reached;
uint64_t cm_host_rsp, cm_host_flags, cm_host_saved[6];
uintptr_t cm_target;
extern void cm_run(void), cm_root_capture(void), cm_root_capture_end(void);
#define DECLARE(n) extern const unsigned char n[], n##_end[]
#define MUTANT_DECLARE(n) DECLARE(n); extern const unsigned char n##_helper[]
DECLARE(cm_gcc);
DECLARE(cm_clang);
MUTANT_DECLARE(cm_bad_skip);
MUTANT_DECLARE(cm_bad_no_store);
MUTANT_DECLARE(cm_bad_stale);
MUTANT_DECLARE(cm_bad_outside);
MUTANT_DECLARE(cm_bad_rbx);

struct profile {
    const char *name;
    const unsigned char *begin, *end;
    size_t length, helper;
    unsigned char bytes[52];
};
static const struct profile profiles[NPROFILE] = {
    {"gcc13", cm_gcc, cm_gcc_end, 45, 38,
     {0x55,0x48,0x89,0xfd,0x53,0x48,0x89,0xd3,0x51,0x48,0x85,0xdb,0x74,0x11,
      0x48,0x89,0xef,0x48,0xff,0xcb,0xe8,0x0d,0,0,0,0x48,0x8d,0x70,1,0xeb,0xea,
      0x5a,0x48,0x89,0xf0,0x5b,0x5d,0xc3,0x48,0x89,0x37,0x48,0x8b,7,0xc3}},
    {"clang18", cm_clang, cm_clang_end, 52, 45,
     {0x48,0x89,0xf0,0x48,0x85,0xd2,0x74,0x24,0x41,0x56,0x53,0x50,0x48,0x89,
      0xd3,0x49,0x89,0xfe,0x4c,0x89,0xf7,0x48,0x89,0xc6,0xe8,0x10,0,0,0,0x48,
      0xff,0xc0,0x48,0xff,0xcb,0x75,0xed,0x48,0x83,0xc4,8,0x5b,0x41,0x5e,0xc3,
      0x48,0x89,0x37,0x48,0x8b,7,0xc3}}
};
struct mutant {
    const char *name;
    const unsigned char *begin, *end, *helper;
    uint64_t count;
    unsigned expected;
};
/* Each exact mask is part of an independent contract rejection, not "any fail".
 * In particular a resource/admission/IO failure, signal or timeout is never one. */
static const struct mutant mutants[NMUTANT] = {
    {"skip-iteration",cm_bad_skip,cm_bad_skip_end,cm_bad_skip_helper,3,RESULT|DATA},
    {"no-store",cm_bad_no_store,cm_bad_no_store_end,cm_bad_no_store_helper,3,DATA},
    {"stale-reload",cm_bad_stale,cm_bad_stale_end,cm_bad_stale_helper,1,RESULT},
    {"outside-DATA",cm_bad_outside,cm_bad_outside_end,cm_bad_outside_helper,3,MEMORY},
    {"callee-saved",cm_bad_rbx,cm_bad_rbx_end,cm_bad_rbx_helper,3,SAVED}
};

static void die(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(2);
}

/* Both complete data files AND both end-label-bounded embedded slots must bind
 * before output admission or execution. No file bytes ever become executable. */
static void bind_inputs(char **paths) {
    bool valid = true;
    for (unsigned i = 0; i < NPROFILE; ++i) {
        const struct profile *p = &profiles[i];
        unsigned char input[53];
        int fd = open(paths[i], O_RDONLY | O_CLOEXEC | O_NONBLOCK | O_NOFOLLOW);
        struct stat st;
        bool io_ok = fd >= 0 && fstat(fd, &st) == 0 && S_ISREG(st.st_mode);
        size_t used = 0;
        while (io_ok && used < sizeof input) {
            ssize_t got = read(fd, input + used, sizeof input - used);
            if (got < 0) { io_ok = false; break; }
            if (got == 0) break;
            used += (size_t)got;
        }
        if (fd >= 0 && close(fd) != 0) io_ok = false;
        if (!io_ok || used != p->length ||
            (uintptr_t)p->end - (uintptr_t)p->begin != p->length ||
            memcmp(p->begin, p->bytes, p->length) != 0 ||
            memcmp(input, p->bytes, p->length) != 0) valid = false;
    }
    if (!valid) die("Whole counted DATA8 text differs from embedded expected profiles");
}

/* Two-operand natural base-256 carry, with the ninth digit discarded. Neither
 * this oracle nor its literal checks replay the caller's counted helper loop. */
static uint64_t oracle(uint64_t left, uint64_t right) {
    uint64_t result = 0;
    unsigned carry = 0;
    for (unsigned digit = 0; digit < 8; ++digit) {
        unsigned sum = (unsigned)((left >> (digit * 8)) & 255) +
            (unsigned)((right >> (digit * 8)) & 255) + carry;
        result |= (uint64_t)(sum % 256) << (digit * 8);
        carry = sum / 256;
    }
    return result;
}
static void check_oracle(void) {
    static const struct { uint64_t x, n, rax, last; } edges[] = {
        {0,0,0,0}, {UINT64_MAX,0,UINT64_MAX,0},
        {0,1,1,0}, {0xff,1,0x100,0xff}, {0xffff,2,0x10001,0x10000},
        {0xffffff,3,0x1000002,0x1000001},
        {0xffffffff,7,0x100000006,0x100000005},
        {0xffffffffff,31,0x1000000001e,0x1000000001d},
        {0xffffffffffff,257,0x1000000000100,0x10000000000ff},
        {0xffffffffffffff,1024,0x1000000000003ff,0x1000000000003fe},
        {UINT64_C(0x7fffffffffffffff),1,UINT64_C(0x8000000000000000),
         UINT64_C(0x7fffffffffffffff)},
        {UINT64_C(0x8000000000000000),1024,UINT64_C(0x8000000000000400),
         UINT64_C(0x80000000000003ff)},
        {UINT64_MAX,1,0,UINT64_MAX}, {UINT64_MAX,2,1,0},
        {UINT64_MAX-1,3,1,0}, {UINT64_MAX,1024,1023,1022},
        /* Full-width second operands test the oracle, not native loop counts. */
        {1,UINT64_MAX,0,UINT64_MAX}, {UINT64_MAX,UINT64_MAX,UINT64_MAX-1,UINT64_MAX-2},
        {UINT64_C(0x8000000000000000),UINT64_C(0x8000000000000000),0,UINT64_MAX},
        {UINT64_C(0x123456789abcdef0),UINT64_C(0xfedcba9876543210),
         UINT64_C(0x1111111111111100),UINT64_C(0x11111111111110ff)}
    };
    for (size_t i = 0; i < sizeof edges / sizeof *edges; ++i)
        if (oracle(edges[i].x, edges[i].n) != edges[i].rax ||
            (edges[i].n && oracle(edges[i].x, edges[i].n - 1) != edges[i].last))
            die("Independent two-operand carry oracle failed");
}
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
static uint64_t profile_flags(uint64_t initial, unsigned profile) {
    uint64_t flags = initial & ~(arithmetic_flags | (UINT64_C(1) << 21));
    for (unsigned i = 0; i < 7; ++i)
        if (profile & (1u << i)) flags |= UINT64_C(1) << flag_positions[i];
    return flags;
}
static size_t target_offset(unsigned sample, size_t page_size) {
    static const size_t offsets[] = {8,9,15};
    return sample % 4 == 3 ? page_size - 8 : offsets[sample % 4];
}
static size_t span(const unsigned char *begin, const unsigned char *end) {
    return (size_t)((uintptr_t)end - (uintptr_t)begin);
}
static const unsigned char *code_begin(unsigned i) {
    return i < NPROFILE ? profiles[i].begin : mutants[i-NPROFILE].begin;
}
static const unsigned char *code_end(unsigned i) {
    return i < NPROFILE ? profiles[i].end : mutants[i-NPROFILE].end;
}
static const unsigned char *helper_begin(unsigned i) {
    return i < NPROFILE ? profiles[i].begin + profiles[i].helper : mutants[i-NPROFILE].helper;
}
static const char *code_name(unsigned i) {
    return i < NPROFILE ? profiles[i].name : mutants[i-NPROFILE].name;
}

/* Exclusive creation and a real, initially empty directory avoid truncation.
 * The admission check itself is after authentication. */
static int admit_output(const char *path, bool writing) {
    int fd = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) die("Evidence directory must be an empty real directory");
    if (writing) {
        DIR *dir = fdopendir(dup(fd));
        if (!dir) die("Cannot inspect evidence directory");
        struct dirent *item;
        errno = 0;
        while ((item = readdir(dir)))
            if (strcmp(item->d_name, ".") && strcmp(item->d_name, ".."))
                die("Evidence directory must be an empty real directory");
        if (errno || closedir(dir) != 0) die("Cannot inspect evidence directory");
    }
    return fd;
}
static FILE *open_output(int dir, const char *name, bool writing) {
    int fd = openat(dir, name, (writing ? O_WRONLY|O_CREAT|O_EXCL : O_RDONLY) |
                    O_CLOEXEC | O_NOFOLLOW, 0644);
    if (fd < 0) die("Cannot open evidence file");
    FILE *file = fdopen(fd, writing ? "wb" : "rb");
    if (!file) die("Cannot open evidence stream");
    return file;
}
static void close_output(FILE *file) {
    bool error = ferror(file) != 0;
    if (fclose(file) != 0 || error) die("Evidence IO failed");
}
static EVP_MD_CTX *digest_context;
static void sha256(const unsigned char *bytes, size_t length, unsigned char digest[32]) {
    unsigned size = 0;
    if (EVP_DigestInit_ex(digest_context, EVP_sha256(), NULL) != 1 ||
        EVP_DigestUpdate(digest_context, bytes, length) != 1 ||
        EVP_DigestFinal_ex(digest_context, digest, &size) != 1 || size != 32)
        die("SHA256 computation failed");
}
static void hex_digest(FILE *out, const unsigned char digest[32]) {
    for (unsigned i = 0; i < 32; ++i) fprintf(out, "%02x", digest[i]);
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
static void permission(const char *maps, uintptr_t address, size_t size, const char *wanted) {
    for (const char *line = maps; line; line = strchr(line, '\n')) {
        if (*line == '\n') ++line;
        uintptr_t begin, end;
        char permissions[5];
        if (sscanf(line, "%" SCNxPTR "-%" SCNxPTR " %4s", &begin, &end, permissions) == 3 &&
            begin <= address && address < end && size <= end-address) {
            if (strcmp(permissions, wanted)) die("Endpoint mapping permissions differ");
            return;
        }
    }
    die("Missing endpoint mapping");
}

/* Host-local, versioned binary records are authoritative; JSON is an index.
 * This is evidence of endpoint observations, not an access-order trace. */
struct header {
    unsigned char magic[8];
    uint64_t record_size, page_size, total, stack, data, root, root_length, initial_flags;
    uint64_t entry[NIMPL], helper[NIMPL], length[NIMPL];
    unsigned char root_hash[32], code_hash[NIMPL][32], helper_hash[NIMPL][32];
};
struct record {
    uint64_t sequence, implementation, flag_profile, count_index, sample;
    uint64_t page_size, page_offset, target_offset, entry, helper, root, reached;
    uint64_t expected_rax, expected_data, old_data, actual_data, failure, expected_mask;
    uint64_t requested[NREG], pre[NREG], post[NREG];
    uint64_t requested_flags, pre_flags, post_flags;
    unsigned char hash[4][32];
};
static void check_permissions(const char *maps, const struct header *h) {
    for (unsigned region = 0; region < 2; ++region) {
        uintptr_t base = region ? h->data : h->stack;
        permission(maps, base-h->page_size, h->page_size, "---p");
        permission(maps, base, h->page_size, "rw-p");
        permission(maps, base+h->page_size, h->page_size, "---p");
    }
    permission(maps, h->root, h->root_length, "r-xp");
    for (unsigned i = 0; i < NIMPL; ++i) permission(maps, h->entry[i], h->length[i], "r-xp");
}
static unsigned evaluate(const struct record *r, const unsigned char *pages, const struct header *h) {
    size_t size = (size_t)h->page_size, offset = (size_t)r->target_offset;
    const unsigned char *before_stack = pages, *before_data = pages+size;
    const unsigned char *after_stack = pages+2*size, *after_data = pages+3*size;
    uint64_t n = r->pre[RDX], x = r->pre[RSI];
    uint64_t expected_data = n ? oracle(x,n-1) : load64(before_data+offset);
    unsigned failure = 0;
    if (r->post[RAX] != oracle(x,n)) failure |= RESULT;
    if (load64(after_data+offset) != expected_data) failure |= DATA;
    if (r->post[RSP] != r->pre[RSP]+8) failure |= STACK;
    if (r->reached != 1 || load64(before_stack+40) != h->root) failure |= ROOT;
    for (size_t i = 0; i < sizeof saved / sizeof *saved; ++i)
        if (r->post[saved[i]] != r->pre[saved[i]]) failure |= SAVED;
    if ((r->post_flags & ~arithmetic_flags) != (r->pre_flags & ~arithmetic_flags)) failure |= FLAGS;
    for (size_t i = 0; i < size; ++i) {
        if ((i < 8 || i >= 40) && before_stack[i] != after_stack[i]) failure |= MEMORY;
        if ((i < offset || i >= offset+8) && before_data[i] != after_data[i]) failure |= MEMORY;
    }
    return failure;
}
static void write_regs(FILE *out, const uint64_t *registers) {
    fputc('[', out);
    for (unsigned i = 0; i < NREG; ++i)
        fprintf(out, "%s\"%016" PRIx64 "\"", i ? "," : "", registers[i]);
    fputc(']', out);
}
static void write_record(FILE *json, FILE *binary, FILE *pages,
                         const struct record *r, const unsigned char *memory) {
    if (fwrite(r, sizeof *r, 1, binary) != 1 ||
        fwrite(memory, (size_t)r->page_size*4, 1, pages) != 1) die("Evidence record write failed");
    fprintf(json, "{\"case\":%" PRIu64 ",\"name\":\"%s\",\"negative\":%s,"
        "\"flag_profile\":%" PRIu64 ",\"count_index\":%" PRIu64 ",\"sample\":%" PRIu64
        ",\"count\":%" PRIu64 ",\"x\":\"%016" PRIx64 "\",\"target_offset\":%" PRIu64
        ",\"page_size\":%" PRIu64 ",\"page_offset\":%" PRIu64
        ",\"entry\":\"%016" PRIx64 "\",\"helper\":\"%016" PRIx64 "\",\"root\":\"%016" PRIx64
        "\",\"requested_flags\":\"%016" PRIx64 "\",\"pre_flags\":\"%016" PRIx64
        "\",\"post_flags\":\"%016" PRIx64 "\",\"expected_rax\":\"%016" PRIx64
        "\",\"expected_data\":\"%016" PRIx64 "\",\"old_data\":\"%016" PRIx64
        "\",\"actual_data\":\"%016" PRIx64 "\",\"failure_mask\":%" PRIu64
        ",\"expected_mask\":%" PRIu64 ",\"sha256\":[",
        r->sequence,code_name((unsigned)r->implementation),r->implementation >= NPROFILE ? "true":"false",
        r->flag_profile,r->count_index,r->sample,r->pre[RDX],r->pre[RSI],r->target_offset,
        r->page_size,r->page_offset,r->entry,r->helper,r->root,r->requested_flags,r->pre_flags,
        r->post_flags,r->expected_rax,r->expected_data,r->old_data,r->actual_data,r->failure,r->expected_mask);
    for (unsigned i = 0; i < 4; ++i) {
        fputs(i ? ",\"" : "\"", json);
        hex_digest(json,r->hash[i]);
        fputc('"',json);
    }
    fputs("],\"requested\":",json); write_regs(json,r->requested);
    fputs(",\"pre\":",json); write_regs(json,r->pre);
    fputs(",\"post\":",json); write_regs(json,r->post);
    fprintf(json,",\"reached_root\":%s}\n",r->reached == 1 ? "true":"false");
}
static void make_header(struct header *h, size_t page_size, unsigned char **ram, uint64_t flags) {
    memset(h,0,sizeof *h);
    memcpy(h->magic,"CML64v1",8);
    h->record_size = sizeof(struct record); h->page_size = page_size;
    h->total = NPROFILE*NFLAG*NCOUNT*NSAMPLE + NMUTANT*NFLAG;
    h->stack = (uintptr_t)ram[0]; h->data = (uintptr_t)ram[1];
    h->root = (uintptr_t)cm_root_capture;
    h->root_length = (uintptr_t)cm_root_capture_end-(uintptr_t)cm_root_capture;
    h->initial_flags = flags;
    sha256((const unsigned char *)cm_root_capture,(size_t)h->root_length,h->root_hash);
    for (unsigned i = 0; i < NIMPL; ++i) {
        h->entry[i] = (uintptr_t)code_begin(i); h->helper[i] = (uintptr_t)helper_begin(i);
        h->length[i] = span(code_begin(i),code_end(i));
        sha256(code_begin(i),(size_t)h->length[i],h->code_hash[i]);
        sha256(helper_begin(i),span(helper_begin(i),code_end(i)),h->helper_hash[i]);
    }
}
static void write_identity(FILE *out, const struct header *h, long cet, unsigned long status,
                           int cet_errno, const sigset_t *effective) {
    fprintf(out,"format=CML64v1 record_bytes=%zu header_bytes=%zu page_size=%" PRIu64
        " root=%016" PRIx64 " root_length=%" PRIu64 " root_sha256=",sizeof(struct record),
        sizeof *h,h->page_size,h->root,h->root_length);
    hex_digest(out,h->root_hash);
    fprintf(out,"\nstack=%016" PRIx64 " data=%016" PRIx64 " S=%016" PRIx64
        " private=[8,40) original_return=[40,48) return_rsp=%016" PRIx64
        "\nregister_order=rax,rcx,rdx,rbx,rsp,rbp,rsi,rdi,r8,r9,r10,r11,r12,r13,r14,r15"
        "\nCET_query=ARCH_SHSTK_STATUS(0x5005) result=%ld status=%lu errno=%d"
        "\nCET_disabled_assumption=true IBT_not_queried=true canonical_user_RAM=true AC_DF_clear=true"
        "\nno_async_interference_assumed=true signal_mask_blocked=",
        h->stack,h->data,h->stack+40,h->stack+48,cet,status,cet_errno);
    for (int i = 1; i < NSIG; ++i) if (sigismember(effective,i) == 1) fprintf(out,"%d,",i);
    fputc('\n',out);
    for (unsigned i = 0; i < NIMPL; ++i) {
        fprintf(out,"%s entry=%016" PRIx64 " helper=%016" PRIx64 " length=%" PRIu64
            " helper_offset=%" PRIu64 " sha256=",code_name(i),h->entry[i],h->helper[i],
            h->length[i],h->helper[i]-h->entry[i]);
        hex_digest(out,h->code_hash[i]); fputs(" helper_sha256=",out);
        hex_digest(out,h->helper_hash[i]); fputc('\n',out);
    }
}
static void read_exact(FILE *file, void *buffer, size_t size) {
    if (fread(buffer,1,size,file) != size) die("Evidence is truncated or unreadable");
}
static void eof_exact(FILE *file) {
    if (fgetc(file) != EOF || ferror(file)) die("Evidence has trailing bytes or an IO error");
}

/* Replay saved machine captures and all four full pages. Coverage is keyed by
 * ACTUAL pre-RSI/RDX/RDI/flags, cross-checked against requested installation,
 * rather than accepting the recorder's schedule/printed totals as coverage. */
static int verify_records(int dir) {
    FILE *records = open_output(dir,"records.bin",false);
    FILE *pages = open_output(dir,"pages.bin",false);
    struct header h;
    read_exact(records,&h,sizeof h);
    if (memcmp(h.magic,"CML64v1",8) || h.record_size != sizeof(struct record) ||
        h.page_size < 4096 || h.page_size > 65536 || h.page_size % 8 ||
        h.total != 17024 || h.stack <= UINT32_MAX || h.data <= UINT32_MAX ||
        h.root <= UINT32_MAX || h.stack % h.page_size || h.data % h.page_size ||
        h.root_length != (uintptr_t)cm_root_capture_end-(uintptr_t)cm_root_capture)
        die("Evidence header differs from native contract");
    unsigned char digest[32];
    sha256((const unsigned char *)cm_root_capture,(size_t)h.root_length,digest);
    if (memcmp(digest,h.root_hash,32)) die("Evidence root code hash differs");
    for (unsigned i = 0; i < NIMPL; ++i) {
        sha256(code_begin(i),span(code_begin(i),code_end(i)),digest);
        if (h.length[i] != span(code_begin(i),code_end(i)) ||
            h.helper[i]-h.entry[i] != (uintptr_t)helper_begin(i)-(uintptr_t)code_begin(i) ||
            memcmp(digest,h.code_hash[i],32)) die("Evidence code identity differs");
        sha256(helper_begin(i),span(helper_begin(i),code_end(i)),digest);
        if (memcmp(digest,h.helper_hash[i],32)) die("Evidence helper hash differs");
    }
    unsigned char *memory = malloc((size_t)h.page_size*4);
    if (!memory) die("Replay allocation failed");
    unsigned char seen[NPROFILE][NFLAG][NCOUNT][NSAMPLE] = {0};
    unsigned char bad_seen[NMUTANT][NFLAG] = {0};
    uint64_t positives = 0, negatives = 0;
    for (uint64_t sequence = 0; sequence < h.total; ++sequence) {
        struct record r;
        read_exact(records,&r,sizeof r);
        if (r.sequence != sequence || r.implementation >= NIMPL || r.page_size != h.page_size ||
            r.page_offset != sequence*h.page_size*4 || r.target_offset > h.page_size-8 ||
            memcmp(r.pre,r.requested,sizeof r.pre) || r.pre_flags != r.requested_flags ||
            r.root != h.root || r.entry != h.entry[r.implementation] ||
            r.helper != h.helper[r.implementation] || r.reached != 1 ||
            r.pre[RSP] != h.stack+40 || r.pre[RDI] != h.data+r.target_offset)
            die("Evidence capture/binding differs");
        unsigned f = 0, c = NCOUNT, s = NSAMPLE;
        for (unsigned i = 0; i < 7; ++i)
            if (r.pre_flags & (UINT64_C(1)<<flag_positions[i])) f |= 1u<<i;
        if (r.flag_profile != f || r.pre_flags != profile_flags(h.initial_flags,f))
            die("Effective flag coverage differs");
        if (r.implementation < NPROFILE) {
            for (unsigned i = 0; i < NCOUNT; ++i) if (r.pre[RDX] == counts[i]) c = i;
            for (unsigned i = 0; i < NSAMPLE; ++i) if (r.pre[RSI] == inputs[i]) s = i;
            if (c == NCOUNT || s == NSAMPLE || r.count_index != c || r.sample != s ||
                r.target_offset != target_offset(s,(size_t)h.page_size) ||
                seen[r.implementation][f][c][s]++ || r.expected_mask) die("Positive coverage differs");
            ++positives;
        } else {
            unsigned m = (unsigned)r.implementation-NPROFILE;
            if (r.pre[RDX] != mutants[m].count || r.pre[RSI] != UINT64_C(0xfedcba9876543210) ||
                r.target_offset != 16 || r.sample != 0 || r.count_index != (m == 2 ? 1u : 3u) ||
                bad_seen[m][f]++ || r.expected_mask != mutants[m].expected)
                die("Negative coverage differs");
            ++negatives;
        }
        read_exact(pages,memory,(size_t)h.page_size*4);
        for (unsigned i = 0; i < 4; ++i) {
            sha256(memory+i*h.page_size,(size_t)h.page_size,digest);
            if (memcmp(digest,r.hash[i],32)) die("Evidence page SHA256 differs");
        }
        uint64_t old = load64(memory+h.page_size+r.target_offset);
        uint64_t expected = r.pre[RDX] ? oracle(r.pre[RSI],r.pre[RDX]-1) : old;
        if ((r.pre[RDX] && old == expected) || (!r.pre[RDX] && old == r.pre[RSI]) ||
            r.old_data != old || r.expected_rax != oracle(r.pre[RSI],r.pre[RDX]) ||
            r.expected_data != expected ||
            r.actual_data != load64(memory+3*h.page_size+r.target_offset) ||
            r.failure != evaluate(&r,memory,&h) || r.failure != r.expected_mask)
            die("Evidence contract replay differs");
    }
    eof_exact(records); eof_exact(pages);
    for (unsigned p = 0; p < NPROFILE; ++p)
        for (unsigned f = 0; f < NFLAG; ++f)
            for (unsigned c = 0; c < NCOUNT; ++c)
                for (unsigned s = 0; s < NSAMPLE; ++s)
                    if (seen[p][f][c][s] != 1) die("Incomplete positive evidence");
    for (unsigned m = 0; m < NMUTANT; ++m)
        for (unsigned f = 0; f < NFLAG; ++f)
            if (bad_seen[m][f] != 1) die("Incomplete negative evidence");
    close_output(records); close_output(pages); free(memory);
    fprintf(stderr,"replay=PASS positive=%" PRIu64 " negative=%" PRIu64
        " flag_profiles=128 counts=8 inputs=8 page_hashes=68096 exact_masks=true formal=NOTRUN\n",
        positives,negatives);
    return 0;
}

int main(int argc, char **argv) {
    bool replay = argc == 5 && strcmp(argv[1],"--verify") == 0;
    if ((!replay && argc != 4) || (argc == 5 && !replay))
        die("usage: call-memory-loop64-check [--verify] DIRECTORY GCC_TEXT CLANG_TEXT");
    bind_inputs(argv+(replay ? 3 : 2));
    check_oracle();
    int dir = admit_output(argv[replay ? 2 : 1],!replay);
    digest_context = EVP_MD_CTX_new();
    if (!digest_context) die("Digest allocation failed");
    if (replay) {
        int status = verify_records(dir);
        EVP_MD_CTX_free(digest_context);
        if (close(dir) != 0) die("Cannot close evidence directory");
        return status;
    }
    uint64_t initial_flags = read_flags();
    if (initial_flags & ((UINT64_C(1)<<18)|(UINT64_C(1)<<10)|(UINT64_C(1)<<8)|
                         (UINT64_C(1)<<14)|(UINT64_C(1)<<17)))
        die("Requires ordinary flags with AC/DF/TF/NT/VM clear");
    unsigned long cet_status = 0;
    errno = 0;
    long cet_result = syscall(SYS_arch_prctl,0x5005,&cet_status);
    int cet_errno = errno;
    if ((cet_result == 0 && cet_status != 0) ||
        (cet_result != 0 && cet_errno != EINVAL && cet_errno != ENOSYS))
        die("Requires disabled CET shadow stack");
    if ((uintptr_t)cm_root_capture <= UINT32_MAX) die("Requires PIE root above 4 GiB");
    long page_result = sysconf(_SC_PAGESIZE);
    if (page_result < 4096 || page_result > 65536 || page_result % 8) die("Unsupported page size");
    size_t page_size = (size_t)page_result;
    unsigned char *mappings[2], *ram[2];
    for (unsigned i = 0; i < 2; ++i) {
        mappings[i] = mmap(NULL,page_size*3,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
        if (mappings[i] == MAP_FAILED) die("Cannot allocate guarded RAM");
        ram[i] = mappings[i]+page_size;
        if ((uintptr_t)ram[i] <= UINT32_MAX) die("Requires owned RAM above 4 GiB");
        if (mprotect(ram[i],page_size,PROT_READ|PROT_WRITE)) die("Cannot initialize RAM permissions");
    }
    unsigned char *memory = malloc(page_size*4);
    char *maps_before = malloc(131072), *maps_after = malloc(131072);
    if (!memory || !maps_before || !maps_after) die("Capture allocation failed");
    struct header h;
    make_header(&h,page_size,ram,initial_flags);
    for (unsigned i = 0; i < NIMPL; ++i)
        if (h.entry[i] <= UINT32_MAX) die("Requires PIE code above 4 GiB");
    FILE *json = open_output(dir,"observations.jsonl",true);
    FILE *binary = open_output(dir,"records.bin",true);
    FILE *pages = open_output(dir,"pages.bin",true);
    FILE *identity = open_output(dir,"identity.txt",true);
    FILE *mapping_before = open_output(dir,"maps-before.txt",true);
    FILE *mapping_after = open_output(dir,"maps-after.txt",true);
    /* Force allocations before the before-maps endpoint. These buffers stay
     * fixed throughout the loop; no lazy stream allocation changes maps. */
    FILE *streams[] = {json,binary,pages,identity,mapping_before,mapping_after};
    for (size_t i = 0; i < sizeof streams / sizeof *streams; ++i)
        if (setvbuf(streams[i],NULL,_IONBF,0)) die("Cannot configure evidence streams");
    sigset_t blocked, old_signals, effective;
    if (sigfillset(&blocked) || sigprocmask(SIG_SETMASK,&blocked,&old_signals) ||
        sigprocmask(SIG_SETMASK,NULL,&effective)) die("Cannot block asynchronous signals");
    write_identity(identity,&h,cet_result,cet_status,cet_errno,&effective);
    close_output(identity);
    if (fwrite(&h,sizeof h,1,binary) != 1) die("Evidence header write failed");
    size_t maps_size = read_maps(maps_before,131072);
    check_permissions(maps_before,&h);
    if (fwrite(maps_before,1,maps_size,mapping_before) != maps_size) die("Mapping evidence write failed");
    uint64_t sequence = 0, positives = 0, negatives = 0;
    unsigned failures = 0;
    for (unsigned f = 0; f < NFLAG; ++f)
        for (unsigned implementation = 0; implementation < NIMPL; ++implementation) {
            bool negative = implementation >= NPROFILE;
            for (unsigned c = 0; c < (negative ? 1u : NCOUNT); ++c)
                for (unsigned s = 0; s < (negative ? 1u : NSAMPLE); ++s) {
                    unsigned m = negative ? implementation-NPROFILE : 0;
                    uint64_t n = negative ? mutants[m].count : counts[c];
                    uint64_t x = negative ? UINT64_C(0xfedcba9876543210) : inputs[s];
                    size_t offset = negative ? 16 : target_offset(s,page_size);
                    for (unsigned region = 0; region < 2; ++region)
                        for (size_t i = 0; i < page_size; i += 8) {
                            uint64_t word = random_word();
                            memcpy(ram[region]+i,&word,8);
                        }
                    uint64_t old = random_word(), avoid = n ? oracle(x,n-1) : x;
                    if (old == avoid) old ^= 1;
                    memcpy(ram[1]+offset,&old,8);
                    memcpy(ram[0]+40,&h.root,8);
                    memcpy(memory,ram[0],page_size);
                    memcpy(memory+page_size,ram[1],page_size);
                    for (unsigned i = 0; i < NREG; ++i) cm_requested[i] = random_word();
                    cm_requested[RSP] = h.stack+40; cm_requested[RDI] = h.data+offset;
                    cm_requested[RSI] = x; cm_requested[RDX] = n;
                    cm_requested_flags = profile_flags(initial_flags,f);
                    cm_reached = 0; cm_target = h.entry[implementation];
                    cm_run();
                    if (memcmp(cm_before,cm_requested,sizeof cm_before) ||
                        cm_before_flags != cm_requested_flags)
                        die("Requested register/flag installation was not observed");
                    memcpy(memory+2*page_size,ram[0],page_size);
                    memcpy(memory+3*page_size,ram[1],page_size);
                    struct record r;
                    memset(&r,0,sizeof r);
                    r.sequence = sequence; r.implementation = implementation; r.flag_profile = f;
                    r.count_index = negative ? (m == 2 ? 1 : 3) : c; r.sample = s;
                    r.page_size = page_size; r.page_offset = sequence*page_size*4;
                    r.target_offset = offset; r.entry = h.entry[implementation];
                    r.helper = h.helper[implementation]; r.root = h.root; r.reached = cm_reached;
                    memcpy(r.requested,cm_requested,sizeof r.requested);
                    memcpy(r.pre,cm_before,sizeof r.pre); memcpy(r.post,cm_after,sizeof r.post);
                    r.requested_flags = cm_requested_flags; r.pre_flags = cm_before_flags;
                    r.post_flags = cm_after_flags; r.expected_rax = oracle(x,n);
                    r.expected_data = n ? oracle(x,n-1) : old;
                    r.old_data = old; r.actual_data = load64(memory+3*page_size+offset);
                    r.expected_mask = negative ? mutants[m].expected : 0;
                    r.failure = evaluate(&r,memory,&h);
                    if (r.failure != r.expected_mask) ++failures;
                    for (unsigned i = 0; i < 4; ++i) sha256(memory+i*page_size,page_size,r.hash[i]);
                    write_record(json,binary,pages,&r,memory);
                    ++sequence;
                    if (negative) ++negatives; else ++positives;
                }
        }
    size_t after_maps_size = read_maps(maps_after,131072);
    check_permissions(maps_after,&h);
    bool maps_equal = maps_size == after_maps_size && !memcmp(maps_before,maps_after,maps_size);
    if (!maps_equal || sequence != h.total) ++failures;
    if (fwrite(maps_after,1,after_maps_size,mapping_after) != after_maps_size)
        die("Mapping evidence write failed");
    close_output(json); close_output(binary); close_output(pages);
    close_output(mapping_before); close_output(mapping_after);
    if (sigprocmask(SIG_SETMASK,&old_signals,NULL)) die("Cannot restore signal mask");
    for (unsigned i = 0; i < 2; ++i)
        if (munmap(mappings[i],page_size*3)) die("Cannot release RAM");
    free(memory); free(maps_before); free(maps_after); EVP_MD_CTX_free(digest_context);
    if (close(dir)) die("Cannot close evidence directory");
    fprintf(stderr,"native=%s positive=%" PRIu64 " negative=%" PRIu64
        " flag_profiles=128 counts=8 inputs=8 maps_equal=%s failures=%u formal=NOTRUN\n",
        failures ? "FAIL":"PASS",positives,negatives,maps_equal ? "true":"false",failures);
    return failures ? 1 : 0;
}
