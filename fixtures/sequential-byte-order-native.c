/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <inttypes.h>
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error "The byte-order CPU fixture requires Linux x86-64"
#endif

/* GNU23 (GCC 13: -std=gnu2x), -O2 -Wall -Wextra -Werror -Wpedantic
 * -mno-red-zone. Only project-owned, statically linked instructions execute.
 * No corpus ELF, generated executable buffer or file-supplied code executes.
 *
 * CPU results and PUSHFQ observations are the oracle; no arithmetic result or
 * flag formula is implemented here. Every probe brackets exactly one literal
 * instruction, records all sixteen GPRs internally, checks their frame, and
 * restores DF before C resumes. The stack used by instrumentation is outside
 * the modeled operand footprint. Signals, MMIO and privileged flags are out
 * of scope. Ordinary operand RAM is read-only, with its last byte immediately
 * followed by a PROT_NONE page. Three actual fault controls check a guard-byte
 * read, a widened four-byte read at the last readable byte, and a write to
 * the read-only byte. Register probes have no operand RAM.
 *
 * Stream v1, little endian, no native struct layout:
 * header[48]: "SBONAT1\n", u32 version=1, total=15648, probes=35,
 * recordBytes=72, mem=8192, reg=512, cmp=3104, sub=3648, rejected=192,
 * reserved=0. Records ordered by probe, left index, right index, variant:
 *   0 u16 probe; 2 u8 operation; 3 u8 source (255 for RAM); 4 u8 dest;
 *   5 u8 sourceBytes; 6 u8 destinationBytes; 7 u8 instructionBytes;
 *   8 u16 leftIndex; 10 u16 rightIndex; 12 u8 variant;
 *   13 u8 CPU checks (RAM/prestate/nonarithmetic-flags/DF, all four set);
 *   14 u16 reserved=0; 16 linked instruction[5], zero padded;
 *   21 u64 flagsBefore; 29 u64 flagsAfter;
 *   37 u64 destinationBefore; 45 u64 sourceBefore;
 *   53 u64 destinationAfter; 61 u64 sourceAfter;
 *   69 u16 actual unchanged-GPR mask; 71 u8 reserved=0.
 * Operations 1..4 are memory MOVZX, register MOVZX, CMP8 and SUB32;
 * 5..7 are actual AH encodings deliberately rejected by the model subset.
 * GPR indices follow x86 encoding order. High-byte negative metadata names
 * the containing RAX; its full prestate distinguishes AH from AL/SPL.
 *
 * Host addresses, native RIP and ASLR locations never enter the stream.
 * Memory address registers are checked against the real input pointer, then
 * relocated to fixed logical base/index values. A destination which aliases
 * the base is normalized only in the BEFORE field; its AFTER value is the
 * actual CPU result. Other host-address GPRs and RSP appear only in the
 * unchanged-GPR mask. This relocation is finite evidence, not a CPU/OS,
 * source, concurrency or address-space refinement theorem or certificate.
 */

enum { MEM = 1, REG = 2, CMP = 3, SUB = 4, HIGH_MOV = 5,
       HIGH_CMP_SOURCE = 6, HIGH_CMP_DEST = 7, PROBES = 35,
       RECORD_BYTES = 72, TOTAL = 15648 };

static const uint32_t byte_corners[16] = {
    0, 1, 2, 3, 0xf, 0x10, 0x55, 0x7e,
    0x7f, 0x80, 0x81, 0xaa, 0xf0, 0xfe, 0xff, 0x40
};
static const uint32_t word_corners[16] = {
    0, 1, 0xf, 0x10, 0x7f, 0x80, 0xff, 0x100,
    0xffff, 0x10000, 0x1000000, 0x7fffffff,
    0x80000000, 0x80000001, 0xfffffffe, 0xffffffff
};
static const uint64_t patterns[4] = { 0, 0x8d5, 0x891, 0x44 };
static const uint64_t poison[16] = {
    UINT64_C(0x123456789abcde40), UINT64_C(0x23456789abcdef51),
    UINT64_C(0x3456789abcdef062), UINT64_C(0x456789abcdef0173),
    UINT64_C(0x56789abcdef01284), UINT64_C(0x6789abcdef012395),
    UINT64_C(0x789abcdef01234a6), UINT64_C(0x89abcdef012345b7),
    UINT64_C(0x9abcdef0123456c8), UINT64_C(0xabcdef01234567d9),
    UINT64_C(0xbcdef012345678ea), UINT64_C(0xcdef0123456789fb),
    UINT64_C(0xdef0123456789a0c), UINT64_C(0xef0123456789ab1d),
    UINT64_C(0xf0123456789abc2e), UINT64_C(0x0123456789abcd3f)
};

/* Fixed assembly storage is private to this single-threaded executable.
 * RIP-relative MOV stores and PUSHFQ/POP do not consume a scratch GPR. */
struct snapshot { uint64_t gpr[16], flags; };
static volatile uint64_t native_input[16] __attribute__((used));
static volatile uint64_t native_seed __attribute__((used));
static volatile struct snapshot native_before __attribute__((used));
static volatile struct snapshot native_after __attribute__((used));

#define LOAD(R, O) "movq native_input+" #O "(%rip), %" #R "\n\t"
#define SAVE(S, R, O) "movq %" #R ", " #S "+" #O "(%rip)\n\t"
#define SNAP(S) \
    SAVE(S, rax, 0) SAVE(S, rcx, 8) SAVE(S, rdx, 16) SAVE(S, rbx, 24) \
    SAVE(S, rsp, 32) SAVE(S, rbp, 40) SAVE(S, rsi, 48) SAVE(S, rdi, 56) \
    SAVE(S, r8, 64) SAVE(S, r9, 72) SAVE(S, r10, 80) SAVE(S, r11, 88) \
    SAVE(S, r12, 96) SAVE(S, r13, 104) SAVE(S, r14, 112) SAVE(S, r15, 120) \
    "pushfq\n\tpopq " #S "+128(%rip)\n\t"
#define PROBE(N, BYTES) \
    extern void byte_order_run_##N(void); \
    extern const uint8_t byte_order_code_##N[], byte_order_end_##N[]; \
    __asm__(".text\n\t.p2align 4\n\t.globl byte_order_run_" #N "\n\t" \
      ".type byte_order_run_" #N ",@function\nbyte_order_run_" #N ":\n\t" \
      "pushq %rbx\n\tpushq %rbp\n\tpushq %r12\n\tpushq %r13\n\t" \
      "pushq %r14\n\tpushq %r15\n\t" \
      LOAD(rax, 0) LOAD(rcx, 8) LOAD(rdx, 16) LOAD(rbx, 24) \
      LOAD(rbp, 40) LOAD(rsi, 48) LOAD(rdi, 56) LOAD(r8, 64) LOAD(r9, 72) \
      LOAD(r10, 80) LOAD(r11, 88) LOAD(r12, 96) LOAD(r13, 104) \
      LOAD(r14, 112) LOAD(r15, 120) \
      "pushq native_seed(%rip)\n\tpopfq\n\t" SNAP(native_before) \
      ".globl byte_order_code_" #N "\nbyte_order_code_" #N ":\n\t.byte " BYTES "\n\t" \
      ".globl byte_order_end_" #N "\nbyte_order_end_" #N ":\n\t" \
      SNAP(native_after) "cld\n\t" \
      "popq %r15\n\tpopq %r14\n\tpopq %r13\n\tpopq %r12\n\t" \
      "popq %rbp\n\tpopq %rbx\n\tret\n\t" \
      ".size byte_order_run_" #N ",.-byte_order_run_" #N "\n\t");

PROBE(0,  "0x0f,0xb6,0x0c,0x07")
PROBE(1,  "0x0f,0xb6,0x04,0x0f")
PROBE(2,  "0x44,0x0f,0xb6,0x04,0x06")
PROBE(3,  "0x44,0x0f,0xb6,0x04,0x0e")
PROBE(4,  "0x45,0x0f,0xb6,0x0c,0x00")
PROBE(5,  "0x47,0x0f,0xb6,0x14,0x01")
PROBE(6,  "0x0f,0xb6,0x00")
PROBE(7,  "0x45,0x0f,0xb6,0x00")
PROBE(8,  "0x0f,0xb6,0xc1")
PROBE(9,  "0x0f,0xb6,0xc0")
PROBE(10, "0x44,0x0f,0xb6,0xc1")
PROBE(11, "0x41,0x0f,0xb6,0xc1")
PROBE(12, "0x45,0x0f,0xb6,0xc1")
PROBE(13, "0x45,0x0f,0xb6,0xc0")
PROBE(14, "0x45,0x0f,0xb6,0xe5")
PROBE(15, "0x40,0x0f,0xb6,0xc6")
PROBE(16, "0x44,0x38,0xc1")
PROBE(17, "0x44,0x38,0xc0")
PROBE(18, "0x41,0x38,0xc1")
PROBE(19, "0x45,0x38,0xca")
PROBE(20, "0x45,0x38,0xc0")
PROBE(21, "0x40,0x38,0xee")
PROBE(22, "0x45,0x3a,0xca")
PROBE(23, "0x44,0x29,0xc0")
PROBE(24, "0x41,0x29,0xc1")
PROBE(25, "0x45,0x29,0xca")
PROBE(26, "0x45,0x29,0xc0")
PROBE(27, "0x29,0xc0")
PROBE(28, "0x45,0x2b,0xca")
PROBE(29, "0x29,0xc8")
PROBE(30, "0x41,0x29,0xc8")
PROBE(31, "0x44,0x29,0xc8")
PROBE(32, "0x0f,0xb6,0xc4")
PROBE(33, "0x38,0xe0")
PROBE(34, "0x38,0xc4")
#undef PROBE

struct probe {
    void (*run)(void);
    const uint8_t *code, *end;
    unsigned int operation, destination, source, base, index, length;
};
#define ENTRY(N, OP, D, S, B, I, L) \
    { byte_order_run_##N, byte_order_code_##N, byte_order_end_##N, OP, D, S, B, I, L }
static const struct probe probes[PROBES] = {
    ENTRY(0,MEM,1,255,7,0,4), ENTRY(1,MEM,0,255,7,1,4),
    ENTRY(2,MEM,8,255,6,0,5), ENTRY(3,MEM,8,255,6,1,5),
    ENTRY(4,MEM,9,255,8,0,5), ENTRY(5,MEM,10,255,9,8,5),
    ENTRY(6,MEM,0,255,0,255,3), ENTRY(7,MEM,8,255,8,255,4),
    ENTRY(8,REG,0,1,255,255,3), ENTRY(9,REG,0,0,255,255,3),
    ENTRY(10,REG,8,1,255,255,4), ENTRY(11,REG,0,9,255,255,4),
    ENTRY(12,REG,8,9,255,255,4), ENTRY(13,REG,8,8,255,255,4),
    ENTRY(14,REG,12,13,255,255,4), ENTRY(15,REG,0,6,255,255,4),
    ENTRY(16,CMP,1,8,255,255,3), ENTRY(17,CMP,0,8,255,255,3),
    ENTRY(18,CMP,9,0,255,255,3), ENTRY(19,CMP,10,9,255,255,3),
    ENTRY(20,CMP,8,8,255,255,3), ENTRY(21,CMP,6,5,255,255,3),
    ENTRY(22,CMP,9,10,255,255,3), ENTRY(23,SUB,0,8,255,255,3),
    ENTRY(24,SUB,9,0,255,255,3), ENTRY(25,SUB,10,9,255,255,3),
    ENTRY(26,SUB,8,8,255,255,3), ENTRY(27,SUB,0,0,255,255,2),
    ENTRY(28,SUB,9,10,255,255,3), ENTRY(29,SUB,0,1,255,255,2),
    ENTRY(30,SUB,8,1,255,255,3), ENTRY(31,SUB,0,9,255,255,3),
    ENTRY(32,HIGH_MOV,0,0,255,255,3),
    ENTRY(33,HIGH_CMP_SOURCE,0,0,255,255,2),
    ENTRY(34,HIGH_CMP_DEST,0,0,255,255,2)
};
#undef ENTRY

static void fail(const char *message)
{
    fputs(message, stderr);
    fputc('\n', stderr);
    exit(1);
}

static void integer(FILE *output, uint64_t value, unsigned int width)
{
    for (unsigned int i = 0; i < width; ++i)
        if (fputc((int)((value >> (8 * i)) & 255), output) == EOF) {
            perror("write"); exit(2);
        }
}

static void protect(uint8_t *mapping, size_t length, int permission)
{
    if (mprotect(mapping, length, permission) != 0) { perror("mprotect"); exit(2); }
}

static sigjmp_buf guard_jump;
static volatile sig_atomic_t guard_armed;

static void guard_signal(int number)
{
    if (!guard_armed) _Exit(128 + number);
    guard_armed = 0;
    siglongjmp(guard_jump,1);
}

static void guard_fault(unsigned int kind, const uint8_t *address)
{
    if (sigsetjmp(guard_jump,1) == 0) {
        guard_armed = 1;
        if (kind == 0)
            __asm__ volatile("movzbl (%0), %%eax" : : "r" (address) : "rax", "memory");
        else if (kind == 1)
            __asm__ volatile("movl (%0), %%eax" : : "r" (address) : "rax", "memory");
        else
            __asm__ volatile("movb $0x5a, (%0)" : : "r" (address) : "memory");
        guard_armed = 0;
        fail("native guard/RO fault control unexpectedly succeeded");
    }
}

static void check_guard(uint8_t *mapping, size_t page)
{
    struct sigaction action = { .sa_handler = guard_signal }, old_segv, old_bus;
    if (sigemptyset(&action.sa_mask) != 0 ||
        sigaction(SIGSEGV,&action,&old_segv) != 0 ||
        sigaction(SIGBUS,&action,&old_bus) != 0) {
        perror("sigaction"); exit(2);
    }
    protect(mapping,page,PROT_READ | PROT_WRITE);
    mapping[page - 1] = 0;
    protect(mapping,page,PROT_READ);
    guard_fault(0,mapping + page);
    guard_fault(1,mapping + page - 1);
    guard_fault(2,mapping + page - 1);
    if (sigaction(SIGSEGV,&old_segv,NULL) != 0 || sigaction(SIGBUS,&old_bus,NULL) != 0) {
        perror("restore sigaction"); exit(2);
    }
}

static uint64_t dirty(unsigned int value, unsigned int variant, int source)
{
    uint64_t high = variant % 2 == 0 ? UINT64_C(0xa5c3d2e100000000)
        : UINT64_C(0x19b7f06d00000000);
    if (source != 0) high ^= UINT64_C(0x5aa5ff0000000000);
    return high | value;
}

static void observe(FILE *output, unsigned int id, unsigned int li,
    unsigned int ri, unsigned int variant, uint8_t *operand)
{
    const struct probe *p = &probes[id];
    unsigned int pattern = (li + 3 * ri + variant) % 4;
    for (unsigned int r = 0; r < 16; ++r) native_input[r] = poison[r];
    native_seed = UINT64_C(0x602) | patterns[pattern];
    uint64_t logical_destination;
    if (p->operation == MEM) {
        native_input[p->index == 255 ? p->base : p->index] = UINT64_C(0x100000003);
        native_input[p->base] = (uintptr_t)operand -
            (p->index == 255 ? 0 : native_input[p->index]);
        logical_destination = p->destination == p->base
            ? UINT64_C(0x300000024) : native_input[p->destination];
    } else if (p->operation >= HIGH_MOV) {
        /* Independent AH and AL values, also distinct from RSI's low byte. */
        native_input[0] = dirty(byte_corners[li] | (byte_corners[(li + 5) % 16] << 8), variant, 0);
        logical_destination = native_input[p->destination];
    } else {
        const uint32_t *corners = p->operation == SUB ? word_corners : byte_corners;
        native_input[p->destination] = dirty(corners[li], variant, 0);
        if (p->source != p->destination)
            native_input[p->source] = dirty(corners[p->operation == REG ? li : ri], variant, 1);
        logical_destination = native_input[p->destination];
    }
    p->run();
    for (unsigned int r = 0; r < 16; ++r)
        if (r != 4 && native_before.gpr[r] != native_input[r])
            fail("assembly prestate differs from requested GPR inputs");
    uint16_t frame = 0;
    for (unsigned int r = 0; r < 16; ++r) {
        if (native_before.gpr[r] == native_after.gpr[r]) frame |= (uint16_t)(1u << r);
        else if (r != p->destination || p->operation == CMP || p->operation >= HIGH_CMP_SOURCE)
            fail("instruction violated full native GPR frame");
    }
    if ((native_before.flags & UINT64_C(0xcd5)) !=
        (UINT64_C(0x400) | patterns[pattern])) fail("incoming flags/DF not exercised");
    if (((native_before.flags ^ native_after.flags) & ~UINT64_C(0x8d5)) != 0)
        fail("instruction changed nonarithmetic flags");
    if ((p->operation == MEM || p->operation == REG || p->operation == HIGH_MOV) &&
        native_before.flags != native_after.flags) fail("MOVZX changed flags");
    if (p->operation == MEM && *operand != li) fail("MOVZX changed read-only RAM");
    if ((uintptr_t)p->end - (uintptr_t)p->code != p->length) fail("linked instruction length differs");

    integer(output,id,2); integer(output,p->operation,1);
    integer(output,p->source,1); integer(output,p->destination,1);
    integer(output,p->operation == SUB ? 4 : 1,1);
    integer(output,p->operation == CMP || p->operation >= HIGH_CMP_SOURCE ? 1 : 4,1);
    integer(output,p->length,1); integer(output,li,2); integer(output,ri,2);
    integer(output,variant,1); integer(output,15,1); integer(output,0,2);
    for (unsigned int i = 0; i < 5; ++i) integer(output,i < p->length ? p->code[i] : 0,1);
    integer(output,native_before.flags,8); integer(output,native_after.flags,8);
    integer(output,logical_destination,8);
    integer(output,p->operation == MEM ? *operand : native_before.gpr[p->source],8);
    integer(output,native_after.gpr[p->destination],8);
    integer(output,p->operation == MEM ? *operand : native_after.gpr[p->source],8);
    integer(output,frame,2); integer(output,0,1);
}

int main(int argc, char **argv)
{
    if (argc != 2) { fputs("usage: sequential-byte-order-native CAPTURE.bin\n",stderr); return 2; }
    long page = sysconf(_SC_PAGESIZE);
    if (page < 8) fail("invalid system page size");
    uint8_t *mapping = mmap(NULL,(size_t)page * 2,PROT_NONE,MAP_PRIVATE | MAP_ANONYMOUS,-1,0);
    if (mapping == MAP_FAILED) { perror("mmap"); return 2; }
    uint8_t *operand = mapping + page - 1;
    check_guard(mapping,(size_t)page);
    FILE *output = fopen(argv[1],"wbx");
    if (output == NULL) { perror("exclusive capture create"); return 2; }
    if (fwrite("SBONAT1\n",1,8,output) != 8) fail("header write failed");
    const uint32_t header[10] = {1,TOTAL,PROBES,RECORD_BYTES,8192,512,3104,3648,192,0};
    for (unsigned int i = 0; i < 10; ++i) integer(output,header[i],4);
    unsigned int count = 0;
    for (unsigned int id = 0; id < PROBES; ++id) {
        const struct probe *p = &probes[id];
        unsigned int left_count = p->operation == MEM ? 256 : 16;
        unsigned int right_count = (p->operation == CMP || p->operation == SUB) &&
            p->destination != p->source ? 16 : 1;
        unsigned int variant_count = p->operation == CMP || p->operation == SUB ? 2 : 4;
        for (unsigned int li = 0; li < left_count; ++li) {
            if (p->operation == MEM) {
                protect(mapping,(size_t)page,PROT_READ | PROT_WRITE);
                *operand = (uint8_t)li;
                protect(mapping,(size_t)page,PROT_READ);
            }
            for (unsigned int ri = 0; ri < right_count; ++ri)
                for (unsigned int variant = 0; variant < variant_count; ++variant) {
                    observe(output,id,li,ri,variant,operand);
                    ++count;
                }
        }
    }
    if (count != TOTAL) fail("incomplete native coverage");
    if (fclose(output) != 0) { perror("fclose"); return 2; }
    if (munmap(mapping,(size_t)page * 2) != 0) { perror("munmap"); return 2; }
    puts("15648 CPU records: 8192 DATA1 guard loads, 512 register MOVZX, 3104 CMP8, 3648 SUB32, 192 high-byte subset negatives; native GPR/RAM/flags/DF checks and 3 actual guard/RO fault controls passed");
    return 0;
}
