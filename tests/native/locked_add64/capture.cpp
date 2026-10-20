/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include "capture.h"
#include <array>
#include <cinttypes>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <signal.h>
#include <vector>

extern "C" {
edsl_ladd_snapshot edsl_ladd_input{}, edsl_ladd_before{}, edsl_ladd_after{};
}
namespace {
constexpr uint64_t arithmetic_flags = 0x8d5;
constexpr std::array<unsigned, 12> bases{0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 14, 15};
constexpr std::array<uint64_t, 8> old_values{
    0x78563412ffffffff, UINT64_MAX, 0x8000000000000000, 0x7fffffffffffffff,
    0xefcdab8967452301, 0x0123456789abcdef, 0, 0xf};
constexpr std::array<uint64_t, 8> deltas{
    1, 1, 0x8000000000000001, 1, 0, 0x8765432100000001, 0, 1};
constexpr std::array<uint64_t, 4> flag_requests{0x202, 0xed7, 0x200202, 0x200ed7};

[[noreturn]] void fail(const char *message, int status = 1) {
    std::fprintf(stderr, "FAIL fixture/validation: %s; no real-defect claim\n", message);
    std::exit(status);
}
bool supported_environment() {
    // CET/LA57 transitions, faults and asynchronous interference are not modeled.
    FILE *status = std::fopen("/proc/self/status", "r");
    if (!status) return false;
    char line[1024];
    bool cet = false;
    while (std::fgets(line, sizeof line, status))
        if (std::strncmp(line, "x86_Thread_features:", 20) == 0 &&
            (std::strstr(line, "shstk") || std::strstr(line, "ibt"))) cet = true;
    const bool good = !std::ferror(status);
    std::fclose(status);
    return good && !cet;
}
bool extraction_matches(const char *path, size_t section_size) {
    FILE *file = std::fopen(path, "rb");
    if (!file) return false;
    std::vector<unsigned char> extracted(section_size + 1);
    const size_t count = std::fread(extracted.data(), 1, extracted.size(), file);
    const bool matches = !std::ferror(file) && count == section_size &&
        std::memcmp(extracted.data(), edsl_ladd_section_begin, section_size) == 0;
    std::fclose(file);
    return matches;
}
void field(uint64_t value) { std::printf("\t%" PRIu64, value); }
void bytes(const std::array<unsigned char, 5> &code) {
    for (const auto byte : code) field(byte);
}
void registers(const edsl_ladd_snapshot &state) {
    for (const auto value : state.registers) field(value);
}
}

int main(int argc, char **argv) {
    if (argc != 2) fail("usage: capture OWN_FINAL_SECTION_EXTRACTION", 2);
    const auto section_size = reinterpret_cast<uintptr_t>(edsl_ladd_section_end) -
        reinterpret_cast<uintptr_t>(edsl_ladd_section_begin);
    const auto table_size = reinterpret_cast<uintptr_t>(edsl_ladd_windows_end) -
        reinterpret_cast<uintptr_t>(edsl_ladd_windows);
    if (!section_size || section_size > 128 * 1024 || table_size != 384 * sizeof(edsl_ladd_window))
        fail("unsupported linked section/table span", 2);
    // This file remains DATA. Only statically linked, project-owned windows run.
    if (!extraction_matches(argv[1], section_size)) {
        std::fputs("Final ELF section extraction differs from executed bytes\n", stderr);
        return 2;
    }
    if (!supported_environment()) fail("unsupported Linux/CET environment", 2);
    sigset_t blocked, previous;
    if (sigfillset(&blocked) || sigprocmask(SIG_BLOCK, &blocked, &previous))
        fail("cannot block asynchronous signals", 2);

    alignas(64) std::array<uint64_t, 3> memory{};
    const uint64_t address = reinterpret_cast<uintptr_t>(&memory[1]);
    if ((address & 7) || address >= (UINT64_C(1) << 47)) fail("unsupported owned RAM address", 2);
    size_t count = 0, aliases = 0, rsp_sources = 0, x_variants = 0, high_responses = 0;
    uint64_t status_set = 0, status_clear = 0;
    std::puts("locked-add64-native-v1");
    for (size_t index = 0; index < 384; ++index) {
        const auto &window = edsl_ladd_windows[index];
        const unsigned source = index / 24;
        const unsigned base = bases[(index / 2) % bases.size()];
        const unsigned ignored_x = index % 2;
        if (window.source != source || window.base != base || window.ignored_x != ignored_x ||
            reinterpret_cast<uintptr_t>(window.end) - reinterpret_cast<uintptr_t>(window.begin) != 5 ||
            reinterpret_cast<uintptr_t>(window.begin) < reinterpret_cast<uintptr_t>(edsl_ladd_section_begin) ||
            reinterpret_cast<uintptr_t>(window.end) >= reinterpret_cast<uintptr_t>(edsl_ladd_section_end))
            fail("linked descriptor/matrix mismatch", 2);
        const std::array<unsigned char, 5> required{
            0xf0, static_cast<unsigned char>(0x48 | ((source >> 3) << 2) | (ignored_x << 1) | (base >> 3)),
            0x0f, 0xc1, static_cast<unsigned char>(((source & 7) << 3) | (base & 7))};
        if (std::memcmp(window.begin, required.data(), 5)) fail("owned probe opcode mismatch", 2);
        for (unsigned vector = 0; vector < old_values.size(); ++vector) {
            for (unsigned r = 0; r < 16; ++r)
                edsl_ladd_input.registers[r] = 0xabcde00123456789 + UINT64_C(0x0102030405060708) * r + vector;
            edsl_ladd_input.registers[source] = deltas[vector];
            edsl_ladd_input.registers[base] = address; // aliases use the actual address as delta
            edsl_ladd_input.flags = flag_requests[vector % flag_requests.size()];
            memory = {UINT64_C(0xa55ac33c96696996), old_values[vector], UINT64_C(0x5aa53cc369969669)};
            if (source == base && vector == 1) memory[1] = UINT64_C(0) - address;
            const auto before_memory = memory;
            std::array<unsigned char, 5> before_code{}, after_code{};
            std::memcpy(before_code.data(), window.begin, 5);
            if (!edsl_ladd_checked_call(window.begin)) fail("System V GPR/stack restoration");
            std::memcpy(after_code.data(), window.begin, 5);
            const auto &before = edsl_ladd_before;
            const auto &after = edsl_ladd_after;
            // There is deliberately NO ADD-flags implementation here. Effective
            // CPU RFLAGS are the independent expected values for Lean replay.
            if (std::memcmp(before.registers, edsl_ladd_input.registers, sizeof before.registers) ||
                before.rip != reinterpret_cast<uintptr_t>(window.begin) ||
                after.rip != reinterpret_cast<uintptr_t>(window.end) ||
                (before.flags & ((UINT64_C(1) << 8) | (UINT64_C(1) << 14) |
                    (UINT64_C(1) << 16) | (UINT64_C(1) << 17) | (UINT64_C(1) << 18))) ||
                ((before.flags ^ after.flags) & ~arithmetic_flags) || before_code != after_code)
                fail("capture setup, continuation, flags frame or code frame");
            const uint64_t delta = before.registers[source];
            for (unsigned r = 0; r < 16; ++r)
                if (after.registers[r] != (r == source ? before_memory[1] : before.registers[r]))
                    fail("full old response or outside-source GPR frame");
            if (memory[1] != before_memory[1] + delta || memory[0] != before_memory[0] ||
                memory[2] != before_memory[2]) fail("unsigned modular qword sum or neighboring data frame");

            std::printf("%zu", count);
            field(source); field(base); field(ignored_x); field(vector);
            field(before.rip); field(after.rip);
            bytes(before_code); bytes(after_code);
            field(before.flags); field(after.flags);
            registers(before); registers(after);
            field(address);
            for (auto value : before_memory) field(value);
            for (auto value : memory) field(value);
            std::putchar('\n');
            ++count;
            aliases += source == base;
            rsp_sources += source == 4;
            x_variants += ignored_x != 0;
            high_responses += (after.registers[source] >> 32) != 0;
            status_set |= after.flags & arithmetic_flags;
            status_clear |= ~after.flags & arithmetic_flags;
        }
    }
    if (count != 3072 || aliases != 192 || rsp_sources != 192 || x_variants != 1536 ||
        !high_responses || status_set != arithmetic_flags || status_clear != arithmetic_flags)
        fail("matrix/defined-flag polarity coverage incomplete");
    if (sigprocmask(SIG_SETMASK, &previous, nullptr)) fail("cannot restore signal mask", 2);
    if (std::fflush(stdout)) fail("capture output error", 2);
    std::fprintf(stderr,
        "PASS native=%zu windows=384 sources=16 direct-bases=12 X=0/1 vectors=8 "
        "aliases=%zu rsp-source=%zu X1=%zu high-old-responses=%zu defined-flags-both=0x%" PRIx64 "\n"
        "All calls checked System V nonvolatile GPRs/SP. CPU flags are the replay oracle. "
        "Single-threaded finite evidence only; no physical TSO, source-order or universal proof claim.\n",
        count, aliases, rsp_sources, x_variants, high_responses, status_set);
    return 0;
}
