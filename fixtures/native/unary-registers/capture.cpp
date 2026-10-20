#include <array>
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <system_error>
#include <vector>

struct Snapshot {
    std::array<std::uint64_t, 4> before;
    std::array<std::uint64_t, 4> after;
    std::uint64_t flags_before;
    std::uint64_t flags_after;
};
static_assert(sizeof(Snapshot) == 80);
static_assert(offsetof(Snapshot, after) == 32);
static_assert(offsetof(Snapshot, flags_before) == 64);
static_assert(offsetof(Snapshot, flags_after) == 72);

#define DECLARE(name) \
    extern "C" void name(std::uint64_t, unsigned int, Snapshot*); \
    extern "C" const unsigned char name##_instruction[]; \
    extern "C" const unsigned char name##_instruction_end[]
DECLARE(fixture_neg32_eax);
DECLARE(fixture_neg32_ecx);
DECLARE(fixture_neg32_r8d);
DECLARE(fixture_neg32_r9d);
DECLARE(fixture_bswap64_rax);
DECLARE(fixture_bswap64_rcx);
DECLARE(fixture_bswap64_r8);
DECLARE(fixture_bswap64_r9);
#undef DECLARE

struct Fixture {
    const char* operation;
    const char* reg;
    void (*run)(std::uint64_t, unsigned int, Snapshot*);
    const unsigned char* instruction;
    const unsigned char* end;
};

#define ENTRY(op, reg, name) \
    Fixture{op, reg, name, name##_instruction, name##_instruction_end}
const std::array<Fixture, 8> fixtures{{
    ENTRY("neg32", "eax", fixture_neg32_eax),
    ENTRY("neg32", "ecx", fixture_neg32_ecx),
    ENTRY("neg32", "r8d", fixture_neg32_r8d),
    ENTRY("neg32", "r9d", fixture_neg32_r9d),
    ENTRY("bswap64", "rax", fixture_bswap64_rax),
    ENTRY("bswap64", "rcx", fixture_bswap64_rcx),
    ENTRY("bswap64", "r8", fixture_bswap64_r8),
    ENTRY("bswap64", "r9", fixture_bswap64_r9),
}};
#undef ENTRY

struct Input {
    std::string operation;
    std::string name;
    std::uint64_t value;
};

std::uint64_t read_hex(const std::string& text) {
    std::uint64_t value = 0;
    const auto parsed = std::from_chars(text.data(), text.data() + text.size(), value, 16);
    if (text.size() != 16 || parsed.ec != std::errc{} ||
        parsed.ptr != text.data() + text.size()) {
        throw std::runtime_error("input must contain exactly sixteen hex digits");
    }
    return value;
}

std::vector<Input> read_inputs(const char* path) {
    std::ifstream file(path);
    if (!file) throw std::runtime_error("cannot open owned input list");
    std::vector<Input> inputs;
    for (std::string line; std::getline(file, line);) {
        if (line.empty() || line.front() == '#') continue;
        std::istringstream fields(line);
        std::string op, name, value, extra;
        if (!(fields >> op >> name >> value) || (fields >> extra) ||
            (op != "neg32" && op != "bswap64")) {
            throw std::runtime_error("invalid owned input row");
        }
        inputs.push_back({op, name, read_hex(value)});
    }
    if (file.bad() || inputs.empty()) throw std::runtime_error("input read failed or empty");
    return inputs;
}

std::string instruction_hex(const Fixture& fixture, const char* directory) {
    const auto start = reinterpret_cast<std::uintptr_t>(fixture.instruction);
    const auto end = reinterpret_cast<std::uintptr_t>(fixture.end);
    if (end <= start || end - start > 15) throw std::runtime_error("invalid instruction span");
    const auto length = static_cast<std::size_t>(end - start);
    const std::string path = std::string(directory) + "/" + fixture.operation + "-" + fixture.reg + ".bin";
    std::ofstream binary(path, std::ios::binary | std::ios::trunc);
    if (!binary) throw std::runtime_error("cannot open owned opcode output");
    binary.write(reinterpret_cast<const char*>(fixture.instruction), static_cast<std::streamsize>(length));
    binary.close();
    if (!binary) throw std::runtime_error("cannot write owned opcode output");
    constexpr char digits[] = "0123456789abcdef";
    std::string result;
    for (std::size_t i = 0; i < length; ++i) {
        const unsigned char byte = fixture.instruction[i];
        result += digits[byte >> 4];
        result += digits[byte & 15];
    }
    return result;
}

void emit_hex(std::uint64_t value) {
    std::cout << '\t' << std::hex << std::setw(16) << std::setfill('0') << value;
}

int main(int argc, char** argv) {
    try {
        if (argc != 3) throw std::runtime_error("usage: capture INPUTS.tsv EXISTING_OPCODE_DIRECTORY");
        std::uint64_t entry_flags = 0;
        asm volatile("pushfq; popq %0" : "=r"(entry_flags) : : "memory");
        if ((entry_flags & UINT64_C(0x0000000000040400)) != 0) {
            throw std::runtime_error("ABI precondition: DF and AC must already be clear");
        }
        const auto inputs = read_inputs(argv[1]);
        std::array<std::string, 8> codes;
        for (std::size_t i = 0; i < fixtures.size(); ++i) {
            codes[i] = instruction_hex(fixtures[i], argv[2]);
        }
        std::cout << "case_id\toperation\tregister\tseed\tinstruction_hex\trequested_input"
                     "\tbefore_rax\tbefore_rcx\tbefore_r8\tbefore_r9"
                     "\tafter_rax\tafter_rcx\tafter_r8\tafter_r9\trflags_before\trflags_after\tclassification\n";
        std::size_t count = 0;
        for (const auto& input : inputs) {
            for (std::size_t i = 0; i < fixtures.size(); ++i) {
                const auto& fixture = fixtures[i];
                if (input.operation != fixture.operation) continue;
                for (unsigned int seed = 0; seed < 8; ++seed) {
                    struct Guarded {
                        std::uint64_t left;
                        Snapshot observed;
                        std::uint64_t right;
                    } storage{UINT64_C(0x6b13fd04a9c287e5), {}, UINT64_C(0xe94a0623bc578d1f)};
                    fixture.run(input.value, seed, &storage.observed);
                    if (storage.left != UINT64_C(0x6b13fd04a9c287e5) ||
                        storage.right != UINT64_C(0xe94a0623bc578d1f)) {
                        throw std::runtime_error("snapshot buffer guard changed");
                    }
                    const auto& state = storage.observed;
                    std::cout << input.name << '\t' << fixture.operation << '\t' << fixture.reg
                              << '\t' << std::dec << seed << '\t' << codes[i];
                    emit_hex(input.value);
                    for (const auto value : state.before) emit_hex(value);
                    for (const auto value : state.after) emit_hex(value);
                    emit_hex(state.flags_before);
                    emit_hex(state.flags_after);
                    std::cout << "\tLITERAL\n";
                    ++count;
                }
            }
        }
        std::cout.flush();
        if (!std::cout) throw std::runtime_error("capture stdout write failed");
        std::cerr << "DATA: " << count << " native observations; __cplusplus=" << __cplusplus
                  << "; no Lean replay, universal proof, or physical refinement.\n";
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "capture failed: " << error.what() << '\n';
        return 1;
    }
}
