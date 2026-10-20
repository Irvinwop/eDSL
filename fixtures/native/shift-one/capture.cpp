// Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
// Only freshly built, controlled project-owned windows execute. The separate
// persisted-data checker uses arithmetic, never a decoder or program interpreter.
#include <array>
#include <cerrno>
#include <charconv>
#include <climits>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <iterator>
#include <sstream>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <vector>
#include <sys/syscall.h>
#include <unistd.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error "The shift-one capture requires Linux x86-64 SysV."
#endif

using Word = std::uint64_t;
static_assert(CHAR_BIT == 8 && sizeof(Word) == 8 && __cplusplus >= 202400L);
constexpr std::array<unsigned, 11> selected{0,1,2,3,4,5,8,9,12,13,15};
constexpr std::array<const char*, 11> regnames{
    "rax","rcx","rdx","rbx","rsp","rbp","r8","r9","r12","r13","r15"};
struct Snapshot {
    std::array<Word, 11> before, after;
    Word flags_before, flags_after;
};
static_assert(std::is_standard_layout_v<Snapshot> && sizeof(Snapshot) == 192 &&
              offsetof(Snapshot, after) == 88 && offsetof(Snapshot, flags_before) == 176 &&
              offsetof(Snapshot, flags_after) == 184);

#define P(name,dst,...) \
    extern "C" void shift_one_##name(const Word*, unsigned, Snapshot*); \
    extern "C" const unsigned char shift_one_##name##_instruction[], shift_one_##name##_instruction_end[];
#include "probes.def"
#undef P
struct Probe {
    const char* name;
    unsigned dst;
    void (*run)(const Word*, unsigned, Snapshot*);
    const unsigned char *start, *end;
    std::array<unsigned char, 3> literal;
};
const std::array<Probe, 40> probes{{
#define P(name,dst,...) \
    {#name,dst,shift_one_##name,shift_one_##name##_instruction,shift_one_##name##_instruction_end,{__VA_ARGS__}},
#include "probes.def"
#undef P
}};
struct Input { const char* name; Word value; };
constexpr Input inputs[]{
#define V(name,value) {#name,UINT64_C(value)},
#include "inputs.def"
#undef V
};
static_assert(std::size(inputs) == 32);
// Independently specified ADD flag contracts for the eight assembly seed pairs.
constexpr std::array<Word,8> seed_flags{0x44,0x55,0x894,0x845,0x10,0x4,0x0,0x84};
constexpr Word af_mask = 0x10, arithmetic_mask = 0x8d5;
constexpr Word highbit = UINT64_C(0x8000000000000000);
constexpr std::size_t matrix_size = std::size(inputs) * probes.size() * seed_flags.size();

void require(bool condition, const std::string& message) {
    if (!condition) throw std::runtime_error(message);
}
std::string hex(Word word, unsigned width = 16) {
    std::ostringstream text;
    text << std::hex << std::setw(static_cast<int>(width)) << std::setfill('0') << word;
    return text.str();
}
std::string code_hex(const std::array<unsigned char,3>& bytes) {
    std::string text;
    for (const auto byte : bytes) text += hex(byte,2);
    return text;
}
Word number(const std::string& text, unsigned width, int base) {
    Word value = 0;
    const auto parsed = std::from_chars(text.data(),text.data()+text.size(),value,base);
    require((width == 0 || text.size() == width) && !text.empty() &&
            parsed.ec == std::errc{} && parsed.ptr == text.data()+text.size(),"malformed number");
    require((base == 16 ? hex(value,width) : std::to_string(value)) == text,"noncanonical number");
    return value;
}
std::vector<std::string> fields(const std::string& line) {
    std::vector<std::string> result;
    std::size_t start = 0;
    for (;;) {
        const auto end = line.find('\t',start);
        result.push_back(line.substr(start,end == std::string::npos ? end : end-start));
        if (end == std::string::npos) return result;
        start = end+1;
    }
}
std::string header() {
    std::string text = "case_id\tprobe\tseed\tinstruction_hex\trflags_before\trflags_after";
    for (const auto name : regnames) text += std::string("\tbefore_")+name;
    for (const auto name : regnames) text += std::string("\tafter_")+name;
    return text;
}
std::array<Word,10> input_vector(std::size_t case_id) {
    std::array<Word,10> result{};
    for (std::size_t i=0;i<result.size();++i) result[i]=inputs[(case_id+i)%std::size(inputs)].value;
    return result;
}
Word reg(const std::array<Word,11>& values, unsigned r) {
    for (std::size_t i=0;i<selected.size();++i) if (selected[i]==r) return values[i];
    throw std::runtime_error("probe requires unobserved register");
}
// Independent arithmetic specification: unsigned wide floor division, not SHR,
// a copied machine interpreter, a hardware-derived expected value or Lean code.
Word expected_result(Word input) {
    return static_cast<Word>(static_cast<__uint128_t>(input) / __uint128_t{2});
}
Word expected_defined_flags(const Snapshot& snapshot, Word input, Word output) {
    unsigned bits = 0;
    for (Word low=output%256;low!=0;low/=2) bits+=static_cast<unsigned>(low%2);
    const Word status = Word(input%2 != 0) + Word(bits%2 == 0)*4 +
        Word(output == 0)*64 + Word(output >= highbit)*128 + Word(input >= highbit)*2048;
    // AF is undefined. This word is only meaningful with AF masked; no physical
    // AF value is selected, predicted, or equated with both later model choices.
    return (snapshot.flags_before & ~arithmetic_mask) | status;
}
void check_observation(const Probe& probe, std::size_t c, unsigned seed, const Snapshot& snapshot) {
    const auto requested = input_vector(c);
    for (std::size_t i=0;i<selected.size();++i) {
        if (selected[i]==4) continue; // Live RSP is observed, not installed.
        require(snapshot.before[i]==requested[i<4 ? i : i-1],"controlled input mismatch");
    }
    require(snapshot.before[4]!=0 && snapshot.before[4]%8==0,"invalid live RSP capture");
    require((snapshot.flags_before & arithmetic_mask)==seed_flags[seed],"flag seed mismatch");
    require((snapshot.flags_before & 0x40500)==0 && (snapshot.flags_before & 2)==2,
            "target requires AC/DF/TF off and RFLAGS reserved bit1");
    require(((snapshot.flags_before | snapshot.flags_after) & 0x30000)==0,
            "PUSHFQ RF/VM masking mismatch");
    const Word input = reg(snapshot.before,probe.dst), result = expected_result(input);
    require(reg(snapshot.after,probe.dst)==result,"independent unsigned division result mismatch");
    for (std::size_t i=0;i<selected.size();++i)
        if (selected[i]!=probe.dst)
            require(snapshot.before[i]==snapshot.after[i],"observed nondestination GPR changed");
    require((snapshot.flags_after & ~af_mask)==(expected_defined_flags(snapshot,input,result) & ~af_mask),
            "independent defined/preserved flags mismatch (AF masked)");
}
void write_file(const std::string& path, const std::string& text) {
    std::ofstream file(path,std::ios::binary);
    require(bool(file),"cannot open output: "+path);
    file << text;
    file.close();
    require(bool(file),"cannot close output: "+path);
}
std::vector<std::string> live_codes(const std::string& dir) {
    // Preflight ALL linked windows before executing ANY of them.
    std::vector<std::string> result;
    for (const auto& probe : probes) {
        const auto start=reinterpret_cast<std::uintptr_t>(probe.start);
        const auto end=reinterpret_cast<std::uintptr_t>(probe.end);
        require(end>start && end-start==probe.literal.size(),"invalid live opcode labels");
        std::array<unsigned char,3> live{};
        for (std::size_t i=0;i<live.size();++i) live[i]=probe.start[i];
        require(live==probe.literal,"live linked bytes differ from independent literal window: "+std::string(probe.name));
        result.push_back(code_hex(live));
    }
    std::string manifest="probe\tdestination\tinstruction_hex\n";
    for (std::size_t i=0;i<probes.size();++i) {
        const auto& probe=probes[i];
        write_file(dir+"/opcodes/"+probe.name+".bin",
                   std::string(reinterpret_cast<const char*>(probe.start),probe.literal.size()));
        manifest+=std::string(probe.name)+"\t"+std::to_string(probe.dst)+"\t"+result[i]+"\n";
    }
    write_file(dir+"/probes.tsv",manifest);
    std::string values="case_id\tvalue\n";
    for (const auto& input : inputs) values+=std::string(input.name)+"\t"+hex(input.value)+"\n";
    write_file(dir+"/inputs.tsv",values);
    std::string seeds="seed\tarithmetic_flags\n";
    for (std::size_t i=0;i<seed_flags.size();++i) seeds+=std::to_string(i)+"\t"+hex(seed_flags[i])+"\n";
    write_file(dir+"/seeds.tsv",seeds);
    return result;
}
void capture(const std::string& dir) {
    Word entry=0;
    asm volatile("pushfq; popq %0" : "=r"(entry) : : "memory");
    require((entry & 0x40500)==0,"target precondition AC/DF/TF must already be clear");
    Word shadow_stack=0;
    errno=0;
    const long status=syscall(SYS_arch_prctl,0x5005,&shadow_stack); // ARCH_SHSTK_STATUS
    const int saved_errno=errno;
    require(status==0 ? shadow_stack==0 : saved_errno==EINVAL || saved_errno==ENOSYS,
            "shadow stack enabled/status unavailable");
    std::cerr << "TARGET: ARCH_SHSTK_STATUS=" << status << " errno=" << saved_errno
        << " features=" << shadow_stack << "; IBT-off/stable ordinary RAM/debug/asynchronous "
        "boundaries remain assumptions; PUSHFQ masks RF/VM.\n";
    const auto codes=live_codes(dir);
    std::cout << header() << '\n';
    std::size_t rows=0;
    for (std::size_t c=0;c<std::size(inputs);++c) {
        const auto values=input_vector(c);
        for (std::size_t n=0;n<probes.size();++n) for (unsigned seed=0;seed<seed_flags.size();++seed) {
            struct Guarded { Word left; Snapshot snapshot; Word right; }
                storage{UINT64_C(0x6b13fd04a9c287e5),{},UINT64_C(0xe94a0623bc578d1f)};
            storage.snapshot.before.fill(UINT64_C(0xb83d5e106c92a7f4));
            storage.snapshot.after.fill(UINT64_C(0x469c8b23e751fd0a));
            storage.snapshot.flags_before=storage.snapshot.flags_after=UINT64_MAX;
            probes[n].run(values.data(),seed,&storage.snapshot);
            require(storage.left==UINT64_C(0x6b13fd04a9c287e5) && storage.right==UINT64_C(0xe94a0623bc578d1f),
                    "capture buffer canary corrupted");
            const auto& snapshot=storage.snapshot;
            // Persist RAW observations before any arithmetic contract checking.
            std::cout << inputs[c].name << '\t' << probes[n].name << '\t' << seed << '\t' << codes[n]
                << '\t' << hex(snapshot.flags_before) << '\t' << hex(snapshot.flags_after);
            for (const Word word : snapshot.before) std::cout << '\t' << hex(word);
            for (const Word word : snapshot.after) std::cout << '\t' << hex(word);
            std::cout << '\n';
            ++rows;
        }
    }
    std::cout.flush();
    require(bool(std::cout),"capture stdout write failure");
    std::cerr << "CAPTURED " << rows << " raw observations (__cplusplus=" << __cplusplus
        << "); physical AF retained, no mathematical check in capture, no Lean replay or physical refinement.\n";
}
void check(const char* path, const std::string& opcode_dir) {
    std::ifstream file(path);
    require(bool(file),"cannot open capture");
    std::string line;
    require(bool(std::getline(file,line)) && line==header(),"capture header/schema mismatch");
    std::vector<bool> seen(matrix_size,false);
    std::size_t count=0;
    constexpr std::array<Word,5> flag_bits{1,4,64,128,2048};
    constexpr std::array<const char*,5> flag_names{"CF","PF","ZF","SF","OF"};
    std::array<std::array<std::size_t,2>,5> flag_counts{};
    std::array<std::size_t,2> af_counts{};
    for (const auto& probe : probes) {
        std::ifstream opcode(opcode_dir+"/"+probe.name+".bin",std::ios::binary);
        require(bool(opcode),"missing opcode file");
        const std::vector<unsigned char> bytes((std::istreambuf_iterator<char>(opcode)),{});
        require(!opcode.bad() && bytes==std::vector<unsigned char>(probe.literal.begin(),probe.literal.end()),
                "opcode file mismatch");
    }
    while (std::getline(file,line)) {
        const auto parsed=fields(line);
        require(parsed.size()==28,"malformed capture field count");
        std::size_t c=0,n=0;
        while (c<std::size(inputs) && parsed[0]!=inputs[c].name) ++c;
        while (n<probes.size() && parsed[1]!=probes[n].name) ++n;
        require(c<std::size(inputs) && n<probes.size(),"unknown input/probe");
        const auto seed=number(parsed[2],0,10);
        require(seed<seed_flags.size(),"invalid seed");
        const auto key=(c*probes.size()+n)*seed_flags.size()+seed;
        require(!seen[key],"duplicate observation");
        seen[key]=true;
        require(parsed[3]==code_hex(probes[n].literal),"captured opcode mismatch");
        Snapshot snapshot{};
        snapshot.flags_before=number(parsed[4],16,16);
        snapshot.flags_after=number(parsed[5],16,16);
        for (std::size_t j=0;j<selected.size();++j) {
            snapshot.before[j]=number(parsed[6+j],16,16);
            snapshot.after[j]=number(parsed[17+j],16,16);
        }
        try { check_observation(probes[n],c,static_cast<unsigned>(seed),snapshot); }
        catch (const std::exception& error) {
            throw std::runtime_error(parsed[0]+"/"+parsed[1]+"/"+parsed[2]+": "+error.what());
        }
        for (std::size_t i=0;i<flag_bits.size();++i)
            ++flag_counts[i][(snapshot.flags_after & flag_bits[i])!=0 ? 1 : 0];
        ++af_counts[(snapshot.flags_after & af_mask)!=0 ? 1 : 0];
        ++count;
    }
    require(!file.bad() && count==seen.size(),"incomplete matrix");
    std::cout << "PASS: " << count << " persisted SHR64-by-one observations; 40 exact windows x 32 "
        "rotated vectors x 8 dirty seeds; independent unsigned wide division, CF/OF/SF/ZF/PF, "
        "all saved nonarithmetic bits and 11 actual GPR frames (AF masked).\n";
    for (std::size_t i=0;i<flag_bits.size();++i)
        std::cout << flag_names[i] << "=0:" << flag_counts[i][0] << " =1:" << flag_counts[i][1] << '\n';
    std::cout << "AF raw =0:" << af_counts[0] << " =1:" << af_counts[1]
        << "; informational only, neither value required.\n";
}
int main(int argc,char** argv) {
    try {
        if (argc==3 && std::string(argv[1])=="capture") capture(argv[2]);
        else if (argc==4 && std::string(argv[1])=="check") check(argv[2],argv[3]);
        else throw std::runtime_error("usage: capture.elf capture OUTPUT | check CAPTURE.tsv OPCODE_DIR");
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "REJECT: " << error.what() << '\n';
        return 1;
    }
}
