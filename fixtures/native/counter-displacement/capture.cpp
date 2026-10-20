// Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
// Only controlled project-owned windows execute. The separate mathematical
// checker never invokes a window or production Lean decoder/flag routine.
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
#include <vector>
#include <cerrno>
#include <sys/syscall.h>
#include <unistd.h>

using Word = std::uint64_t;
constexpr std::array<unsigned, 11> selected{0,1,2,3,4,5,8,9,12,13,15};
constexpr std::array<const char*, 11> regnames{
    "rax","rcx","rdx","rbx","rsp","rbp","r8","r9","r12","r13","r15"};
struct Snapshot {
    std::array<Word, 11> before, after;
    Word flags_before, flags_after;
};
static_assert(sizeof(Snapshot) == 192 && offsetof(Snapshot, after) == 88 &&
              offsetof(Snapshot, flags_before) == 176 && offsetof(Snapshot, flags_after) == 184);
#define P(name,kind,dst,base,index,scale,imm,pref,...) \
    extern "C" void counter_##name(const Word*, unsigned, Snapshot*); \
    extern "C" const unsigned char counter_##name##_instruction[], counter_##name##_instruction_end[];
#include "probes.def"
#undef P
struct Probe {
    const char* name;
    unsigned kind, dst, base, index, scale, imm, pref;
    void (*run)(const Word*, unsigned, Snapshot*);
    const unsigned char *start, *end;
    std::vector<unsigned char> literal;
};
const std::vector<Probe> probes{
#define P(name,kind,dst,base,index,scale,imm,pref,...) \
    {#name,kind,dst,base,index,scale,imm,pref,counter_##name, \
     counter_##name##_instruction,counter_##name##_instruction_end,{__VA_ARGS__}},
#include "probes.def"
#undef P
};
struct Input { const char* name; Word value; };
constexpr Input inputs[]{
#define V(name,value) {#name,UINT64_C(value)},
#include "inputs.def"
#undef V
};
constexpr std::array<Word,4> seed_flags{0x44,0x55,0x894,0x845};
constexpr Word arithmetic_mask = 0x8d5;

void require(bool b, const std::string& message) {
    if (!b) throw std::runtime_error(message);
}
std::string hex(Word w, unsigned width = 16) {
    std::ostringstream s;
    s << std::hex << std::setw(static_cast<int>(width)) << std::setfill('0') << w;
    return s.str();
}
std::string code_hex(const std::vector<unsigned char>& code) {
    std::string s;
    for (const auto b : code) s += hex(b,2);
    return s;
}
Word number(const std::string& s, unsigned width, int base) {
    Word n = 0;
    const auto parsed = std::from_chars(s.data(),s.data()+s.size(),n,base);
    require((width == 0 || s.size() == width) && !s.empty() &&
            parsed.ec == std::errc{} && parsed.ptr == s.data()+s.size(),"malformed number");
    require((base == 16 ? hex(n,width) : std::to_string(n)) == s,"noncanonical number");
    return n;
}
std::vector<std::string> fields(const std::string& line) {
    std::vector<std::string> f;
    std::size_t start = 0;
    for (;;) {
        const auto end = line.find('\t',start);
        f.push_back(line.substr(start,end == std::string::npos ? end : end-start));
        if (end == std::string::npos) return f;
        start = end+1;
    }
}
std::string header() {
    std::string s = "case_id\tprobe\tseed\tinstruction_hex\trflags_before\trflags_after";
    for (const auto name : regnames) s += std::string("\tbefore_")+name;
    for (const auto name : regnames) s += std::string("\tafter_")+name;
    return s;
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
// Independent mathematical contract: no model evaluator or opcode decoding.
Word expected_result(const Probe& p, const Snapshot& s) {
    const std::int64_t immediate = p.imm < 128 ? p.imm : static_cast<std::int64_t>(p.imm)-256;
    if (p.kind == 2) {
        const __int128_t sum = static_cast<__int128_t>(reg(s.before,p.base)) + immediate +
            (p.index == 16 ? 0 : static_cast<__int128_t>(reg(s.before,p.index)) * (Word{1} << p.scale));
        return static_cast<Word>(sum); // modulo 2^64, including negative/noncanonical values
    }
    const Word x = reg(s.before,p.dst) % (Word{1}<<32);
    const std::int64_t sum = static_cast<std::int64_t>(x) + (p.kind==1 ? 1 : immediate);
    return static_cast<Word>(sum) % (Word{1}<<32); // upper32 must be zero
}
Word expected_flags(const Probe& p, const Snapshot& s, Word output) {
    if (p.kind == 2) return s.flags_before;
    constexpr Word modulus = Word{1}<<32;
    const Word x = reg(s.before,p.dst) % modulus;
    const std::int64_t signed_x = x < (Word{1}<<31) ? static_cast<std::int64_t>(x) :
        static_cast<std::int64_t>(x)-static_cast<std::int64_t>(modulus);
    const std::int64_t immediate = p.kind==1 ? 1 :
        (p.imm < 128 ? p.imm : static_cast<std::int64_t>(p.imm)-256);
    const Word y = static_cast<Word>(immediate) % modulus;
    const bool cf = p.kind==1 ? (s.flags_before % 2 != 0) : x+y >= modulus;
    const std::int64_t signed_sum = signed_x+immediate;
    const bool of = signed_sum < -INT64_C(2147483648) || signed_sum > INT64_C(2147483647);
    unsigned bits = 0;
    for (Word low=output%256;low!=0;low/=2) bits+=static_cast<unsigned>(low%2);
    const Word status = Word(cf) + Word(bits%2==0)*4 + Word(x%16+y%16>=16)*16 +
        Word(output==0)*64 + Word(output>=(Word{1}<<31))*128 + Word(of)*2048;
    return (s.flags_before & ~arithmetic_mask) | status;
}
void check_observation(const Probe& p, std::size_t c, unsigned seed, const Snapshot& s) {
    const auto requested = input_vector(c);
    for (std::size_t i=0;i<selected.size();++i) {
        if (i==4) continue; // real live RSP is observed, not installed from a table
        require(s.before[i]==requested[i<4 ? i : i-1],"controlled input mismatch");
    }
    require(s.before[4]!=0 && s.before[4]%8==0,"invalid live RSP capture");
    require((s.flags_before & arithmetic_mask)==seed_flags[seed],"flag seed mismatch");
    require((s.flags_before & 0x40500)==0 && (s.flags_before & 2)==2,
            "target requires AC/DF/TF off and RFLAGS reserved bit1");
    require(((s.flags_before | s.flags_after) & 0x30000)==0,"PUSHFQ RF/VM masking mismatch");
    const Word result = expected_result(p,s);
    require(reg(s.after,p.dst)==result,"independent mathematical result mismatch");
    for (std::size_t i=0;i<selected.size();++i)
        if (selected[i]!=p.dst) require(s.before[i]==s.after[i],"observed nondestination GPR changed");
    require(s.flags_after==expected_flags(p,s,result),"independent mathematical flags mismatch");
}
void write_file(const std::string& path, const std::string& text) {
    std::ofstream file(path,std::ios::binary);
    require(bool(file),"cannot open output: "+path);
    file << text;
    file.close();
    require(bool(file),"cannot close output: "+path);
}
std::vector<std::string> live_codes(const std::string& dir) {
    std::vector<std::string> result;
    std::string manifest = "probe\tkind\tdestination\tbase\tindex\tscale\timm8\tprefixed\tinstruction_hex\n";
    for (const auto& p : probes) {
        const auto start=reinterpret_cast<std::uintptr_t>(p.start), end=reinterpret_cast<std::uintptr_t>(p.end);
        require(end>start && end-start<=15,"invalid live opcode labels");
        const std::vector<unsigned char> live(p.start,p.start+(end-start));
        require(live==p.literal,"live linked bytes differ from independent literal window");
        write_file(dir+"/opcodes/"+p.name+".bin",std::string(live.begin(),live.end()));
        result.push_back(code_hex(live));
        manifest += std::string(p.name)+"\t"+std::to_string(p.kind)+"\t"+std::to_string(p.dst)+"\t"+
            std::to_string(p.base)+"\t"+std::to_string(p.index)+"\t"+std::to_string(p.scale)+"\t"+
            std::to_string(p.imm)+"\t"+std::to_string(p.pref)+"\t"+code_hex(p.literal)+"\n";
    }
    write_file(dir+"/probes.tsv",manifest);
    std::string in;
    for (const auto& i : inputs) in+=std::string(i.name)+"\t"+hex(i.value)+"\n";
    write_file(dir+"/inputs.tsv",in);
    return result;
}
void capture(const std::string& dir) {
    Word entry=0;
    asm volatile("pushfq; popq %0" : "=r"(entry) : : "memory");
    require((entry & 0x40500)==0,"target precondition AC/DF/TF must already be clear");
    Word shstk=0;
    errno=0;
    const long status=syscall(SYS_arch_prctl,0x5005,&shstk); // ARCH_SHSTK_STATUS
    require(status==0 ? shstk==0 : errno==EINVAL || errno==ENOSYS,"shadow stack enabled/status unavailable");
    std::cerr << "TARGET: ARCH_SHSTK_STATUS=" << status << " errno=" << errno << " features=" << shstk
        << "; IBT-off/ordinary-RAM/debug/asynchronous boundaries remain target assumptions; PUSHFQ masks RF/VM.\n";
    const auto codes=live_codes(dir);
    std::cout << header() << '\n';
    std::size_t rows=0;
    for (std::size_t c=0;c<std::size(inputs);++c) {
        const auto values=input_vector(c);
        for (std::size_t n=0;n<probes.size();++n) for (unsigned seed=0;seed<4;++seed) {
            struct Guarded { Word left; Snapshot snapshot; Word right; }
                storage{0x6b13fd04a9c287e5,{},0xe94a0623bc578d1f};
            probes[n].run(values.data(),seed,&storage.snapshot);
            require(storage.left==UINT64_C(0x6b13fd04a9c287e5) && storage.right==UINT64_C(0xe94a0623bc578d1f),
                    "capture buffer canary corrupted");
            const auto& s=storage.snapshot;
            // Native capture does not depend on this check; observations are
            // independently checked again from the persisted raw TSV below.
            std::cout << inputs[c].name << '\t' << probes[n].name << '\t' << seed << '\t' << codes[n]
                << '\t' << hex(s.flags_before) << '\t' << hex(s.flags_after);
            for (const Word w : s.before) std::cout << '\t' << hex(w);
            for (const Word w : s.after) std::cout << '\t' << hex(w);
            std::cout << '\n';
            ++rows;
        }
    }
    std::cout.flush();
    require(bool(std::cout),"capture stdout write failure");
    std::cerr << "CAPTURED " << rows << " observations (__cplusplus=" << __cplusplus
        << "); no Lean replay or universal physical CPU/OS refinement.\n";
}
void check(const char* path, const std::string& dir) {
    std::ifstream file(path);
    require(bool(file),"cannot open capture");
    std::string line;
    require(bool(std::getline(file,line)) && line==header(),"capture header/schema mismatch");
    std::vector<bool> seen(std::size(inputs)*probes.size()*4,false);
    std::size_t count=0;
    for (const auto& p : probes) {
        std::ifstream opcode(dir+"/"+p.name+".bin",std::ios::binary);
        require(bool(opcode),"missing opcode file");
        const std::vector<unsigned char> bytes((std::istreambuf_iterator<char>(opcode)),{});
        require(bytes==p.literal,"opcode file mismatch");
    }
    while (std::getline(file,line)) {
        const auto f=fields(line);
        require(f.size()==28,"malformed capture field count");
        std::size_t c=0,n=0;
        while (c<std::size(inputs) && f[0]!=inputs[c].name) ++c;
        while (n<probes.size() && f[1]!=probes[n].name) ++n;
        require(c<std::size(inputs) && n<probes.size(),"unknown input/probe");
        const auto seed=number(f[2],0,10);
        require(seed<4,"invalid seed");
        const auto key=(c*probes.size()+n)*4+seed;
        require(!seen[key],"duplicate observation");
        seen[key]=true;
        require(f[3]==code_hex(probes[n].literal),"captured opcode mismatch");
        Snapshot s{};
        s.flags_before=number(f[4],16,16); s.flags_after=number(f[5],16,16);
        for (std::size_t j=0;j<11;++j) {
            s.before[j]=number(f[6+j],16,16); s.after[j]=number(f[17+j],16,16);
        }
        try { check_observation(probes[n],c,static_cast<unsigned>(seed),s); }
        catch (const std::exception& e) { throw std::runtime_error(f[0]+"/"+f[1]+"/"+f[2]+": "+e.what()); }
        ++count;
    }
    require(!file.bad() && count==seen.size(),"incomplete matrix");
    std::cout << "PASS: " << count << " persisted native observations; 1920 ADD32, 384 INC32, 1152 LEA64; "
        "independent wide arithmetic, signed overflow/carry/nibble/parity, all saved flags and selected GPR frames.\n";
}
int main(int argc,char** argv) {
    try {
        if (argc==3 && std::string(argv[1])=="capture") capture(argv[2]);
        else if (argc==4 && std::string(argv[1])=="check") check(argv[2],argv[3]);
        else throw std::runtime_error("usage: capture.elf capture OUTPUT | check CAPTURE.tsv OPCODE_DIR");
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "REJECT: " << e.what() << '\n';
        return 1;
    }
}
