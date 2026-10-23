// Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
// Only controlled project-owned windows execute. The separate mathematical
// checker never invokes a window or production Lean decoder/flag routine.
#include <array>
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
#include <cerrno>
#include <sys/syscall.h>
#include <unistd.h>

using Word = std::uint64_t;
enum Family : unsigned { Add32, Inc32, Lea64, Sub32, Cmp32, Lea32, TestLow8 };
enum AddressForm : unsigned { Base, Indexed, BaseDisp8, SibDisp8 };
constexpr std::array<unsigned, 11> selected{0,1,2,3,4,5,8,9,12,13,15};
constexpr std::array<const char*, 11> regnames{
    "rax","rcx","rdx","rbx","rsp","rbp","r8","r9","r12","r13","r15"};
struct Snapshot {
    std::array<Word, 11> before, after;
    Word flags_before, flags_after;
};
static_assert(sizeof(Snapshot) == 192 && offsetof(Snapshot, after) == 88 &&
              offsetof(Snapshot, flags_before) == 176 && offsetof(Snapshot, flags_after) == 184);
#define P(name,kind,dst,base,index,scale,imm,pref,form,...) \
    extern "C" void counter_##name(const Word*, unsigned, Snapshot*); \
    extern "C" const unsigned char counter_##name##_instruction[], counter_##name##_instruction_end[];
#include "probes.def"
#undef P
struct Probe {
    const char* name;
    unsigned kind, dst, base, index, scale, imm, pref, form;
    void (*run)(const Word*, unsigned, Snapshot*);
    const unsigned char *start, *end;
    std::vector<unsigned char> literal;
};
const std::vector<Probe> probes{
#define P(name,kind,dst,base,index,scale,imm,pref,form,...) \
    {#name,kind,dst,base,index,scale,imm,pref,form,counter_##name, \
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
bool observed(unsigned r) {
    for (const auto selected_register : selected) if (selected_register==r) return true;
    return false;
}
// Validate literal contracts before any file/observation emission. No byte is
// decoded here; metadata and linked bytes have separate authentication paths.
void validate_probes() {
    std::set<std::string> names;
    for (const auto& p : probes) {
        require(names.insert(p.name).second,"duplicate probe contract");
        require(p.kind<=TestLow8 && p.scale<4 && p.imm<256 && p.pref<2 && p.form<=SibDisp8,
                "unsupported probe contract");
        require(observed(p.dst) && (p.dst!=4 || p.kind==TestLow8),
                "unobserved operand or forbidden native RSP destination");
        require(!p.literal.empty() && p.literal.size()<=15,"invalid literal length");
        if (p.kind!=Lea64 && p.kind!=Lea32) {
            require(p.form==Base && p.base==0 && p.index==16 && p.scale==0,
                    "noncanonical unused address metadata");
            require(p.kind!=Inc32 || p.imm==1,"noncanonical INC immediate metadata");
            continue;
        }
        require(observed(p.base) && (p.index==16 || (observed(p.index) && p.index!=4)),
                "unobserved address operand or invalid RSP index");
        require(p.kind!=Lea64 || (p.pref==1 && p.form>=BaseDisp8),"unsupported LEA64 form");
        if (p.form==Base || p.form==BaseDisp8)
            require(p.index==16 && p.scale==0 && p.base!=4 && p.base!=12,"malformed plain address");
        if (p.form==Base || p.form==Indexed)
            require(p.imm==0 && p.base!=5 && p.base!=13,"malformed nondisplaced address");
        if (p.form==Indexed) require(p.index!=16,"indexed address requires an index");
    }
}
// Independent mathematical contract: no model evaluator or opcode decoding.
Word expected_result(const Probe& p, const Snapshot& s) {
    require(p.kind<=TestLow8,"unsupported probe family");
    const std::int64_t immediate = p.imm < 128 ? p.imm : static_cast<std::int64_t>(p.imm)-256;
    if (p.kind == Lea64 || p.kind == Lea32) {
        const __int128_t sum = static_cast<__int128_t>(reg(s.before,p.base)) +
            (p.form==BaseDisp8 || p.form==SibDisp8 ? immediate : 0) +
            (p.index == 16 ? 0 : static_cast<__int128_t>(reg(s.before,p.index)) * (Word{1} << p.scale));
        if (p.kind==Lea32) {
            const __int128_t modulus = Word{1}<<32;
            const __int128_t reduced = sum % modulus;
            return static_cast<Word>(reduced<0 ? reduced+modulus : reduced);
        }
        return static_cast<Word>(sum); // modulo 2^64, including negative/noncanonical values
    }
    if (p.kind==TestLow8) {
        const Word x = reg(s.before,p.dst)%256;
        Word intersection=0;
        for (Word power=1;power<256;power*=2)
            intersection+=power*((x/power)%2)*((p.imm/power)%2);
        return intersection; // only for flags; every full64 GPR is preserved
    }
    const Word x = reg(s.before,p.dst) % (Word{1}<<32);
    const std::int64_t delta = p.kind==Inc32 ? 1 :
        (p.kind==Sub32 || p.kind==Cmp32 ? -immediate : immediate);
    const std::int64_t sum = static_cast<std::int64_t>(x) + delta;
    // CMP uses this mathematical difference for flags only, never as a write.
    return static_cast<Word>(sum) % (Word{1}<<32); // upper32 must be zero
}
Word expected_flags(const Probe& p, const Snapshot& s, Word output) {
    if (p.kind == Lea64 || p.kind == Lea32) return s.flags_before;
    if (p.kind==TestLow8) {
        unsigned bits=0;
        for (Word low=output;low!=0;low/=2) bits+=static_cast<unsigned>(low%2);
        const Word status=Word(bits%2==0)*4+Word(output==0)*64+Word(output>=128)*128;
        // AF-normalized expectation. CF=OF=0; every nonarithmetic bit survives.
        return (s.flags_before & ~arithmetic_mask) | status;
    }
    constexpr Word modulus = Word{1}<<32;
    const Word x = reg(s.before,p.dst) % modulus;
    const std::int64_t signed_x = x < (Word{1}<<31) ? static_cast<std::int64_t>(x) :
        static_cast<std::int64_t>(x)-static_cast<std::int64_t>(modulus);
    const std::int64_t immediate = p.kind==Inc32 ? 1 :
        (p.imm < 128 ? p.imm : static_cast<std::int64_t>(p.imm)-256);
    const Word y = static_cast<Word>(immediate) % modulus;
    const bool subtract = p.kind==Sub32 || p.kind==Cmp32;
    // Borrow compares the unsigned width32 operands; it is not ADD(-imm)'s carry.
    const bool cf = p.kind==Inc32 ? (s.flags_before % 2 != 0) :
        (subtract ? x<y : x+y >= modulus);
    const bool auxiliary = subtract ? x%16<y%16 : x%16+y%16>=16;
    const std::int64_t signed_sum = subtract ? signed_x-immediate : signed_x+immediate;
    const bool of = signed_sum < -INT64_C(2147483648) || signed_sum > INT64_C(2147483647);
    unsigned bits = 0;
    for (Word low=output%256;low!=0;low/=2) bits+=static_cast<unsigned>(low%2);
    const Word status = Word(cf) + Word(bits%2==0)*4 + Word(auxiliary)*16 +
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
    if (p.kind==Cmp32 || p.kind==TestLow8)
        require(reg(s.after,p.dst)==reg(s.before,p.dst),
                p.kind==Cmp32 ? "observed CMP operand changed" : "observed TEST operand changed");
    else require(reg(s.after,p.dst)==result,"independent mathematical result mismatch");
    for (std::size_t i=0;i<selected.size();++i)
        if (selected[i]!=p.dst) require(s.before[i]==s.after[i],"observed nondestination GPR changed");
    const Word observed_flags=p.kind==TestLow8 ? s.flags_after & ~Word{0x10} : s.flags_after;
    require(observed_flags==expected_flags(p,s,result),"independent mathematical flags mismatch");
}
void write_file(const std::string& path, const std::string& text) {
    std::ofstream file(path,std::ios::binary);
    require(bool(file),"cannot open output: "+path);
    file << text;
    file.close();
    require(bool(file),"cannot close output: "+path);
}
std::string probe_manifest() {
    std::string manifest = "probe\tkind\tdestination\tbase\tindex\tscale\timm8\tprefixed\taddress_form\tinstruction_hex\n";
    for (const auto& p : probes) {
        manifest += std::string(p.name)+"\t"+std::to_string(p.kind)+"\t"+std::to_string(p.dst)+"\t"+
            std::to_string(p.base)+"\t"+std::to_string(p.index)+"\t"+std::to_string(p.scale)+"\t"+
            std::to_string(p.imm)+"\t"+std::to_string(p.pref)+"\t"+std::to_string(p.form)+"\t"+
            code_hex(p.literal)+"\n";
    }
    return manifest;
}
std::string input_manifest() {
    std::string in;
    for (const auto& i : inputs) in+=std::string(i.name)+"\t"+hex(i.value)+"\n";
    return in;
}
std::string read_file(const std::filesystem::path& path) {
    std::ifstream file(path,std::ios::binary);
    require(bool(file),"cannot open persisted manifest");
    const std::string text((std::istreambuf_iterator<char>(file)),{});
    require(!file.bad(),"persisted manifest read failure");
    return text;
}
std::vector<std::vector<unsigned char>> linked_codes() {
    std::vector<std::vector<unsigned char>> result;
    for (const auto& p : probes) {
        const auto start=reinterpret_cast<std::uintptr_t>(p.start), end=reinterpret_cast<std::uintptr_t>(p.end);
        require(end>start && end-start<=15,"invalid live opcode labels");
        const std::vector<unsigned char> live(p.start,p.start+(end-start));
        require(live==p.literal,"live linked bytes differ from independent literal window");
        result.push_back(live);
    }
    return result;
}
std::vector<std::string> live_codes(const std::string& dir) {
    // Authenticate ALL labeled windows before emitting any opcode/metadata.
    const auto live=linked_codes();
    std::vector<std::string> result;
    for (std::size_t n=0;n<probes.size();++n) {
        write_file(dir+"/opcodes/"+probes[n].name+".bin",std::string(live[n].begin(),live[n].end()));
        result.push_back(code_hex(live[n]));
    }
    write_file(dir+"/probes.tsv",probe_manifest());
    write_file(dir+"/inputs.tsv",input_manifest());
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
    auto opcode_path=std::filesystem::path(dir).lexically_normal();
    if (opcode_path.filename().empty()) opcode_path=opcode_path.parent_path();
    const auto parent=opcode_path.parent_path();
    require(read_file(parent/"probes.tsv")==probe_manifest(),"probe manifest mismatch");
    require(read_file(parent/"inputs.tsv")==input_manifest(),"input manifest mismatch");
    std::ifstream file(path);
    require(bool(file),"cannot open capture");
    std::string line;
    require(bool(std::getline(file,line)) && line==header(),"capture header/schema mismatch");
    std::vector<bool> seen(std::size(inputs)*probes.size()*4,false);
    std::size_t count=0;
    std::array<std::size_t,7> family_counts{};
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
        ++family_counts.at(probes[n].kind);
    }
    require(!file.bad() && count==seen.size(),"incomplete matrix");
    for (const bool present : seen) require(present,"missing required observation");
    constexpr std::array<const char*,7> families{"ADD32","INC32","LEA64","SUB32","CMP32","LEA32","TEST-low8"};
    std::cout << "PASS: " << count << " persisted native observations across " << probes.size()
        << " windows x " << std::size(inputs) << " rotated vectors x " << seed_flags.size() << " seeds;";
    for (std::size_t i=0;i<families.size();++i)
        std::cout << ' ' << family_counts[i] << ' ' << families[i] << ';';
    std::cout << " independent wide arithmetic, signed overflow/carry/borrow/nibble/parity, "
        "arithmetic byte intersection; all saved flags exact except TEST AF; selected GPR frames "
        "(CMP/TEST preserve full64).\n";
}
int main(int argc,char** argv) {
    try {
        validate_probes();
        if (argc==3 && std::string(argv[1])=="capture") capture(argv[2]);
        else if (argc==4 && std::string(argv[1])=="check") check(argv[2],argv[3]);
        else throw std::runtime_error("usage: capture.elf capture OUTPUT | check CAPTURE.tsv OPCODE_DIR");
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "REJECT: " << e.what() << '\n';
        return 1;
    }
}
