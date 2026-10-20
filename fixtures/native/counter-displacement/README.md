# Owned finite counter/displacement conformance

Run `bash scripts/verify-counter-displacement.sh --native-only` for a controlled
Linux x86-64 SysV capture and independent persisted-observation comparison.
`bash scripts/verify-counter-displacement.sh --replay RUN_DIRECTORY` reuses a
sealed native run without rerunning its windows. With no arguments the script
captures and replays. Production replay first builds the current production
closure, then pins and copies its sources and providers. No preexisting local readiness file is needed.
Native-only is independently useful and does not claim Lean model admission.
No outer flock: every individual Lean/Lake call takes the shared lock itself.

The exact finite scope is 72 literal windows, twelve rotated full64 input
vectors and four incoming flag seeds: 1920 ADD32-imm8, 384 INC32, 1152 LEA64,
3456 observations total. ADD/INC destinations are RAX/RCX/R8/R9/R12/R13. RAX/RCX
have both no prefix and 40; high registers use 41. ADD immediates are 80, ff, 00,
01, 7f. The twelve inputs include dirty upper32, nibble/byte parity boundaries,
signed min/max, unsigned wrap and negative128. Every destination sees every
input; rotating inputs keeps unrelated sources asymmetric.

Twelve plain and twelve SIB mod01 LEAs cover all REX.W48..4f values, signed
displacements80/ff/00/7f, encoded scales0..3, RBP/R13 mod01 bases, no-index SIB
at all scales, R12 index with X=1, high banks, destination=base, destination=index,
base=index and three-way aliases. Modular and noncanonical outputs are allowed;
the windows never read DATA. Live RSP is a captured source in one SIB window.
RSP is never a tested destination. Other encodings/GPR combinations, including
RSP destination cases, belong to independent generic model tests; this matrix
is not exhaustive ISA coverage.

Assembly saves/restores its callee-saved GPRs and uses only normal stack scratch.
Ten controlled GPRs plus live RSP have actual before/after values:
RAX,RCX,RDX,RBX,RSP,RBP,R8,R9,R12,R13,R15. MOV and balanced PUSHFQ/POP-to-GPR
preserve flags around the exact labeled windows. ADD outside the window seeds
arithmetic flags44/55/894/845, covering incoming CF both ways. No arbitrary
POPFQ installation occurs. The C++ capture writes raw observations and copies
live linked instruction-label bytes; its separate `check` mode reads the saved
TSV. Results use wide integer modular arithmetic; flags use unsigned carry,
signed overflow, low-nibble carry and low-byte bit parity, never a tested window,
production model/flag function or copied decoder. CF preservation is mandatory
for INC even at ffffffff; every saved LEA flag and all nonarithmetic saved bits
are compared. Both input and opcode literal tables are independent contracts,
not hardware-derived expected outputs.

`tests/native/RegisterCapture.lean` supplies shared capture/state parsing and
full production-step mechanics; it imports unchanged public UnaryReplay
register-canary/memory providers and universal fullRAMFrame/fullRAMAt theorems.
`CounterDisplacementReplay.lean` gives one family-level metadata adapter and
independent mathematical checker for every future program using these families.
Production `decodeAt` must yield the declared public constructor and exact length.
Production `step` runs for both AF choices, compares all flags, all sixteen modeled
GPRs, exact relocated RIP and no operand reads, and challenges memory/value/execute/
write maps. The five unobserved GPRs use distinct synthetic model canaries. RAM
maps, including code/sentinels/canonical-boundary holes, are independent model
frames. The universal theorem preserves the entire three maps at every address
under the checked decode/new/no-store/success conditions. Neither canaries nor
model maps are physical observations or observed OS resource authority.

The generator rejects duplicate, missing and malformed captures and corrupt
results/flags before emitting proofs. Twenty-seven direct corruption controls
bypass these guards and challenge the actual full-step projection: dirty upper32,
nondestination GPRs, CF/AF/OF/high flags, incoming INC CF, aliased LEA prestate and
no-index/R12 distinction. A completed replay requires an ordinary `decide +kernel`
theorem for each of 3456 observations; modules contain sixteen finite rows each. Standard
kernel budgets, warnings as errors and Lean4.35.0 apply; no holes/project axioms,
native_decide, unchecked solver, linter suppression or resource increases.
An imported dependency audit permits only propext, Quot.sound and Classical.choice.

PUSHFQ saves RF/VM as zero, so this cannot observe their hidden physical values.
AC/DF/TF must already be off. Debug, asynchronous/exception-priority state,
ordinary RAM, long mode, the production four-level canonical-address profile,
CET/IBT and shadow stacks disabled remain target assumptions. The capture probes
ARCH_SHSTK_STATUS and records success/features or unsupported EINVAL/ENOSYS;
unsupported status does not discharge the CET assumptions. Compiler flags exclude
CET instrumentation; ELF notes and target/tool information are recorded. No
universal physical CPU/OS refinement, ABI/resource/concurrency or source/backend
preservation theorem follows from finite native agreement.

Raw observations, snapshots, ELF/disassembly, opcode files, exact commands,
environments, stdout/stderr/exits and source/provider/opcode before/after pins
stay in ignored `.cache/popcount/native/run.*`. Each closed run has a SHA256
receipt manifest and seal. `NATIVE-READY` means only native capture/mathematical
comparison; `READY` additionally requires current production replay and audit.
Failures remain failures, not security findings. Required tools are recorded;
the runner uses standard Bash/awk/sed/grep/coreutils/binutils, C++ and Lean tools,
with no rg runtime dependency. No broad gates, registration or publication are
performed; integrated/current fresh gates remain root-owned.
The local `.cache/popcount/native/HANDOFF.md` states which phases actually ran;
source implementation alone does not establish a compiled/replayed Lean API.
