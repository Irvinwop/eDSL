# Owned finite counter/displacement conformance

Run `bash scripts/verify-counter-displacement.sh --native-only` for a controlled
Linux x86-64 SysV capture and independent persisted-observation comparison.
`bash scripts/verify-counter-displacement.sh --replay RUN_DIRECTORY` reuses a
sealed native run without rerunning its windows. With no arguments the script
captures and replays. Production replay first builds the current production
closure, then pins and copies its sources and providers. No preexisting local readiness file is needed.
Native-only is independently useful and does not claim Lean model admission.
No outer flock: every individual Lean/Lake call takes the shared lock itself.

The exact finite native scope is 136 literal windows, twelve rotated full64 input
vectors and four incoming flag seeds: 1920 ADD32-imm8, 384 INC32, 1152 LEA64,
1536 SUB32-imm8 and 1536 CMP32-imm8, 6528 observations total.
ADD/INC destinations are RAX/RCX/R8/R9/R12/R13. RAX/RCX
have both no prefix and 40; high registers use 41. ADD immediates are 80, ff, 00,
01, 7f. The twelve inputs include dirty upper32, nibble/byte parity boundaries,
signed min/max, unsigned wrap and negative128. Every destination sees every
input; rotating inputs keeps unrelated sources asymmetric.

Thirty-two SUB and thirty-two CMP windows bind literal 83 /5 and /7 bytes,
with immediates80/ff/00/7f (-128/-1/0/+127). RAX/RCX have unprefixed and
canonical40 forms; R8/R9/R12/R13 use canonical41. Unprefixed CMP EAX,0 retains
the production legacy cmpEaxZero constructor, so CMP EDX,0 replaces that single
matrix entry; prefixed CMP EAX,0 uses the new family. SUB must clear upper32 even
for immediate0, while CMP must preserve every full64 register. The same twelve
inputs expose unsigned borrow, low-nibble borrow, equality, parity and signed
overflow in both directions. For example, 0-(-128)=128 has CF=1 but no OF;
16-127 has AF=1, signed-min-127 has OF=1 and signed-max-(-1) has OF=1.
The table never writes live RSP, including when R12 exercises the matching
high-bank register code.

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
TSV. Results use wide integer modular arithmetic; flags use unsigned carry/borrow,
signed overflow, low-nibble carry/borrow and low-byte bit parity, never a tested window,
production model/flag function or copied decoder. CF preservation is mandatory
for INC even at ffffffff; subtraction CF compares the unsigned width32 operands
and differs from ADD(-imm)'s carry. Every saved LEA flag and all nonarithmetic saved bits
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

The runner rejects duplicate, missing and malformed captures and corrupt
results/flags before emitting proofs. Thirteen persisted-observation controls
include the original five plus real-bit changes to SUB/CMP upper32, CF, AF and OF;
full mode also requires the Lean generator to reject each one before emission.
The original twenty-seven direct production corruption controls
bypass these guards and challenge the actual full-step projection: dirty upper32,
nondestination GPRs, CF/AF/OF/high flags, incoming INC CF, aliased LEA prestate and
no-index/R12 distinction remain. Twelve additional direct production-step
controls challenge SUB/CMP upper32, nondestination registers and CF/AF/OF/high
flags, giving thirty-nine direct controls in total.
A completed replay requires an ordinary `decide +kernel`
theorem for each of 6528 observations; modules contain sixteen finite rows each. Standard
kernel budgets, warnings as errors and Lean4.35.0 apply; no holes/project axioms,
native_decide, unchecked solver, linter suppression or resource increases.
An imported dependency audit permits only propext, Quot.sound and Classical.choice.
The runner builds, pins, imports and audits Immediate32's universal context and
flag contracts alongside the actual finite production-step replay. Its Lean
calls explicitly retain warning errors, autoImplicit=false, maxHeartbeats300000
and maxRecDepth128.

The shared Lean adapter/generator in `tests/native/CounterDisplacementReplay.lean`
checks families0..4 with exact probe counts136/40/8/24/32/32 and row count6528.
Its independent Nat/Int result and flag contracts separate CMP's arithmetic
difference from its preserved full64 operand. The adapter still requires actual
production decode/step agreement; it does not supply an alternate executor.
The matrix substitutes CMP EDX,0 for the legacy unprefixed CMP EAX,0 overlap;
all its CMP probes therefore require the new public constructor.

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
performed by this finite gate. The full-project catalogue and fresh replay
gate is documented in [build and validation](../../../docs/validation.md).
Source implementation alone does not establish a compiled/replayed Lean API;
inspect a completed run's result, source bindings and receipts for evidence.
