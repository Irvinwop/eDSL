# Finite register and flag conformance

This fixture captures exact x86-64 instruction windows, compares their
observations with independent mathematical contracts, and emits Lean proofs
for replay through the production decoder and executor.

Run `bash scripts/verify-counter-displacement.sh --native-only` for controlled
Linux x86-64 SysV capture and independent persisted comparison. Run
`bash scripts/verify-counter-displacement.sh --replay RUN_DIRECTORY` to reuse a
sealed current-source native run without executing its windows again. With no
arguments the runner captures and replays. Full replay builds the current
production closure before pinning/copying its sources and providers.
Native-only does not require Lean admission or a previous readiness file.

The required inventory covers seven families. These are required windows;
a successful run separately records its actual observation counts:

| ID | Family | Literal windows |
| --- | --- | ---: |
| 0 | ADD32-imm8 | 40 |
| 1 | INC32 | 8 |
| 2 | LEA64 | 24 |
| 3 | SUB32-imm8 | 32 |
| 4 | CMP32-imm8 | 32 |
| 5 | LEA32 | 17 |
| 6 | TEST-low8-imm | 30 |

Every window requires all twelve unchanged `inputs.def` rotations and four
ADD-established flag seeds. The independent input values include dirty high
bits, zero, nibble/byte boundaries, signed limits, wrap and noncanonical words.
Ten controlled registers receive asymmetric cyclic rotations; RSP is an actual
live observation rather than a controlled table value. Replay authenticates an
explicit literal name/metadata/byte key inventory, the entire input rotation
and every input/probe/seed key. Neither aggregate counts nor a smaller complete
submatrix can replace that inventory. Runtime summaries derive from rows
actually checked after the complete required matrix passes comparison.

ADD/INC use RAX/RCX/R8/R9/R12/R13 with the original prefix and immediate cases.
SUB/CMP retain signed immediates80/ff/00/7f and no-prefix/canonical40/41 banks.
Unprefixed CMP EAX,0 remains a legacy production constructor, so the existing
matrix uses CMP EDX,0 for that one entry. SUB clears upper32; CMP preserves the
entire register file. Independent carry/borrow, signed overflow, nibble
carry/borrow and parity distinguish subtraction from ADD(-imm).

LEA64 retains its twelve plain and twelve SIB disp8 windows, all REX.W48..4f,
signed endpoints, scales, no-index/R12 cases and aliases. LEA32 adds no-prefix
and every W=0 REX40..47, all four Address constructors, explicit-zero disp8,
signed -128/-1/0/+127, destination/base/index aliases, no-index scales0..3,
X=1 R12 indexing and live source-only RSP. Unprefixed legacy 8d40/8d47 windows
are deliberately excluded from the new-family inventory. The independent
contract sums full64 prestate operands in signed wide arithmetic and reduces
LEA32 modulo 2^32, with upper32 zero and all flags preserved. Neither LEA family
reads data or requires a canonical/access-authorized computed address.
Output residues cannot distinguish mathematically equivalent early truncation;
finite agreement does not establish an unobservable implementation order.

TEST covers unprefixed AL/CL/DL/BL, canonical40 AL/SPL/BPL and canonical41
R8B/R9B/R12B/R13B/R15B. Representative controlled registers exercise raw
00/01/7f/80/ff masks; SPL and R12B include ff/80. All full64 registers survive.
The mathematical byte intersection uses arithmetic division/remainder and bit
weights, independent of the production evaluator and logical flag routines.
CF=OF=0; PF/ZF/SF use that byte result. AF alone is free; every other saved flag
bit is exact, including preserved nonarithmetic bits. There are no physical
SIL/DIL/R10B/R11B/R14B snapshots in this ABI. The actual model test
`tests/TestImmediate8.lean` already includes the needed SIL window and the
remaining byte banks. Model cases do not enlarge the observed physical subset.

The literal probe manifest schema is now:

```text
probe kind destination base index scale imm8 prefixed address_form instruction_hex
```

Fields are tab-separated. Family IDs0..4 retain their meanings; 5=LEA32 and
6=TEST-low8. Register numbers are architectural; index16 means absent.
Address forms are 0=base, 1=indexed, 2=baseDisp8, 3=sibDisp8. Non-LEA rows use
canonical unused address metadata (base0/index16/scale0/form0). Nondisplaced
forms have immediate0; indexed forms require an index. No form is inferred
from byte length and no second decoder/encoder constructs expected bytes.
The capture TSV header/order remains unchanged: six identifying/flag fields,
eleven before GPRs and eleven after GPRs. The snapshot ABI remains 192 bytes.

Assembly still saves/restores callee-saved GPRs and uses ordinary stack scratch.
Actual before/after GPRs are RAX RCX RDX RBX RSP RBP R8 R9 R12 R13 R15.
R14 holds the capture pointer; R10 is scratch. MOV and balanced PUSHFQ/POP-to-GPR
preserve flags around the exact labeled windows. No tested instruction writes
live RSP; TEST SPL only reads it. ADD outside each window seeds arithmetic
flags44/55/894/845. No arbitrary POPFQ installation occurs. All literal linked
window labels/bytes are authenticated before any opcode/manifest emission.
C++ `check CAPTURE.tsv OPCODE_DIR` also authenticates the sibling
`probes.tsv` and `inputs.tsv`, and never calls a tested window/intrinsic to
supply an expected value. The same parser, buffers and evaluator serve all
seven families.

`RegisterCapture.AFPolicy` has only `exact` and `undefinedAF`.
`checkWithAF` authenticates public production decodeAt, declared constructor,
exact length, new/nonlocked/no-store/no-read metadata and the actual choiceFlag.
Exact policy requires no choice; undefinedAF requires precisely AF, so an
AF-preserving OF-choice operation cannot enter as deterministic.
`stepCheckWithAF` runs actual public step false and true. Each compares the
entire final flags word against observed non-AF bits plus that exact AF choice.
This also represents the physical saved AF witness, without assigning a CPU
rule for undefined AF. Existing `check`/`stepCheck` signatures remain exact
wrappers. Exact relocated RIP, no operand reads, all sixteen modeled GPRs and
all three finite memory-map challenges remain required. The five unobserved
GPRs use distinct model canaries; RAM/value/execute/write maps are synthetic.
Existing exported fullRAMFrame/fullRAMAt contracts preserve the entire model
maps under their stated authenticated-decode/new/no-store/success assumptions.
These frames are separate from actual physical register observations.

All previous persisted and direct-step corruption controls remain. Extensions
mutate actual LEA32 high32/flags and TEST operand low/high halves, other GPRs and
defined/preserved flags. Direct TEST controls challenge every saved flag bit
except AF and low/high-half mutations of every observed GPR, bypassing schema
and independent-result guards. Distinguishing raw-mask/register-selector,
LEA32 aliased-prestate and no-index/R12 mutations reach actual production step.
AF-only flips are positive synthetic admissibility controls, never additional
native observations. Persisted missing/duplicate/malformed rows, wrong bytes/
lengths, a reduced probe matrix, wrong address form and missing input must fail;
full-mode generator rejections must occur before creating an output directory.

Generated proof modules keep sixteen finite rows each and ordinary
`decide +kernel` row theorems. Lean stays pinned to4.35.0 with warnings as errors,
autoImplicit=false, maxHeartbeats300000 and maxRecDepth128; no proof holes,
project axioms, unchecked solvers or increased caps. Each Lean/Lake call uses
one Lean thread and the existing shared lock/memory guard. No outer flock.
The runner pins/imports the actual Address32 and TestImmediate8 modules and
their transitive closure, then audits their context, signed arithmetic,
admissibility, choice and current-resource contracts together with the row
theorems. Only propext, Quot.sound and Classical.choice are on the existing
dependency allowlist. Each run records which checks actually completed.

PUSHFQ saves RF/VM as zero and cannot observe their hidden physical values.
AC/DF/TF must already be off. Long mode, ordinary RAM, debug/asynchronous and
exception-priority limits, Linux x86-64 SysV, the four-level canonical model,
CET/IBT and shadow stacks disabled remain target assumptions. The
ARCH_SHSTK_STATUS record distinguishes success from unsupported EINVAL/ENOSYS;
unsupported status does not discharge CET assumptions. Compiler flags still
exclude CET instrumentation. ELF/target/tool information and exact commands,
environments, exits, stdout/stderr and source/provider/opcode before/after pins
remain in ignored `.cache/popcount/native/run.*`, with closing SHA256 receipts
and seal. `NATIVE-READY` means native comparison only; `READY` also requires
current production replay and audit. Source equality rejects older-schema
native runs. No universal physical CPU/OS/ABI/resource/concurrency or
source/backend preservation claim follows. Failures are not security findings.
