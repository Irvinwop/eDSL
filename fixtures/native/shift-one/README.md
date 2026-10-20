# Independent native SHR64 by one

Run `bash scripts/verify-shift-one.sh` on Linux x86-64 SysV for capture,
independent saved-data checking and production Lean replay. Use
`--native-only` for the independent C++/assembly stage without Lean/Lake or
shared dependencies. Use `--replay SEALED_RUN` to replay a completed sealed
native-only run without repeating physical capture. Historical ELF files are
never executed; a newly built owned checker validates the preserved data.

The finite matrix is **40 exact windows × 32 rotated full64 inputs × 8 dirty
ADD-established arithmetic flag seeds = 10,240 observations**. Each window is
exactly REX.W `D1 /5`, ModRM mod3, count one. Prefixes 48/4a/4c/4e select
RAX/RCX/RDX/RBX/RBP; 49/4b/4d/4f select R8/R9/R12/R13/R15. Thus every ignored
R/X setting is exercised with ordinary B bank selection. RSP, capture pointer
R14 and scratch R10 are never tested destinations. Other registers, other
encodings, other counts, memory operands, faults and concurrency are outside
this native matrix.

`registers.S` emits a literal REX byte followed by an assembler-generated
`shrl $1, low-bank-operand` opcode. Hardware consumes REX.W/B and performs the
64-bit operation. The 32-bit operand spelling prevents a second REX; encoded
ESP with B=1 means R12. `probes.def` is a separate literal destination/byte
contract and is not included by assembly. Capture checks every linked start/end
label against this table **before any window runs**, then copies actual label
bytes into opcode files and writes manifests. A safe owned build with a changed
ignored prefix bit must reject at this preflight.

The input table includes 0, 1, 2, 3, nibble/byte/word/32-bit boundaries, highbit,
highbit+1/+2, signed maximum, allones, alternating and dirty high32 values.
All ten controlled GPRs receive cyclic rotations, so every destination sees
every input. The input contract and flag seed contracts are specified before
capture. Eight ADD pairs establish flags 44/55/894/845/10/4/0/84 without POPFQ;
each incoming arithmetic flag has both values across the seeds.

Actual observed GPRs are **RAX RCX RDX RBX RSP RBP R8 R9 R12 R13 R15**.
RSP is a real live stack value, not installed from an input table. Before and
after registers and PUSHFQ observations are saved using MOV and balanced
PUSHFQ/POP-to-GPR; callee-saved registers and the ordinary stack are restored.
The snapshot has surrounding buffer canaries and initially poisoned fields.
RDI/RSI/R10/R11/R14, memory/permission maps and OS resource authority are not
observed by the TSV. No synthetic model GPR or RAM values are reported as
hardware observations.

`capture` writes raw snapshots; it does not call the mathematical checker.
The separate `check CAPTURE.tsv OPCODE_DIR` mode executes no fixture windows.
Its independent result contract is unsigned **128-bit division by two**, with
CF = old value modulo two, OF = old MSB, SF/ZF from the result and PF from an
arithmetic count of low-byte bits. All saved nonarithmetic flag bits and all
observed nondestination GPRs, including RSP, must be preserved. This is a finite
arithmetic comparison, with no copied program interpreter or production
decoder/flag function.

**AF is undefined and masked for defined/preserved comparisons.** The original
full physical `rflags_after`, including AF, remains in the raw capture so a
later model adapter can choose that observed AF as an existential witness.
Neither physical AF=0 nor physical AF=1 is required. Separate, explicitly
synthetic control datasets force AF clear or set in every saved after-flags
word; both must pass. They check the mask policy, not physical observations or
Lean admission. Both model AF choices remain admitted, with
their defined bits agreeing; they must not both be equated to physical AF.
The generic `RegisterCapture.check` deliberately rejects `choosesAF` and
requires both full flag words to match. It remains unchanged. The owned
`tests/native/ShiftOneReplay.lean` adapter uses its capture parsing/state,
canary and frame helpers with a SHR-specific projection. It authenticates the
current production `decodeAt` constructor `shrOne64`, exact length three,
operand reads/store intents/lock policy and plain next observations. Both AF
choices execute; all sixteen modeled GPRs, exact RIP advance, defined flags
and every nonarithmetic bit must match. The actual full observed flags equal
the model flags selected by observed AF. The two model choices differ by
exactly AF; neither AF value nor physical variation is required.

An independent Lean Nat contract checks unsigned division by two, arithmetic
bit-count parity and the other defined flags without production flag helpers
or hardware. The exact literal 40 × 32 × 8 matrix binds all ten rotated inputs,
incoming seeds, saved opcode files and all 10,240 unique row keys. Every row
generates one ordinary `decide +kernel` theorem in 320 modules of 32 rows.
Compilation uses default budgets, Lean 4.35, warnings as errors, one thread,
direct `-j1`, and a separate `/tmp/edsl-lean-build.lock` acquisition for every
Lean/Lake call (Lake receives no `-j1`). A final transitive declaration audit
imports every generated module. There is no `native_decide`, solver result,
proof hole or project axiom. IO checking/generation alone is not replay proof.

Core's universal context/AF-choice/observed-witness theorems supplement the
finite replay with whole modeled RAM/permission frames and every other GPR.
Physical observations still cover only eleven GPRs; the other five, RIP,
memory and permissions are synthetic model challenges. Direct controls bypass
parsing to challenge result/upper bits, defined and preserved flags, unrelated
physical/model GPRs, missing bytes, REX bank, length/RIP, and all three map
projections. Both synthetic AF choices must pass. Parser controls reject
malformed, missing and duplicate rows. These are project controls, not defects.

Twenty negative controls challenge the independent result (including dirty
upper32), each defined flag, saved IF and a high nonarithmetic bit, a
nondestination GPR, live RSP, installed input, incoming seed flags, reported
window, out-of-range seed, malformed/missing/duplicate rows, saved opcode file
and actual linked bytes. Each must return exit 1 for its expected reason.
Corrupted data and mutated owned byte fixtures are synthetic project controls;
failures or timeouts establish no real security finding.

Target contract: Linux x86-64 SysV in long mode, stable project-owned ordinary
RAM/stack and code, CET shadow stack and IBT disabled, AC/DF/TF already off,
and no debug/asynchronous intervention in the observed instruction boundary.
`ARCH_SHSTK_STATUS` is recorded; enabled status or unexpected errors reject.
Unsupported EINVAL/ENOSYS does not discharge CET assumptions. PUSHFQ saves RF/VM
as zero; hidden physical RF/VM values or their preservation are not observed.
The runner disables CET instrumentation and records ELF notes and tool/target
information. Finite native agreement establishes no universal physical CPU/OS
refinement, memory authority, ABI/resource proof or compiler preservation.

The pinned profile is Clang 18.1.3, x86_64-pc-linux-gnu, GNU++26, warnings as
errors, integrated assembler, no LTO/red zone/CET instrumentation, BFD linker,
PIE and a nonexecutable stack. Unexpected compiler versions/targets reject.
Every new run gets a private `.cache/shift-average/native-replay/run.*` directory
with source snapshots, compiler/header dependency inventory, tool and loaded
library pins, objects, final ELF/text, disassembly, ELF inspection, raw data,
opcode/input/seed manifests, command/environment/timestamp/stdout/stderr/exit
receipts, corruption controls and before/after hashes. Replay first builds the
minimal current production closure through Lake, then pins its actual sources
and objects in place. It compiles the shared capture helper and owned adapter
from current sources into the actual `tests.*` build directory (Lean resolves
each package prefix at one root); generated chunks use the run's separate
output directory. It never copies/overlays production
objects or uses a private readiness file as a build prerequisite, so clean
checkouts use the same production build checks. Any closing source, import,
object or tool pin change fails. This is not a fresh whole-library build.

Historical replay verifies the **complete** original manifest/seal and all
seven original source snapshots. Current capture.cpp/registers.S/probes.def/
inputs.def/controls.awk must match those sealed sources byte for byte. Runner
and README evolution is explicitly allowed and inventoried with both hashes
and literal diffs: the old runner was native-only, and the current orchestration
adds replay and documentation. Neither entry is silently removed from an old
manifest comparison. The old seal and absolute-path binding manifests remain
unchanged; the new run records their identity, copies data/opcodes with equality
checks and has its own current source/tool/build receipts and closing seal.
The earlier native acceptance proves only that saved runner's native stage.

Failures are retained. `EVIDENCE.sha256` and its SHA256 seal detect changes;
they are integrity checks, not authentication. `NATIVE-READY` requires the
native comparison, its controls and closing pins. `READY` additionally requires
all 10,240 kernel replay theorems, the audit and stable current dependencies.
Core acceptance/source freeze is coordinated separately; a pending/failed
production closure cannot issue `READY`. No publication, ABI/OS authority,
physical refinement, compiler preservation or corpus credit follows from it.
