# Memory-source ADD64

The separate Lean `X86.Sequential` backend accepts a single REX.W prefix
`48`–`4f` followed by opcode `03 /r` with a mod=00 memory source. The full64
destination may be any of the 16 GPRs. The existing strict base/SIB profile
admits real bases and indices, scales 1/2/4/8, and R/B/X bank extensions.
With X=1, SIB index4 denotes R12; plain-base encodings ignore X. Instructions
occupy three bytes for a plain base or four bytes for SIB.

The instruction reads a complete little-endian qword at the pre-state effective
address and adds it to the old destination modulo 2^64. Both operands use the
old state when the destination aliases a base or index, including RSP. The
result defines CF/PF/AF/ZF/SF/OF through `addFlags64` and preserves every other
flag, every other register, the entire RAM and both permission maps. The
operand footprint is exactly one DATA8 read; there is no store intent or
locked event. The instruction has no undefined-AF choice.

`execute_addMem64_context` exposes that complete frame and next PC.
`execute_addMem64_arithmetic` relates the result to the natural sum modulo
2^64, carry to its mathematical range and overflow to signed addition.
`execute_addMem64_success_iff` requires the actual complete qword load;
`execute_addMem64_fault` propagates a failed load. Missing or unreadable bytes,
noncanonical spans and wrapping qword spans reject. Unaligned ordinary reads
are admitted under the modeled alignment-checking profile.

Displacements, RIP-relative addressing, missing base/index encodings,
memory-destination opcode `01`, W=0, LOCK and extra/repeated prefixes remain
unsupported. Existing register ADD encodings remain supported. The legacy
decoder, concurrent/TSO instruction profile and sum32 shape checker do not gain
this instruction.

## Current OS resources

`OS.ReadOnlyArithmetic64` connects current named read authority to actual
execution. `CallResources.addMem64_enabled` requires a successful checked
`Borrowing.loadWord64` for the current worker's principal, named live loan
and pre-state effective address. It derives a real qword load, exact flags,
DATA8 permission and execution success. `current_addMem64_step` additionally
uses actual current decoding. Raw CPU readability alone supplies no loan.

The corresponding `ArrayResources64` lemmas derive the checked read from a
present array element and its effective address. Complete current RAM coupling
retains the same coherent OS world, metadata, code, permissions and loans.
Compatible read-only aliases need no added disjointness condition. An RSP
destination retains the original caller-slot loan and bytes; it grants no
authority or return-slot binding at the new RSP. The resource regression
follows such an addition with an actual RET fault at the new unmapped slot.

Contracts assume stable ordinary sequential RAM, the modeled canonical-address
profile, alignment checking and CET disabled, and no asynchronous interference.
They establish no concurrent visibility, atomicity or whole-kernel guarantee.
This foundation supports the missing instruction family in the observed
22-byte GCC and 25-byte Clang scalar array-sum outputs. No independent
`ArraySum64` correctness theorem or registered array-sum task is implemented.
Static CFG import alone does not prove functional correctness, and this
extension proves no minimum operation count or timing bound.

## Independent native conformance

`scripts/verify-sequential-add-memory64.sh` builds 64 owned instruction windows
and runs 12 profiles per window, producing 768 positive CPU observations per
compiler. The fixture includes the exact GCC `48 03 14 c7` and Clang
`48 03 04 cf` addition windows. Coverage includes all 16 destinations, RSP
changes, bank extensions, every scale, ignored X without SIB, address aliases,
full64 indices, unaligned qwords and the final aligned qword before a guard page.
These are finite selected inputs rather than exhaustive physical conformance.

Before any probe or Lean stdout, the observer compares the supplied extraction
with the entire final executed ELF section, including harness and capture code.
Altered, truncated and extended extractions must reject before execution.
The C oracle independently checks all 16 GPRs, complete effective RFLAGS and
the entire read-only 4096-byte data-page snapshot. It uses a 65-bit unsigned sum,
nibble carry, sign comparisons and low-byte population count to determine
arithmetic flags. The capture restores the real host stack before saving flags
and performs no stack access while an arbitrary modeled RSP is installed.

Nine safe owned mutants must violate their requested oracle category: narrow
arithmetic or load, wrong operation/destination/address, omitted flags, cleared
carry or altered nonarithmetic flags. No intentional invalid-memory mutant is
executed; signals and timeouts are failures, not semantic counterexamples.

Positive observations generate Lean theorems using actual `Sequential.step`
on literal observed bytes and states for both AF choices, followed by the
transitive dependency audit. The sparse replay maps only instruction bytes and
the eight observed source bytes, with no writable memory. It checks every GPR,
all flags, exact next PC, complete modeled memory/permissions and the DATA8
footprint at the old effective address. Operand footprints are independent
contracts, not hardware memory-access traces.

```sh
lake env lean -DwarningAsError=true tests/SequentialAddMemory64.lean
lake env lean -DwarningAsError=true tests/SequentialAddMemory64Resources.lean
EDSL_CLANG=clang-18 bash scripts/verify-sequential-add-memory64.sh
```

Evidence, source copies, provenance, status and hashes go to
`artifacts/sequential-add-memory64/`. Default success requires the native
contracts, kernel replay and audit. `--native-only` explicitly leaves model
replay `NOT RUN`; it does not establish model conformance. The optional
`EDSL_ADD_MEMORY64_LEAN_ROOT` reuses an existing checkout and its build cache.
CI runs the default mode and retains only these owned fixture artifacts.

The native harness requires single-threaded Linux x86-64, ordinary selected
user flags, alignment checking and CET disabled. These checks do not establish
universal ISA/CPU/OS correctness, physical fault delivery, timing, speculation,
concurrent execution, source-language preservation or bootstrap compiler
correctness.
