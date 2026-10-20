# Checked control-flow graphs and local proofs

The reusable `X86.Sequential.CFG` layer checks a finite graph against exact
machine-code bytes. Separate local Lean obligations establish an independently
chosen result and read-permission contract. This removes the need to add a
whole-function shape recognizer for each new read-only control-flow pattern.
It does not infer invariants or certify an arbitrary imported program.

## Static checking and actual execution

[`CFG.check`](../EDSL/X86/Sequential/CFG.lean) accepts a graph only when:

- The explicit function window contains **1–64 bytes** and **1–32 static
  instructions**, completely partitioned into positive-length instructions.
- Each supplied node agrees with the actual sequential decoder at its offset.
- Every possible non-RET successor is another instruction boundary in the
  window, including both outcomes of conditional branches.
- Entry is a cutpoint. Each edge into a noncutpoint strictly decreases a
  checked finite depth bounded by `maxDepth`.
- Each operation belongs to the read-only sequential profile. Ordinary stores,
  locked operations and syscalls reject.

`check_sound` derives `CFG.Valid`. The discovery pass proposes instruction
nodes, cutpoints at entry and backward-edge targets, and depths; acceptance
rechecks that data. The bounds limit static code, not input length or the
number of loop iterations.

The graph is not an interpreter. `Sequential.step` still fetches and decodes
current actual memory. [`CFGTransport`](../EDSL/X86/Sequential/CFGTransport.lean)
relates that execution to the graph using current `CodeAt` and RIP. Successful
steps follow checked successors and preserve the full current memory, including
permission maps. Decode transport requires no padding after the last RET.
The [sequential ISA](sum32.md#separate-sequential-isa) retains its explicit
encoding, architectural and physical-conformance limits.

## Supply a contract before supplying a certificate

Write the task's input/output specification independently of the machine code.
For an objective grader, fix the task identifier, specification definition and
required theorem type before accepting a candidate. A proof of a candidate's
self-selected `Post`, a finite CFG import, or a successful bounded native run
does not establish that task's intended answer.

For new clients, start with the [verification guide](verify-a-function.md) and
[shared VCG](reusable-checker.md). Use `vcgen_run` for finite paths or
`vcgen_block` for sparse loop cutpoints, then the scalar/buffer call adapter.
These compose production instruction semantics and preserve the common ABI
and resource obligations. The lower-level annotation interface below is
available when that generated workflow does not fit; clients need not write
a transition rule for every instruction.

[`CFG.Annotations`](../EDSL/X86/Sequential/CFGVerification.lean) takes a fixed
`Post : State → Prop` and `AllowedRead : State → Read → Prop`. To extend it:

1. Select the exact raw function bytes, or an explicit ELF entry span, and
   obtain a checked graph. Preserve artifact/build identity separately.
2. State an admitted precondition: current code, input values/ranges, caller
   registers, return stack and any required resource/environment facts.
3. Define `Inv` at cutpoints and a natural-valued `rank` that decreases on
   every transfer into a cutpoint. Different loops can use different cases
   of the same rank function.
4. Define `Interior` for current states between cutpoints, retaining the
   source cutpoint and its original rank budget. Prove `binding` to current
   executable bytes and actual RIP, and `start` from cutpoint invariants.
5. Prove `localVC` for the actual decoded instruction and **both AF choices**.
   It establishes a successful step and current permission for every observed
   operand read. RET establishes `Post`; a continuing step establishes either
   a lower-rank cutpoint invariant or the next interior annotation.
6. Prove the admitted precondition implies the checked entry invariant, then
   apply `execution`, `sound`, `all_executions`, `safe` and `no_divergence`.
   Exhibit admitted inputs so an impossible precondition cannot hide a
   vacuous result.

These obligations describe local current effects. A successful future run is
not a premise of the generic theorem. Incorrect local facts cannot be supplied
as unverified certificate data; Lean must check their proofs.

[`Cutpoints`](../EDSL/X86/Sequential/Cutpoints.lean) first inducts on static
depth to compose a finite segment, then on dynamic rank across cutpoints. It
constructs actual execution for every undefined-AF choice stream, with at most
`(maxDepth+1)*(entryRank+1)` retired model instructions. `sound` derives a
successful evaluator run from this bound. Safety and read-origin theorems
retain local annotations at every actual continuing prefix; permissions and
successful operand loads refer to that prefix's current pre-instruction state.
The eight-byte RET read is included; instruction fetches use `CodeAt` separately.

The optional [`Cutpoints.Accounting`](../EDSL/X86/Sequential/CutpointsAccounting.lean)
API adds local equations for the remaining instruction count and ordered
operand reads. `execution_exact` composes those equations over real execution;
`sound` combines them with separately proved totality to run at exact fuel.
An instance must prove its equations. Static graph size alone gives no exact
dynamic count. Neither exact counts nor the conservative bound establish
hardware timing, micro-operation counts or minimum operations among alternative
implementations.

## Current examples

| Input | Implemented evidence |
| --- | --- |
| GCC 13 stride-two sum, 19 bytes | Independent even-index sum, all-choice total correctness, current OS admission/read origins, exact `6*count+4` instructions and ordered reads |
| GCC 13 two-buffer sum with two loops, 35 bytes | Independent two-list sum, all-choice total correctness, current two-input OS admissions, exact cost and ordered reads; [details](pair32.md) |
| Owned early-return function, 14 bytes | Complete static graph includes both RETs; truncation at the first RET rejects |
| Owned two-byte self-loop | Static graph accepted and actual divergence proved; static acceptance does not supply a termination theorem |

The stride specification in
[`Stride32.Contract`](../EDSL/Stride32/Contract.lean) selects the values at
indices `0,2,…,2*(count-1)` of a contiguous list of exactly `2*count` words,
then sums them modulo 2^32. Odd-index values do not contribute to that
independent result. The precondition binds the complete current array, a
nonwrapping span, full RSI count, executable bytes and an actual stack8 return
slot. The postcondition requires full zero-extended RAX, unchanged full memory,
actual return RIP/RSP, preserved GPRs outside `[rax,rsi,rdi,rsp]`, and preserved
nonarithmetic flags.

[`Stride32.Correctness`](../EDSL/Stride32/Correctness.lean) constructs execution
through the generic annotations. `exact_sound` derives successful evaluation at
`6*count+4` fuel using the local equations in
[`Stride32.Accounting`](../EDSL/Stride32/Accounting.lean). The ordered footprint
is exactly the even-index four-byte operands followed by the eight-byte return
slot. The count includes RET; it is not a minimum over alternative programs.

[`Stride32.Resources`](../EDSL/Stride32/Resources.lean) derives those current
facts from `OS.ArrayResources.Admission` with explicit caller-register bindings.
Each even-index four-byte operand lies within the current contiguous input
loan; the complete return slot uses its current stack loan. Empty input needs
no input loan. Logical loan authority and the OS RAM projection do not prove
native kernel enforcement or permit unmanaged interference.

## Import raw bytes or a function from an ELF

Build the importer and run it from the repository:

```sh
lake build edsl-cfg-import
lake exe edsl-cfg-import FUNCTION.bin artifacts/CFG.lean
lake exe edsl-cfg-import --elf 35 FUNCTION.elf artifacts/CFGELF.lean
lake exe edsl-cfg-import --elf-symbol function_name PROGRAM.elf artifacts/Named.lean
lake env lean -DwarningAsError=true tests/CFG.lean
lake env lean -DwarningAsError=true tests/Stride32.lean
EDSL_GCC=gcc-13 bash scripts/verify-cfg.sh
```

Raw mode uses the entire file as the selected function window. ELF mode
requires an explicit byte count in `1..64`; it never stops at the first RET.
The selected interval must be executable and file-backed under the restricted
ELF model. This allows an early-return branch to reach code after another RET.
The callable entry is not a process-startup contract. The
[named-function mode](named-elf-import.md) selects the declared full extent of
a unique function symbol, which may differ from the ELF entry, and checks the
complete file/name/metadata binding. It requires no hand-transcribed ELF tables.

The generated Lean file embeds literal bytes and a literal graph, recomputes
static acceptance, defines a typed `LocalObligations` interface and proves a
conditional execution theorem. ELF mode additionally embeds the full file and
image, proves parsing and selected entry bytes, modeled loading under page
freshness, and installed entry `CodeAt`. Current caller data/stack/resource
admission remains separate. No semantic proof holes or assumed correctness
axioms are emitted.

The CLI checks the emitted source with Lean and prints **`IMPORTED`**. It does
not print a functional certification verdict. Its kernel subprocess uses
`flock`; do not place an outer lock on the same build-lock file around the CLI.
The command needs `flock` available in addition to the pinned Lean toolchain.
The integration script imports owned compiler outputs, observes independent
native result/ABI oracles, and separately emits `RawFunctional.lean` and
`ELFFunctional.lean` for the stride and two-array contracts. Those supplemental proofs bind the
actual artifact bytes to the proved instruction instance, including exact cost,
read footprint and OS-admission wrappers. The early-return imports retain
static-only status.

| Exit status | Meaning |
| --- | --- |
| 0 | Literal finite-code import checked; functional/access obligations remain |
| 1 | Kernel checking failed |
| 2 | Invalid invocation |
| 3 | Unsupported span, instruction, graph or ELF feature |
| 4 | Malformed or truncated input |
| 5 | I/O failure |

Use the successful status and exact generated bytes. An existing output path
does not establish that the latest import succeeded. Rejection or timeout
establishes no defect. The synthetic cases in [`tests/CFG.lean`](../tests/CFG.lean)
exercise wrong instructions, incomplete windows, invalid branch targets,
missing cutpoints, false depths and excluded effects. All inputs are owned
fixtures; real security findings remain outside Git and CI.

## Remaining gates

General invariant discovery, arbitrary task grading, calls, writable CFG
effects, concurrency and source/IR preservation remain unimplemented in this
interface. Broader instruction support needs reviewed semantics and fail-closed
decoding before a local proof may use it. A whole OS additionally requires
privileged state, devices, interrupt behavior, implementation invariants and
hardware/runtime refinement; compiling it to assembly does not discharge those
obligations.
