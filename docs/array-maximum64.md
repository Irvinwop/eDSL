# Full64 unsigned array maximum

The `arrayMaximum64` grading task specifies the mathematical unsigned maximum
of a list of 64-bit words, with zero for an empty list. RDI contains the input
base and RSI its element count. `ArrayMaximum64.maximumNat` uses natural word
interpretations; its upper-bound characterization is independent of flags,
instruction selection, a compiler, read order or instruction count.

The result contract requires actual return to the caller, RSP advanced by
eight, complete unchanged RAM and permission functions, and all nonarithmetic
flag bits preserved. Every GPR outside RAX, RCX, RDX and RSP is preserved,
including RDI and RSI. Arithmetic status flags may change. The semantic claim
constructs terminating execution for every admitted list, incoming register
and flag state, and modeled undefined-AF choice stream.

## Current array resources

`X86.ArrayAt64` observes complete little-endian eight-byte words in current
RAM. `ArrayBound64` requires a nonwrapping natural byte span and permits its
endpoint to equal 2^64. A nonempty array must also have current authorized
read authority for the complete input span. Current well-formed loans imply
canonicality of every actual element byte. No alignment is required.

`OS.ArrayResources64.Contract` extends current executable-code and original
caller-slot resources with the actual array, bound and input loan.
`Current` couples the complete machine memory record to that same borrowing
world, including unrelated cells and all permissions. Read-only aliases are
compatible: an input may share the original caller slot and reuse its loan ID
when the values and span agree. Admission introduces no artificial
disjointness between compatible read-only resources.

An empty input needs no input mapping, allocation or loan and imposes no
alignment or canonicality constraint on the unused RDI bits. Its input loan
ID may be absent or alias another ID. Actual code and the complete original
eight-byte caller slot remain required. The return target and post-return
stack pointer retain their canonicality and stack-bound conditions.

Registration fixes all-input correctness, current admission, reachable
read-only effects, successful authorized operand reads and returned current
authority. Its general read permission uses current worker loans; it fixes
neither the input-read order nor a compiler's narrower footprint. These two
clients separately prove that their only operand reads are each original
DATA8 element in index order followed by the original STACK8 caller slot.
Fetches are checked separately from operand reads.

Complete RAM equality retains the same coherent world, owners, allocation
epochs, permissions and existing loans at every reachable prefix and return.
There is no future-execution premise in resource admission. The useful domain
witness has a nonzero full64 maximum and works for every nonempty candidate
byte span up to 4096 bytes independently of decoding or execution. This
nonvacuity witness does not exclude empty or zero-only inputs from the task.

## Two complete final compiler outputs

The client implementations live under `tests/fixtures/ArrayMaximum64/` and
remain outside trusted grader imports. `Known` imports the independent domain
and its nonvacuity theorem, without importing a maximum implementation.

| Compiler | Bytes | Complete final `.text` |
|---|---:|---|
| GCC 13 | 26 | `31d231c04839f27410488b0cd74839c8480f42c148ffc2ebebc3` |
| Clang 18 | 32 | `4885f6741831c931c0488b14cf4839c2480f47c248ffc14839ce75edc331c0c3` |

Both outputs use actual indexed full64 loads, unsigned CMP/CMOV64, loop
branches and RET. GCC tests the loop bound before each iteration; Clang has
a separate empty path and a tail test. Each proof covers every element ordering,
all upper-half and sign-bit values, and every modeled AF stream.

`GCC.raw_semantics` and `Clang.raw_semantics` establish the independent result
and frame. Their `raw_policy` theorems cover all reachable prefixes.
`readOnly_semantics_of_raw` transports those proofs to current OS resources.
The closed exports are:

| Module | Registered claim |
|---|---|
| `tests.fixtures.ArrayMaximum64.GCCExport` | `EDSL.ArrayMaximum64.Client.gcc` |
| `tests.fixtures.ArrayMaximum64.ClangExport` | `EDSL.ArrayMaximum64.Client.clang` |

Separate accounting proves `7*n+5` modeled instructions for GCC, and four
for empty Clang input or `6*n+5` for nonempty Clang input, including RET.
`GCC.execution_exact` and `Clang.execution_accounting` apply to any actual
returning execution under the same entry premises and prove the ordered
operand reads as well. These counts are absent from the registered claim.
They establish no lower bound, global optimum, micro-op count or timing result.

The native source is GNU23, using `-std=gnu2x -Os`, warnings as errors,
no LTO or CET instrumentation, and function sections. Each function is
separately final-linked; selection uses the entire final `.text` and rejects
final relocations. Compiler drift is unsupported output, not a compiler defect.
The final callable ELF is a function container, not a standalone process.
No source-to-machine preservation theorem is claimed.

## Validation and grading

```sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-array-maximum64.sh
```

Full mode records and verifies a source snapshot, builds and audits the Lean
proofs, replays stored terms through a fresh kernel, and checks trusted-client
isolation. Both reference and body packets grade against exact raw bytes and
complete explicit-span ELF artifacts with unchanged default limits: four
exports and eight successful grades. Changed task IDs, shortened spans,
altered bytes and cross-compiler proof reuse require eight status-5 rejections.
The recorded full run passed all these gates and the separate native checks.
Native-only mode omits the proof gates explicitly.

`tests/ArrayResources64.lean` uses independently assigned literal bytes for
unaligned high-address loads, destination/address-register aliasing and exact
loan bounds. It also checks that a high index is not truncated, an omitted
eighth byte rejects, unrelated permission changes violate current coupling,
and empty or compatible caller-slot alias admission needs no extra resource.

`--native-only` explicitly records universal Lean validation as not run. The
native observer executes embedded copies of the actual final extractions and
checks both complete identities before any probe. Its independent unsigned
oracle requires original-input membership and an upper bound for every
original value, or zero for empty input. Input snapshots also check memory
framing. Aligned and unaligned read-only inputs near guard pages exercise
width and endpoint handling; empty inputs include inaccessible and
noncanonical unused bases. The caller observer captures actual return-stack,
register and effective nonarithmetic-flag behavior.

The recorded native-only validation passed 387,328 positive calls across the
two outputs, 23 owned synthetic mutant counterexamples and eight pre-probe
extraction rejections. Mutants exercise result, narrowing, unsigned order,
endpoint, memory, register, stack and flag defects in the observer's contract.
Altered, truncated, extended and substituted extractions reject before
execution. These are finite observations; they do not establish an all-input
proof. Signals and timeouts are inconclusive.

The separate parallel `array-maximum64.yml` workflow caches the pinned Lean
toolchain and a distinct partial Lake build. Cache reuse does not replace
auditing, fresh kernel replay, isolation, proof grading or native execution.
Evidence defaults to `artifacts/array-maximum64/`; override its destination
with `EDSL_ARRAY_MAXIMUM64_OUTPUT` for local archival storage.

## Boundaries

Theorems use the sequential ordinary-RAM x86-64 profile with current stable
code, inputs and caller memory, four-level canonical addressing, suitable
CPU/ABI state and CMOV support, disabled alignment checking/CET and no modeled
asynchronous interference. The pinned Lean kernel checks the proofs; the
dependency audit permits only `propext`, `Classical.choice` and `Quot.sound`,
as applicable.

Native Linux/System V observations supply finite conformance evidence under
their recorded environment. They do not establish physical CPU or whole-kernel
correctness, OS implementation refinement, concurrency or atomicity,
speculation, universal physical memory-access traces, or source/IR
preservation. General GNU C++26/LLVM frontends and broader ISA/OS coverage
remain separate work.
