# Full64 modular array sum

The `arraySum64` grading task specifies the unsigned mathematical sum of a list
of 64-bit words, reduced modulo 2^64, with zero for an empty list. RDI contains
the input base and RSI its element count. `ArraySum64.sumNat` sums the natural
interpretations of the original words; `sumMod` reduces that natural sum only
at the end. The specification is independent of instruction selection,
accumulator registers, loop shape, read order and instruction count.

The result contract requires actual RET to the original caller target, RSP
advanced by eight, complete unchanged RAM and permission functions, and all
nonarithmetic flag bits preserved. Every GPR outside RAX, RCX, RDX and RSP is
preserved, including RDI and RSI. Arithmetic flags may change. The client
proofs construct terminating execution for every admitted array, incoming
register/flag state and modeled undefined-AF choice stream, including empty,
zero-only, wrapping and nonempty wrapping-to-zero inputs.

## Current array resources

`X86.ArrayAt64` observes complete little-endian eight-byte elements in current
RAM. `ArrayBound64` requires a nonwrapping natural byte span; its endpoint may
equal 2^64. Current OS admission additionally requires live code, original
caller-slot and nonempty input loans for the same worker. Well-formed current
loans require canonical bytes throughout each actual element. No element
alignment is required. The Linux native target uses lower canonical userspace.

`OS.ArrayResources64.Current` couples the entire machine memory record,
including unrelated cells and all permissions, to the same borrowing world.
Compatible read-only aliases are admitted: input and caller-slot regions may
share a loan ID when their contents and spans agree. Complete memory equality
retains current owners, allocation epochs, permissions and loans at every
reachable prefix and actual return.

An empty input needs no input mapping, allocation or loan, and imposes no
alignment or canonicality requirement on unused RDI bits. Its input loan ID
may be absent or alias another ID. Code and the complete original eight-byte
caller slot remain required, with a canonical return target and post-return
stack pointer and the stated nonwrapping stack bound.

`ArraySum64.ResourcePre` contains current observations and authority, with no
execution, future-success or cost callback. Registration requires successful
authorized reads and read-only effects at every actual reachable prefix.
General read permission comes from current worker loans; the task does not
fix the narrower read footprint of either compiler client.

`ArraySum64.Domain` constructs useful current inputs for every nonempty
candidate **code** span of at most 4096 bytes, including unsupported opcodes,
with arbitrary other incoming registers and full flags. No decoding or
execution premise is needed. Usefulness requires a positive modular sum;
it does not restrict admission or remove empty, zero or wrapping-to-zero
inputs from the universal contract.

## Two complete compiler clients

The implementations live under `tests/fixtures/ArraySum64/`, outside trusted
grader imports. The registry imports the independent contract and domain.
It accepts a proof for the fixed `arraySum64` task rather than requiring a
particular compiler or decoded loop shape.

| Compiler | Bytes | Complete final `.text` |
|---|---:|---|
| GCC 13 | 22 | `31c031d24839f07409480314c748ffc0ebf24889d0c3` |
| Clang 18 | 25 | `4885f6741131c931c0480304cf48ffc14839ce75f4c331c0c3` |

GCC uses `ADD RDX,[RDI+RAX*8]` and a loop-header count test. Clang uses
`ADD RAX,[RDI+RCX*8]`, a tail count test and a separate empty path. The complete
Clang profile includes both RETs and the suffix after the first RET. Both use
the pre-state full64 effective address and accumulator for each addition.
Their natural-sum suffix invariants justify intermediate wrapping independently
of the machine implementation of the result.

`GCC.raw_semantics` and `Clang.raw_semantics` prove the independent result,
termination and frame; `raw_policy` covers every reachable prefix for all AF
choices. `readOnly_semantics_of_raw` composes these with current OS authority.
The closed registered claims are:

| Module | Claim |
|---|---|
| `tests.fixtures.ArraySum64.GCCExport` | `EDSL.ArraySum64.Client.gcc` |
| `tests.fixtures.ArraySum64.ClangExport` | `EDSL.ArraySum64.Client.clang` |

Separate accounting proves `5*n+6` modeled instructions for GCC and four for
empty Clang input or `4*n+5` otherwise, including RET. `GCC.execution_exact`
and `Clang.execution_accounting` also prove that every actual returning
execution reads the original DATA8 elements in index order, then the original
STACK8 caller slot. Fetch checks are separate from operand reads. Neither
accounting nor read order is part of the registered semantic claim. These
counts establish no minimum operation count, micro-op count or timing bound.
Static CFG validity alone establishes no functional sum theorem.

The native source is GNU23, compiled with `-std=gnu2x -Os`, warnings as errors,
LTO and CET instrumentation disabled, and function sections. Each object is
separately final-linked with entry `sum64_array` at `0x401000`; selection checks
the complete final `.text` and absence of final relocations. Compiler drift is
unsupported output, not a compiler defect. The callable ELF is a function
container, not a standalone process. No source/IR preservation theorem follows.

## Validation requirements and evidence

```sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-array-sum64.sh
```

Default success requires the native checks and all proof gates. Full mode
snapshots and checks the Lean sources, builds the clients and exports, runs
resource/registration regressions and transitive axiom audits, replays stored
terms through a fresh kernel, and checks trusted/client snapshot isolation.
Both reference and body packets must export and grade against the exact raw
bytes and complete explicit-span ELF artifacts using unchanged default limits:
four exports and eight positive grades. Changed task, shortened span, internally
altered bytes and cross-compiler bytes require eight status-5 rejections.
Binding rejection does not establish a semantic defect in the changed code.
A separate full-mode checkpoint passed all of these gates for the selected
22/25-byte artifacts, including both packet modes at unchanged default limits.
The native-only record below remains separate finite execution evidence.

`tests/ArraySum64.lean` exercises actual decoded execution on independently
specified full-width, repeated-wrap and nonempty zero-result vectors, exact
return/read behavior and insufficient fuel before RET. It also checks current
returned authority, compatible caller-slot aliasing, unused empty bases and
loan IDs, independent unsupported-code admission, and registry/import isolation.
The main Lean workflow invokes this test alongside the array-maximum test.

`--native-only` explicitly leaves universal Lean validation `NOTRUN`. The
native observer embeds the two actual complete final extractions and checks
both slots against fixed profiles and supplied extractions before any probe
or stdout. Alteration, truncation, extension and cross-compiler substitution
must reject before execution. Supplied files are read as data.

The result oracle uses original input snapshots and base-256 byte-column sums
with a carry chain, discarding carry above byte seven. It does not run a second
scalar qword fold. Full accessible input pages, including padding, are compared
after every call. The observer checks six saved GPRs, RDI/RSI/R8..R11, actual
CALL/RET stack adjustment and effective nonarithmetic RFLAGS. It seeds other
registers and covers all 128 combinations of the six arithmetic flags and ID
on selected vectors; DF is clear at the System V call.

The inspected native-only run passed **387,328 positive calls**, **23 safe owned
synthetic mutant rejections** and **eight pre-probe extraction rejections**.
Its archived source copies match the reviewed fixture and script. Selected
arrays cover unsigned edges, high halves, carry boundaries, multiple lengths
through 511, aligned/unaligned guard-page endpoints, writable padded framing
and deterministic random inputs. Empty calls use null, inaccessible and
noncanonical unused bases. The finite native selection does not cover every
admitted model input or establish universal physical access traces.

Mutants cover XOR, sign-extending/narrow loads, skipped elements, zero,
saturation, nonzero empty results, memory, registers, stack adjustment and
nonarithmetic flags. Nonempty mutants receive owned writable padded arrays;
only the requested observed failure category counts as a counterexample.
Signals, timeouts and environmental failures fail inconclusively.

The parallel `array-sum64.yml` workflow uses GCC 13/Clang 18 and the default
script. It shares the pinned Lean toolchain cache and saves a distinct
`lake-array-sum-v1` partial build cache, with compatible earlier builds as
restore inputs. Cache reuse never skips proof or native gates and never saves
a partial build under the main full-project cache key. Evidence defaults to
`artifacts/array-sum64/`; `EDSL_ARRAY_SUM64_OUTPUT` selects local archival
storage. CI retains only this project's owned synthetic fixture evidence.

## Target and trust boundaries

The model uses the sequential ordinary-RAM x86-64 callable profile, four-level
canonical addressing and current OS loans. Abstract regions may occupy either
canonical half; the Linux native target uses lower canonical userspace. Physical
interpretation requires stable coherent code/input/caller memory, suitable
CPU/ABI state, alignment checking and CET disabled, and no asynchronous or
concurrent interference. Native observations require Linux x86-64/System V,
a usable aligned host stack and the recorded compiler/kernel/CPU environment.
Arbitrary modeled flags do not remove physical control-state requirements.

Lean is pinned by `lean-toolchain`, with warnings as errors. Dependency audits
permit only the standard `propext`, `Classical.choice` and `Quot.sound`, as
applicable; fresh kernel replay remains a separate required check. The claims
prove the stated Lean model contracts under their assumptions. Native checks
supply finite evidence. Neither establishes general source/IR preservation,
physical CPU or whole-kernel correctness, OS implementation refinement,
concurrent visibility, atomicity, speculation, timing or optimality. General
GNU C++26/LLVM frontends and broader ISA/OS support remain separate work.
