# Grading the fixed full64 counted DATA8 contract

`edsl-grade-call-memory-loop64` checks `EDSL.CallMemoryLoop64.Claim` for an
exact code window and selected entry. RDI supplies the current owned DATA8
pointer, RSI the full64 value `x`, and RDX the full64 count `n`. Every admitted
current resource world, initial CPU state, old DATA word and undefined-AF
choice stream must have an actual covered returning CPU/OS execution:

| Output | Required result |
| --- | --- |
| RAX | `(x + n) mod 2^64` |
| DATA8, `n = 0` | The actual initial target word |
| DATA8, `n > 0` | `(x + n - 1) mod 2^64` |

The contract includes zero and maximum full64 counts, at least **32 private
bytes**, both current owner capabilities, original caller RET and RSP+8,
callee-saved registers, nonarithmetic flags, permissions and allocation/loan
metadata. RAM outside the union of the provided private allocation and DATA8
is unchanged. A useful nonvacuity witness accompanies the universal claim.
See the [resource contract](call-memory-loop64.md) for admission details.

Candidates supply bytes and proof data; they cannot select the specification,
domain, execution engine, resource policy, imports or budgets. Admission assumes
no future execution. Acceptance requires no loop, CALL, target reload,
intermediate DATA writes, operand-read order, count restriction, compiler
profile or instruction cost. This is a standalone fixed task; the older
`CallStack` and `CallMemory64` task propositions retain their separate scope.

## Clients and commands

| Client | Whole text | Entry | Helper | Exact modeled instructions, `N = n.toNat` |
| --- | ---: | ---: | ---: | --- |
| GCC 13 nested | 45 bytes | 0 | 38 | `12 + 10*N` |
| Clang 18 nested | 52 bytes | 0 | 45 | `4` at zero; otherwise `12 + 9*N` |
| GCC 13 closed form | 17 bytes | 0 | none | `4` at zero; otherwise `6` |
| Clang 18 closed form | 19 bytes | 0 | none | `5` at zero; otherwise `7` |

The closed-form source, `fixtures/call-memory-loop64-closed-form.c`, computes
`result = x+n`, stores `result-1` only when `n != 0`, and returns `result`.
It uses the same GNU23 `-Os` compiler/linker profile as the nested fixture.
`EDSL.CallMemoryLoop64.ClosedForm.claim` takes `Profile.gcc` or `Profile.clang`
from that namespace and proves the unchanged root contract. Costs are separate
retired-instruction results in the model, without a global minimum, cycle or
micro-op claim.
These machine-code proofs establish no C/volatile or source/IR preservation
theorem. Native observations cover the nested profiles only; closed-form
clients receive proof grading.

Build the pinned installation and compiled clients:

```sh
lake build edsl-grade-call-memory-loop64 edsl-proof-export \
  tests.fixtures.CallMemoryLoop64.GCC tests.fixtures.CallMemoryLoop64.Clang \
  tests.fixtures.CallMemoryLoop64ClosedFormExports
```

For the corresponding complete nested raw extractions and linked ELFs:

```sh
lake env .lake/build/bin/edsl-proof-export \
  tests.fixtures.CallMemoryLoop64.GCC EDSL.CallMemoryLoop64.GCC.claim gcc-nested.json
lake env .lake/build/bin/edsl-proof-export \
  tests.fixtures.CallMemoryLoop64.Clang EDSL.CallMemoryLoop64.Clang.claim clang-nested.json
lake env .lake/build/bin/edsl-grade-call-memory-loop64 0 gcc-nested.bin gcc-nested.json
lake env .lake/build/bin/edsl-grade-call-memory-loop64 --elf 45 0 gcc-nested.elf gcc-nested.json
lake env .lake/build/bin/edsl-grade-call-memory-loop64 0 clang-nested.bin clang-nested.json
lake env .lake/build/bin/edsl-grade-call-memory-loop64 --elf 52 0 clang-nested.elf clang-nested.json
```

The exporter takes a closed named theorem. The closed-form aliases below are
in `tests.fixtures.CallMemoryLoop64ClosedFormExports`, importing the proofs
from `tests.fixtures.CallMemoryLoop64.ClosedForm`:

```sh
lake env .lake/build/bin/edsl-proof-export \
  tests.fixtures.CallMemoryLoop64ClosedFormExports \
  EDSL.CallMemoryLoop64.ClosedForm.Exported.gcc gcc-closed.json
lake env .lake/build/bin/edsl-proof-export \
  tests.fixtures.CallMemoryLoop64ClosedFormExports \
  EDSL.CallMemoryLoop64.ClosedForm.Exported.clang clang-closed.json
lake env .lake/build/bin/edsl-grade-call-memory-loop64 0 gcc-closed.bin gcc-closed.json
lake env .lake/build/bin/edsl-grade-call-memory-loop64 --elf 17 0 gcc-closed.elf gcc-closed.json
lake env .lake/build/bin/edsl-grade-call-memory-loop64 0 clang-closed.bin clang-closed.json
lake env .lake/build/bin/edsl-grade-call-memory-loop64 --elf 19 0 clang-closed.elf clang-closed.json
```

These filenames stand for byte files matching the stated selected programs;
the commands do not compile C or produce the input artifacts. Each grade is a
fresh process checking one candidate. The integrated reproduction interface is
documented in [counted DATA8 verification](call-memory-loop64.md#reproduction-and-evidence-boundaries).

## Artifact binding, trust and limits

The CLI syntax is
`edsl-grade-call-memory-loop64 [--elf SPAN_BYTES] ENTRY_OFFSET INPUT PROOF.json`.
`EDSL.Grading.CallMemoryLoop64.Artifact` reuses the unchanged CallStack raw/ELF
formats and pure selector. Its own `Artifact.Claim` conjoins successful literal
selection with the full-count root claim for `selected.program`.

Raw mode retains the whole file. ELF mode selects the whole window beginning
at `e_entry - ENTRY_OFFSET`, including any helper before or after the caller.
The window must fit in one executable file-backed segment in the lower
canonical address range. Selection never scans for a first RET. The kernel
checks the entire literal file, span, entry and successful selector reduction
in the final wrapper. Changing a nonloaded ELF note may legitimately reuse a
program proof if the selected program is identical, with a new checked literal
wrapper.
This proves the callable contract on admitted worlds, without ELF startup,
other-segment or whole-process safety. Supplying the current resource world
and satisfying loader freshness remain caller obligations.

Exporter and driver use the same five fixed foundational imports: `Known`,
`Artifact`, `CallStack.Artifact`, `CallMemory64.Artifact` and
`CallMemoryLoop64.Artifact`, all under `EDSL.Grading`. The extension contains
generic admission, cutpoint and private-memory infrastructure, with no compiler
fixture imports or byte whitelist. Client lemmas remain untrusted serialized
declarations, independently kernel-checked and audited. Only the exporter
loads the requested compiled client module. The grader accepts data, uses its
isolated installed search path, ignores user `LEAN_PATH` and loads no client
modules or plugins. Lean is pinned to 4.35.0 with warnings as errors; only
`propext`, `Classical.choice` and `Quot.sound` are approved axiom dependencies.
The executable, project objects and Lean sysroot must be immutable trusted products.

Defaults remain 4,194,304 packet bytes, expression depth 128, 300,000 decoder
steps, 256 declaration entries/generated names, 100,000 audit steps and
10,000,000 kernel heartbeats. Packet and wrapper share a cumulative kernel
budget; wrapper recursion depth 32768 is the existing baseline. Raw files and
selected windows are bounded by 4096 bytes, ELF files by 65536 bytes.

Acceptance prints `ACCEPTED` and exits 0. Usage exits 2, unsupported admission 3,
malformed packets 4, proof/audit rejection 5, resource exhaustion 6, and IO or
installation failure 1. Rejection, timeout and unsupported code establish no
defect.

The ordinary sequential RAM, four-level canonical-address, AC/CET-disabled and
no-asynchronous-interference assumptions remain unchanged. Source/IR proofs
are optional; this slice establishes no frontend preservation, physical CPU or
kernel refinement, concurrency, atomic, syscall, recursion or indirect-call
claim. General task registration remains separate work.
