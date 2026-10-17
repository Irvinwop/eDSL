# Grading owned callable code

`edsl-grade-call-stack` checks a fixed full64 `(input + 2) mod 2^64` callable
contract against complete selected code bytes and an explicit entry offset.
A submission supplies code and proof data. The grader fixes the input domain,
result, ABI/memory frame, CallReturn engine and code-extent policy. Neither a
compiler profile nor a claim supplied by the candidate chooses these rules.

This is a separate resource-first contract. It quantifies over every current
`CallStack.ResourcePre` world and every undefined-AF stream. It requires a real
`CoveredExecution` ending at the original caller-slot RET, with the independent
`CallStack.Post`. It proves actual machine behavior on those OS-admitted worlds;
it does not assert universal correctness on all unmanaged raw `Pre` states.
The existing `edsl-grade` task propositions and Sequential engine stay intact.

## Contract and evidence

`EDSL.Grading.CallStack.Claim program` combines universal `SemanticClaim` and
a useful nonempty input domain. Admission requires present code/caller loans,
a current unborrowed private allocation, complete qword permissions, input and
entry bindings, at least 16 private bytes and the stated external stack
alignment. It assumes no decoder success, future execution, result or budget.
`CallStack.Domain.resource_pre` constructs admission for arbitrary nonempty
byte windows up to 4096 bytes and every in-bounds entry, full64 argument,
other GPRs and flags.
Unsupported code still has admission; supplying a correct execution proof is a
separate obligation.

`FetchWithin` binds the actual decoded instruction and its full encoded length
to the stable code window. Prefix proofs cover every real pre-instruction state,
including both internal and original RET. The final return target may be outside
that window because the callable boundary does not fetch it. Current code and
original caller loans remain live through the actual checked CALL/PUSH stores;
private reads create no loans. The postcondition retains callee-saved GPRs,
nonarithmetic flags, all permissions and RAM outside the private frame. Private
bytes may remain dirty. `Returned` retains the same actual CPU/OS execution,
coupled endpoint, private history, resource metadata and reusable owner authority.

No instruction shape, CALL requirement, cost formula or operand-read order is a
task acceptance condition. The nested compiler clients and the two-instruction
inlined implementation are witnesses for the same independent contract.
Accounting is separate: accepted implementations need at least two modeled
instructions on admitted inputs requiring RAX to change, and the inlined LEA/RET
implementation attains two. This is a bound for this modeled ISA and callable
boundary, not a claim about CPU cycles, micro-ops or all possible x86 instructions.
`EDSL.Grading.CallStack.minimum_modeled_instructions` states the lower bound;
`EDSL.CallStack.Inline.optimal_for_useful_inputs` supplies its attaining witness.

The closed nested-client proofs live in `tests.fixtures.CallStack.Covered`:

| Proof in `EDSL.CallStack.Client` | Whole window bytes | Entry offset | Modeled instructions |
| --- | ---: | ---: | ---: |
| `gccSame` | 14 | 5 | 5 |
| `gccSeparate` | 16 | 0 | 7 |
| `clangSame` | 16 | 5 | 7 |
| `clangSeparate` | 16 | 0 | 7 |

`tests.fixtures.CallStack.Inline` supplies the different five-byte
`48 8d 47 02 c3` implementation at entry zero, with the closed theorem
`EDSL.CallStack.Inline.claim`. These client proofs are packet declarations,
outside the grader's fixed foundational imports.

## Use

Build the pinned project and reconstruct a client packet:

```sh
lake build edsl-grade-call-stack edsl-proof-export tests.fixtures.CallStack.Covered
lake env .lake/build/bin/edsl-proof-export \
  tests.fixtures.CallStack.Covered EDSL.CallStack.Client.gccSame gcc-same.json
lake env .lake/build/bin/edsl-grade-call-stack 5 whole-text.bin gcc-same.json
lake env .lake/build/bin/edsl-grade-call-stack --elf 14 5 function.elf gcc-same.json
```

The byte files must be the corresponding complete extracted text and linked
ELF. `scripts/verify-call-stack.sh` builds these inputs and runs this boundary
for all four profiles. To export the alternative implementation's proof:

```sh
lake build tests.fixtures.CallStack.Inline.Accounting
lake env .lake/build/bin/edsl-proof-export \
  tests.fixtures.CallStack.Inline EDSL.CallStack.Inline.claim inline.json
lake env .lake/build/bin/edsl-grade-call-stack 0 inline.bin inline.json
```

Raw mode retains the entire input file. ELF mode selects the explicit whole
file-backed executable window beginning at `e_entry - entryOffset`; subtraction,
entry and span bounds are checked. Thus a helper before the entry remains bound
alongside the caller. The selector never scans to the first RET. The controller
checks the packet against the selected Program, then kernel-checks a wrapper
containing the complete literal file, span, entry metadata and successful pure
selection. A proof can be reused for another container with the same selected
code and entry; the wrapper establishes a new claim for that actual full file.
It does not establish safety of every other entry point or segment in the ELF.

The exporter may read compiled client modules. The grader accepts only proof
packet data and starts from fixed foundational imports and an immutable trusted
installation; client modules are not imported into its trusted snapshot.
Generic foundational decoding/footprint transport is shared by exporter and
grader; compiler bytes, executions and closed client claims remain fresh
packet declarations. The executable, project build products and pinned Lean
sysroot must be provisioned as the trusted installation. Candidate source,
module names and search paths are not grader inputs.
Fresh declarations are kernel-checked and audited, with only `propext`,
`Classical.choice` and `Quot.sound` allowed. The existing default limits remain:

| Limit | Default |
| --- | ---: |
| Proof packet bytes | 4,194,304 |
| Expression depth | 128 |
| Cumulative decoder steps | 300,000 |
| Auxiliary declaration entries and generated names | 256 each |
| Dependency-audit steps | 100,000 |
| Cumulative kernel heartbeats | 10,000,000 |

Acceptance prints one `ACCEPTED` line and exits zero. Usage errors exit 2;
unsupported admission exits 3; malformed packets exit 4; proof/audit rejection
exits 5; exhausted budgets exit 6; IO or installation failures exit 1.
Unsupported inputs, rejected proofs and exhausted budgets establish no defect.

The default `scripts/verify-call-stack.sh` gate checks the four whole nested
compiler outputs, raw/ELF grading, fresh inlined compiler outputs and owned
binding/protocol negatives. Its existing native observer covers the four nested
profiles. Inlined compiler artifacts receive proof grading; no extra native
inline observations are claimed. `--native-only` skips every formal/grading gate.
CI retains compact receipts while local runs retain full observations and packets.

## Limits

The target is the documented ordinary-RAM, four-level-canonical x86-64 profile,
with AC/CET disabled and no asynchronous interference. ELF selection requires
a window contained in one executable file-backed segment in the lower canonical
address range, with 4096-byte code-window and 65536-byte file limits. Raw input
is limited to 4096 bytes too. Successful selection establishes installed code
for any prior modeled space; loader freshness and native CPU correspondence
remain environmental obligations. The function-entry contract is not process
startup, kernel refinement or compiler source-preservation evidence. General
interprocedural analysis, richer calling conventions and OS/concurrent integration
remain unfinished. See [owned nested calls](call-stack.md) for the ISA and native
boundary, and [coverage](coverage.md) for the wider project status.
