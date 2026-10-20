# Uninterrupted atomic set proof grading

`EDSL.Grading.AtomicSet64` accepts literal machine code and serialized Lean
proofs for independently chosen full64 intersection, union or symmetric
difference. Its strict instruction model decodes locked AND/OR/XOR on
`qword [RDI], RSI` and RET. A requested mathematical operation does not choose
the decoded instructions or restrict initial admission.

## Contract and resources

`Claim desired bytes` combines universal `SemanticClaim` with a useful
nonvacuous resource witness. Admission is the existing `AtomicSet64.Pre`:
current typed actor/handle authority, well-formed registered resources, full
CPU/OS RAM equality, named code/caller loans, actual literal code and caller
slot, and the locked profile's canonical/alignment/ABI conditions. It does not
assume future decoding, successful execution, a particular operation, or any
instruction/event count. The existing arbitrary-byte constructor supplies
useful witnesses for each desired task and every nonempty span of at most
4096 bytes, including unsupported and RET-only windows.

`Frame`, `Current` and `Preservation` reuse the operation-neutral OR resource
infrastructure. `FetchWithin` uses the actual generic decode and requires each
complete encoding to fit in the original selected extent, including RET.
`Step` couples each real CPU RMW to its checked current OS `logicalUpdate`.
The actual operation is recovered from the instruction/event; it is independent
of the requested task. RET retains the current world and reads the original
caller slot. There are no administrative history-hop rules.

Every admitted initial state and every AF stream must have a returning
`CoveredExecution` satisfying independent natural-bit membership, actual
initial/final RAM reads, original caller return and RSP+8, the SysV saved
register frame, nonarithmetic flags, outside-target bytes/permissions and exact
surviving resource registries/frontiers/loans. The returned world belongs to
that same actual execution. Prefix, operand-access and terminal-origin theorems
retain current authority and complete selected-window fetch coverage.
`logicalTrace`, `chain` and `readback` derive the complete ordered modification
history from actual events, retaining unchanged updates and their tags.

## Implementations, costs and concurrency boundary

Client proofs live in `tests.fixtures.AtomicSet64Grading`, outside the trusted
foundation. Single AND/OR/XOR, repeated AND/OR, triple XOR and mixed XOR/XOR/OR
solve their independent set tasks. All actual events remain visible. In the
mixed union implementation the first two XORs cancel for an uninterrupted call;
the third operation supplies independent union membership. A checker that
requires every instruction to match the desired operation would reject this
valid implementation.

`Returned.event_required` and `Returned.useful_lower_bound` separately prove
at least one actual RMW and two retired modeled instructions for a useful
input. They impose no acceptance restriction. These costs concern the strict
locked-set/RET model; they are not global x86, micro-op, latency or source-level
optima.

The task establishes **uninterrupted callable results**. Several RMWs with a
correct standalone final value need a separate interference/linearizability
proof before they implement one abstract concurrent method. Actual event
histories are retained for that later work. The existing OR-only managed
scheduler and grader keep their own contracts.

## Data-only controller

```sh
lake build edsl-grade-atomic-set64 edsl-proof-export
lake env .lake/build/bin/edsl-grade-atomic-set64 intersection function.bin proof.json
lake env .lake/build/bin/edsl-grade-atomic-set64 union --elf 13 function.elf proof.json
bash scripts/verify-atomic-set64-grading.sh
```

Canonical task names are `intersection`, `union` and `symmetricDifference`.
The packet proves `Grading.AtomicSet64.Claim desired selectedCode`; the controller
selects the independent expected proposition and kernel-checks a new
`Artifact.Claim desired literalArtifact` wrapper. Whole literal raw/full-ELF
inputs, entry, selected span and file backing are bound by the wrapper. Symbols
and sections are not selection authority. Nonloaded metadata may change while
the code proof remains applicable, but each file receives its own checked wrapper.

Raw spans are bounded at 4096 bytes; complete ELF files at 65536 bytes. The
explicit ELF span selects a file-backed executable entry window. Every executed
instruction fits within that window; unrelated executable regions and process
startup are outside the claim. This reuses the grading loader rather than the
one-operation convenience certifier's stricter complete-segment format.

The fixed installed environment includes contracts/domains and excludes client
implementations/helpers/submission modules. Auxiliary declarations travel as
checked proof data. Both packet and artifact wrapper use the same unchanged
limits, including kernel depth512 and cumulative checking ceiling. No wrapper
budget override or unchecked solver result is used. Exporting a theorem is a
separate client operation and does not establish successful grading.

Exit statuses are 2 usage, 3 artifact admission, 4 malformed packet, 5 proof or
audit rejection, 6 resource limits and 1 internal/IO failure. Only `ACCEPTED`
reports successful checking; rejection, timeout and unsupported code establish
no program defect. CLI IO and immutable trusted installation remain external
trust boundaries.

## Evidence and limits

The verifier compiles seven owned GNU23 inputs using GCC13 and Clang18. Fresh
helper-dependent reference/body packets grade complete raw/full-ELF inputs while
client/helper source and objects are outside their import locations. It checks
crossed tasks/bytes/proofs, truncated spans, malformed/bounded inputs, permitted
metadata changes, unknown client references and poisoned search paths. Tests
also connect useful unsupported/RET-only inputs, double-XOR refutation, current
mixed-prefix RAM and selected-window truncation to actual semantics. Audits and
fresh kernel replay use the pinned Lean toolchain.

Separate C observers compare ELF-entry bytes, the extracted raw span and the
exact loaded executable slot before calling the code. Finite observations
check independent per-bit set results and neighboring RAM, with wrong-task
negative controls. They do not measure events or establish physical/model
correspondence, flag/ABI correctness or concurrent behavior. Commands, statuses,
source snapshots and manifests remain available on incomplete runs as well.

The locked profile's ordinary coherent WB RAM, stable translation/code/private
context, supported controls/CET state, alias/layout and native atomic-object
representation/lifetime assumptions remain external. General source memory
orders, TSO64, generic managed peer scheduling, whole-process/whole-OS safety and
physical CPU/kernel refinement remain subsequent work.
