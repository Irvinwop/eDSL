# Independent flag choices

Some x86 instructions leave several status flags undefined. A verifier must
admit every permitted combination: assigning all undefined bits the same
Boolean would omit executions. The shared execution engine now accepts an
arbitrary `ChoiceStream Choice`, with one fresh element per retired instruction.
Returning executions record the complete final state, exact instruction count
and ordered operand reads. Continuing blocks and fault-prefix relations record
their finite costs and reads; divergence uses indexed continuing states and
per-step read witnesses. A failed bounded run returns only `Error`.

## Available interfaces

[`FlagChoices`](../EDSL/X86/Sequential/FlagChoices.lean) contains independent
CF, PF, AF, ZF, SF and OF components. `representatives active` enumerates the
combinations of a declared active list. Its coverage theorem proves that every
valuation agrees with a representative on those bits. A list of four distinct
flags has sixteen representatives; inactive bits need not be enumerated.

`FlagChoices.check_eq_true_iff` equates finite checking with universal
quantification only when the client proves `Invariant active predicate`.
This premise prevents a checker from discarding a flag its actual predicate
observes. Duplicate active entries are accepted and can repeat representatives.

[`MachineChoices`](../EDSL/X86/Sequential/MachineChoices.lean) provides
`executeWith` and `stepWith` for the existing instruction profile. Selection
uses the actual instruction and prestate: AF for logical instructions and
SHR-by-one, OF for a rotate count greater than one, and no choice for instructions
whose flags are defined. `stepWith` decodes current executable memory and
preserves all errors and checked operand reads.

[`ExecutionChoices`](../EDSL/X86/Sequential/ExecutionChoices.lean) specializes
the generic engine as `runWith`, `ExecutesWith`, `BlockWith` and
`AllExecutionsWith`. Existing `execute`, `step`, `Choices`, `run` and VCG APIs
retain their Bool signatures. Two-way simulation proves equality of possible
finite outcomes, including faults, exhaustion, final memory and permissions,
flags, costs and reads. Uniformly bounded existing total-correctness proofs
transfer with `allExecutionsWith_of_allExecutions`; they do not need a separate
per-program execution proof for this adapter.

## Support boundary

The vector adapter currently supports exactly the existing opcode profile.
It does **not** add IMUL or extend the Bool VCG to multi-flag instructions.
The generic simulation library proves finite behavior transfer and does not
silently infer unbounded termination from a fixed-fuel observation.

[`WordMath.Multiplication`](../EDSL/WordMath/Multiplication.lean) separately
proves multiplication modulo the word size against unbounded natural arithmetic,
uniqueness, and signed overflow against integer bounds. These facts have no
machine or OS assumptions. They are groundwork for instruction support, not
certificates for an additional corpus entry. Published coverage is unchanged.

A decoded XOR/rotate/RET regression exercises independent AF and OF selection
across instruction boundaries, with literal expected flags, the actual return
stack read, and exact instruction cost. Production proofs and regressions are
included in the axiom audit and fresh-replay targets.
