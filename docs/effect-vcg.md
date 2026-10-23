# Bounded verification with memory effects

`EDSL.X86.VCGen.Effects` generates bounded conditions over the production vector
executor for a structurally checked x86-64 graph. It supports ordinary successor
states and the existing legacy DWORD XCHG/XADD observations, retaining the exact
ordered atomic events. Its soundness theorem is shared across programs.

A new program supplies its bytes and graph, an independent result/event contract,
an initial executable mapping and entry PC, a policy, and a proof of the generated
formula. It supplies no new instruction interpreter. This is a library API;
automatic structural graph discovery, a generic Boolean decision procedure,
packet-grader integration and loop-cutpoint rules for this effectful API remain
future work. Existing read-only discovery, reflection and packet APIs keep their
current admission policy.

## Policy and framing

`Effects.Policy` separates three predicates:

- `Current` states what must hold in each actual instruction prestate and at
  return.
- `AllowedRead` authorizes each actual operand read in its current prestate.
- `AllowedEffect` authorizes the decoded instruction and complete actual
  observation. Same-value writes still have write intent.

Every soundness entry point requires `Effects.CodeFrame policy bytes base`.
This proof carries the initial executable bytes through every allowed ordinary
or atomic continuation. It is separate from the generated formula and supplies
no whole-memory equality. The next instruction is authenticated against the
actual successor memory, after applying this frame.

Import `EDSL.X86.VCGen.Effects.Frames` for a reusable frame:

```lean
import EDSL.X86.VCGen.Effects.Frames

#check EDSL.X86.VCGen.Effects.CodeSeparated
#check EDSL.X86.VCGen.Effects.codeSeparatedPolicy
#check EDSL.X86.VCGen.Effects.codeSeparatedPolicy_codeFrame
```

`CodeSeparated` admits the read-only instruction family, ordinary stores with
actual DWORD/QWORD prestate intents and footprints disjoint from the selected
code, or the supported legacy DWORD atomic forms with the same separation.
It authorizes writes independently of final-memory equality. The adapter derives
code preservation from successful production execution and the existing memory
frame laws; clients do not repeat opcode cases for each new program.

The adapter protects the selected executable window. Caller-slot separation,
current ownership and epochs, other memory regions and resource transitions need
additional policy and proof obligations. A CPU predicate closed over an initial
OS world does not establish coherent resource evolution after writes.

## Conditions and results

`Effects.wp graph base policy fuel node initial Post` quantifies over every
complete flag valuation and reduces `Sequential.executeWith`. Each continuing
step requires a graph edge, its actual successor RIP and the residual formula.
Returns satisfy `Post : Result → List AtomicEvent → Prop`. Errors, zero fuel,
missing successors and syscalls fail closed.

`Effects.sound` yields actual `ExecutesWith`, the independent postcondition,
an instruction bound and `Effects.Trace`. The trace has production ret/next/atomic
steps with current executable bytes, decoding and read/effect authorization.
Its atomic constructor prepends the actual event, preserving order and
multiplicity. `Effects.run_sound` reuses the existing engine's evaluator theorem.
The evaluator still returns its existing `Result`; the separate trace certifies
the event list. `Effects.all_executions` and `Effects.safe` provide the corresponding
universal returning-execution and sequential prefix-safety results.

## Worked regressions

[`tests/EffectVCGen.lean`](../tests/EffectVCGen.lean) demonstrates the shared API:

- Store/load/RET proves literal little-endian data, RAX, the original stack
  return, three retired instructions, ordered reads and no atomic events.
- XCHG/XADD/RET proves the final word and the two literal old/new events in their
  actual order. A reversed-event contract is rejected through the real trace.
- An actual same-value store leaves complete memory equal but is rejected by
  a separately chosen policy that forbids writes.
- An allowed physical store overlapping the executable RET changes the byte;
  the separation policy and generated conditions reject that footprint.

The fixtures use `Current := True` and impose no logical OS authority. They
establish bounded sequential model behavior, without adding corpus coverage.
The tests belong to `CFGProfileTests` and the full corpus fresh target.

This sequential atomic trace is not a concurrent scheduler history. TSO buffers,
delayed publication, current OS authority, lock transfer, fairness and
linearizability require an explicit bridge to the concurrent models. Physical
CPU/OS correspondence and source/compiler preservation remain separate target
refinement obligations.
