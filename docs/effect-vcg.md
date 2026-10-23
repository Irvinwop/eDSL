# Bounded verification with memory effects

`EDSL.X86.VCGen.Effects` verifies bounded x86-64 executions using the production
vector executor. It supports ordinary DWORD/QWORD stores and legacy DWORD
XCHG/XADD observations, retaining exact ordered atomic events. Clients
supply bytes, a graph, an initial state and entry node, fuel, a policy and an
independent result/event contract. Execution and soundness are shared across
programs. Graphs can come from [structural discovery](structural-cfg.md).

## Policy and code separation

`Effects.Policy` separates three predicates:

- `Current` holds in every actual instruction prestate and the returned state.
- `AllowedRead` authorizes each actual operand read in its prestate.
- `AllowedEffect` authorizes the decoded instruction and its complete actual
  observation. Same-value writes still have write intent.

The generic soundness APIs require `Effects.CodeFrame policy bytes base`,
separately from the generated formula. It preserves the selected executable bytes
through every allowed ordinary or atomic continuation, so decoding uses actual
successor memory at each step. It permits data memory to change.

`EDSL.X86.VCGen.Effects.Frames` supplies `CodeSeparated`, `codeSeparatedPolicy`
and `codeSeparatedPolicy_codeFrame`. The policy admits `CFG.readOnly`
instructions, ordinary stores with actual DWORD/QWORD prestate intents disjoint
from the selected code, and the legacy DWORD XCHG/XADD forms with disjoint RDI
footprints. The shared frame theorem derives code preservation from successful
production execution and memory frame laws.

`EDSL.X86.VCGen.Effects.SeparationCheck` supplies `checkCodeFootprint`,
`checkCodeSeparated` and `decidableCodeSeparated`. The footprint check uses exact
modular byte-address differences; its DWORD/QWORD equivalences include wrapping
and empty windows. `checkCodeSeparated_iff` proves equivalence to `CodeSeparated`.
Authorization uses write intent even when the stored value leaves memory equal.
Separation supplies no writability or OS authority; execution still checks
permissions. Executable admission separately requires an actual `CodeAt` window.

## Finite WP checking

`Effects.wp graph base policy fuel node initial Post` quantifies over every
complete flag valuation and evaluates `Sequential.executeWith`. Each continuation
requires a graph edge, the actual successor RIP and the residual formula. Returns
satisfy `Post : Result → List AtomicEvent → Prop`. Errors, zero fuel, missing
successors and syscalls fail closed.

`EDSL.X86.VCGen.Effects.Reflection` supplies the reusable `Effects.decidableWP`.
Clients pass explicit decisions for `Current`, `AllowedRead`, `AllowedEffect`
and `Post`. Fuel recursion checks finite graph successors and enumerates the
instruction's active undefined-flag representatives. Equality of the entire
executor observation justifies omitting inactive choices, including reads,
successor states, atomic payloads and errors. Independent active flags retain
all combinations.

With that decision installed, `Effects.check` returns a Boolean and `check_iff`
equates acceptance with the existing WP. It checks dynamic obligations only.
`checked_run_sound` additionally requires `CFG.Structural.Valid`, initial
`CodeAt`, the selected node's RIP and `CodeFrame`. For every flag-choice stream it
gives an actual `runWith`, the independent contract, an instruction bound and
`Effects.Trace`. The result retains ordered reads; the trace certifies atomic
event order and multiplicity separately from the engine's returned `Result`.
`checked_sound`, `checked_all_executions` and `checked_safe` expose execution and
sequential prefix-safety results under the same premises.

## Combined certificate

Import `EDSL.X86.VCGen.Effects.Checked` for `Effects.certifySeparatedWith` and
the default-profile `Effects.certifySeparated`. Callers supply `Current`,
`AllowedRead`, `Post` and their explicit decisions. `decidableSeparatedWP`
builds the WP decision using `decidableCodeSeparated` for effects.

Combined acceptance checks all four obligations on the supplied inputs:

1. `CFG.Structural.checkWith profile bytes graph` authenticates the graph.
2. `ELF.checkCode initial.memory base bytes` checks actual executable bytes.
3. The initial RIP equals `base + BitVec.ofNat 64 (graph.node node).offset`.
4. `Effects.check` accepts the WP under `codeSeparatedPolicy`.

`certifySeparatedWith_sound` and `certifySeparated_sound` derive the actual
production run, contract, instruction bound and ordered trace for every choice
stream. Code mapping and entry RIP follow from the checks; the shared separation
adapter supplies the frame. Clients need no separate `CodeAt` or code-frame
proof. The default static caps are 64 bytes and 32 nodes; larger windows require
an explicit profile. Dynamic fuel remains a separate bound.

[`tests/EffectReflection.lean`](../tests/EffectReflection.lean) checks literal
store/load results, atomic event order, denied reads and final-state predicates,
same-value writes, executable overlap, footprint boundaries and independent
PF/ZF choices. [`tests/EffectChecked.lean`](../tests/EffectChecked.lean) connects
combined acceptance to a production run and rejects changed executable text and
a wrong entry RIP even where the raw WP accepts the proposed instructions.

## Connecting an ordinary step to the scheduler

Import `EDSL.OS.TSO64.EffectSimulation` for the
[ordinary scheduler bridge](effect-scheduler-bridge.md). `Effects.Trace.head`
extracts the first actual checked step. `EffectSimulation.OrdinaryReady` supplies
the separate current prestate OS gates; `issue_from_head` derives a successful
production issue and whole successor-CPU equality. Ordinary stores retain their
actual DWORD/QWORD FIFO intent. RET retains pending stores, and a successful own
drain preserves the issuing worker's local CPU while publishing to shared RAM.
Peer publication may change a resumed worker's memory, so an old sequential
trace alone does not justify its next issue.

`EffectSimulation.Simulation.schedule` and `schedule_cut` transport a client
relation through successful actual schedules, retaining blocks and drains. The
client must prove a universal lift law for the production origins; the successful
schedule premise does not establish fault freedom, fairness or termination.
The bridge extends neither the scheduler's opcodes nor its authority profiles
and does not convert sequential DWORD atomic events into full64 RMW events.

These APIs establish conditional model behavior. The separation policy protects
only the selected code; caller-slot ownership and other resource frames need
additional obligations. A CPU predicate closed over an initial OS world does
not establish coherent current-world or ownership/epoch evolution after writes.
Lock transfer, linearizability and whole-program interference invariants remain
client or future protocol proofs. Cutpoints provide no unbounded-loop rule here.
Physical CPU/OS correspondence and source/compiler preservation remain separate
refinement obligations. Rejection or exhausted fuel does not establish a
program defect.
