# From checked effects to scheduler steps

The effect checker certifies sequential CPU behavior. An OS execution also
needs current resource authority, private store queues and publication into
shared RAM. `EDSL.OS.TSO64.EffectSimulation.Ordinary` connects a checked
ordinary step to the existing TSO64 scheduler without adding another
instruction interpreter.

## Current-state admission

`Effects.Trace.head`, from `EDSL.X86.VCGen.Effects.Head`, extracts evidence
about the first actual step of a checked trace: executable bytes, current
policy, decoding, the complete observation, reads and effect authorization.
Its instruction and observation are proposition indices. It does not compute
an alternative step or supply OS authority.

`EffectSimulation.OrdinaryReady` supplies separate OS gates at the current state:

- The selected worker is live and running.
- Its original code and caller leases are current.
- Guarded fetch selects an admitted instruction within its code loan.
- Every operand read passes the current OS check.
- Its actual store intent has queue admission with retained authority.

These gates describe the prestate. They contain neither a desired successor
world nor an assumption that the issue already succeeds.

`issue_from_head` combines these admissions, scheduler well-formedness and a
checked head at the worker's current `localCPU`. It constructs a successful
production issue and relates its result to the complete CPU observation.
The adapter works under either existing authority profile. The scheduler's
ordinary subset has a proved Bool-choice profile; this does not collapse
independent flag choices for other instructions in the extended ISA.

## Arithmetic, control flow and data widths

Ordinary admission reuses the existing sequential Bool-choice profile for
scalar operations and control flow. Legacy DWORD XCHG/XADD and syscalls remain
excluded. Register operations with independently chosen undefined flags, such
as the current IMUL and immediate-shift vector forms, also remain excluded;
acceptance does not replace those choices with one Bool.

Opcode admission is separate from operand authority. Current data-read gates
admit the existing aligned DWORD/QWORD profiles; a DATA1 read still fails closed.
Register-only byte operations need no data-memory authority. Every store still
uses actual prestate intent and the current queue-admission checks.

A branch grants no code authority at its destination. The next issue fetches
through the retained original code loan, even if other executable memory exists
in the world. Loops retain pending stores and their occurrence counter through
ordinary arithmetic and branches. Admission supplies no loop invariant,
termination argument or new frozen-function certificate.

## Stores, returns and publication

`ordinary_reifies` derives whole successor-CPU equality from an actual ordinary
scheduler effect. This includes registers, RIP, flags and the memory interface.

An ordinary store retains the shared world and appends its tagged DWORD or
QWORD intent to the issuing worker's FIFO. The successor CPU reconstructs RAM
through that queue. `queue_memory` proves this view equals the executor's
memory update, including overlapping mixed-width stores.

RET installs the returned context while retaining pending entries, resource
descriptors and the occurrence counter. `ordinary_ret_pending` makes that
boundary explicit. Return does not imply that the queue has drained or that
collection is permitted.

`drain_localCPU` proves that a successful own drain preserves the worker's whole
local CPU while publishing the FIFO head into the actual world. This theorem
concerns the draining worker. Publication can change memory seen by another
worker, so a resumed peer cannot assume its previous local CPU remains equal.

## Generated blocks and cutpoints

[OneStep](../EDSL/X86/VCGen/Effects/OneStep.lean) generates continuation
obligations by matching the production executor. Its head-equivalence theorem
authenticates the same complete observation using current code and decoding.
The selected flag valuations remain explicit; choosing uniform Bool values
does not cover instructions with independently undefined flags.

[Passive](../EDSL/OS/TSO64/EffectSimulation/Passive.lean) records connected native
origins and closes assertions under peer issues and every drain. Existing history
needs its own initial admission and connected trace. The saved-worker frame
preserves context, phase, resources and the store counter; shared RAM and pending
entries can change. [Resources](../EDSL/OS/TSO64/EffectSimulation/Resources.lean)
transports original worker authority and protected caller reads across origins.

[Resumable.Block](../EDSL/OS/TSO64/EffectSimulation/Resumable/Block.lean) builds
the bounded ordinary-block WP from these rules. A fixed Descriptor retains the
exact bytes, checked structural graph and original resources. Every instruction
boundary regenerates its head and resource gates at the actual resumed state.
Passive actions retain the residual node and fuel; an own issue consumes fuel.
Atomic and syscall heads remain outside this ordinary adapter.

[Resumable.Simulation](../EDSL/OS/TSO64/EffectSimulation/Resumable/Simulation.lean)
constructs the existing native-origin simulation from client cutpoint invariants
and generated block proofs. A reached cutpoint starts its next residual immediately
at that state, before another passive action. The caller supplies independent
entry/ABI facts and discharges the generated obligations; graph discovery alone
is not a functional certificate.

For caller-only bodies, the [generic sequential-proof lift](caller-only-os-proofs.md)
consumes existing bounded or cutpoint WPs and regenerates the current OS gates.
It retains the sequential proof on reference RAM while executing the actual
worker against current RAM; clients do not supply instruction-local OS proofs.

The returned-position theorem derives a historical response and its Post from
an actual returned observation. Later publication retains that response prefix
and the current returned register frame. It does not move a memory-dependent
Post to the later world. All peer, blocked and publication positions remain in
the schedule. This is conditional partial correctness and current own-issue
enabledness; whole-program termination, scheduler fairness, exact accounting
and native-RMW boundaries need additional proofs.

The identity client derives a fuel-two residual for MOV RAX,RDI; RET from an
arbitrary input word and present caller/resource admission, allowing nonempty
initial FIFOs and passive interference at both boundaries. The passive-history
regression distinguishes saved returned registers from RAM changed by later
publication and retains a blocked attempt in the original schedule positions.

## Composing real schedules

`EDSL.OS.TSO64.EffectSimulation.Lifting` supplies a generic proof fold.
A client provides a `Simulation.lift` law relating every production `Origin`
to its ghost transition and current-state relation. `Simulation.schedule`
propagates that relation along a successful actual schedule. `schedule_cut`
exposes the relation and lifted prefix at every actual cut.

Every action and observation remains present, including blocks and drains.
The law is a client proof obligation; naming a relation does not establish it.
The fold assumes a successful schedule and does not independently prove
fault freedom, fairness or termination.

After interference, a sequential certificate's tail may refer to a stale CPU.
A client must establish evidence at the actual resumed state or prove a
suitable transport law. Unchanged thread registers alone do not justify reuse.

## Instruction families and checked steps

The shared `OriginTrace`, `Pause`, `Box`, `Simulation` and `OrdinaryReady`
interfaces accept an optional RMW instruction family. The default remains
`.xaddOnly`; select `.arithmetic` explicitly for the supported locked ADD and
INC forms. Every origin in a trace uses the same selected family. Current
resource, code, caller and ordinary-read/queue checks retain their contracts.
Existing ordinary resumable blocks continue to use their original domain.

`EDSL.OS.TSO64.EffectSimulation.CheckedSimulation` is available through the
bridge import.
Its local law receives an actual successful **current step**, allowing a client
to retain details such as the selected atomic handle. An arbitrary
`Origin.rmw` records a granted handle and its effect, but does not record the
executor's first matching handle selection; there is no converse from an origin
to an executable step.

`CheckedSimulation.schedule` and `schedule_cut` retain every action and
observation in `LiftTrace`. `Simulation.toChecked` converts an existing
origin-based law using the forward step-to-origin theorem. These folds do not
establish enabledness or completion. [Mixed instruction resumption](mixed-resumption.md)
adds generated ordinary/RMW block obligations, present own-issue enabledness
and an adapter for complete histories. Counted-loop contracts and eventual
completion remain separate work.

## Scope

These adapters retain the current scheduler's instruction support, authority
profiles and resource model. They add no opcodes, lifecycle transitions or lock
protocol. Sequential DWORD atomic events are not converted into the scheduler's
full64 RMW events.

Concrete program contracts, lock transfer, queued release and liveness require
client invariants and protocol proofs. Source/compiler preservation and physical CPU/OS
correspondence remain separate obligations.
