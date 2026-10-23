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

## Scope

These adapters retain the current scheduler's instruction support, authority
profiles and resource model. They add no opcodes, lifecycle transitions or lock
protocol. Sequential DWORD atomic events are not converted into the scheduler's
full64 RMW events.

Whole-program safety under interference, lock transfer, queued release,
unbounded loops and conditional progress require additional protocol and
simulation proofs. Source/compiler preservation and physical CPU/OS
correspondence remain separate obligations.
