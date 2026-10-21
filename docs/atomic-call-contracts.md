# Atomic calls, finite publication and order weakening

Three reusable interfaces help separate a callable atomic operation's contract
from its execution, later publication and memory-order proof. They are building
blocks for method adapters; they do not yet certify additional corpus functions.

## Declare the intended operation

`EDSL.Concurrency.AtomicCalls` defines acquire-load, release-store and ordered
RMW requests. A store request fixes its value and has a unit reply. Loads and
RMWs return a value; an RMW request fixes the intended update function before
that reply is known. Matching observed before/after values alone cannot choose
the specification afterward.

Each completed call records its logical thread, occurrence, request, reply and
invocation/access/return positions. `Realizes` relates the calls to a supplied
atomic graph: initialized-boundary events followed by exactly one event per
call, in access order. It requires distinct call keys, valid intervals and
nonoverlapping calls on each thread. `History` additionally requires the
existing C23 atomic-fragment legality predicate.

These are independent postconditions. A machine adapter must derive the calls,
positions, replies and complete event correspondence from actual execution.
This module does not supply that adapter. `History.read_source` retains the
selected writer identity; `Realizes.direct_synchronizes` requires a qualifying
release/acquire RF edge. Equal values or an earlier return do not establish it.

A buffered store may return before publication. Its source event belongs to
the call; its modification rank may be determined by a later drain. The call
contract does not require publication inside the invocation/return interval.
The shared [RET rules](managed-vc-rules.md) provide actual response and caller
facts for future adapters.
The [load/store method family](managed-plain-methods.md) adds body progress,
interference closure, indexed access/RET origins and complete finite call-cohort
extraction. Constructing `AtomicCalls.History` still requires complete graph
correspondence and operational legality; its machine adapter currently covers
one invocation per initial worker slot.

## Close the current store queues

`EDSL.OS.TSO64.DrainClosure` constructs a finite drain schedule from the actual
worker queues. `drainAll` runs the production scheduler on that schedule and
preserves its exact fault behavior. `drainAll_complete` proves success from
current `WellFormed` authority alone, without a future-success premise.

The certificate proves final quiescence, one drain action and observation per
initial pending entry, and zero retired user instructions. Every worker retains
its complete context, resources, phase and store counter; only its queue clears.
The world metadata frame permits the actual published memory changes. Both
profiles are covered: `sharedCell` permits valid mixed ordinary/managed queues,
while `ownedOnly` retains its existing ordinary-only policy.

```lean
import EDSL.OS.TSO64.DrainClosure
import EDSL.Concurrency.C23Atomic.Weakening
open EDSL

example {state : OS.TSO64.State} {profile : OS.TSO64.Profile}
    (valid : OS.TSO64.WellFormed state profile) :
    ∃ result, OS.TSO64.DrainClosure.drainAll state profile = .ok result ∧
      OS.TSO64.Quiescent result.1 := by
  obtain ⟨result, executed, certificate⟩ :=
    OS.TSO64.DrainClosure.drainAll_complete valid
  exact ⟨result, executed, certificate.quiescent⟩

example {strong weak : Concurrency.C23Atomic.Candidate Nat Nat}
    (legal : Concurrency.C23Atomic.Legal strong)
    (labels : Concurrency.C23Atomic.Candidate.Weakens strong weak) :
    Concurrency.C23Atomic.Legal weak := legal.weaken labels
```

An arbitrary initial valid queue is a provenance boundary. The closure does not
invent instruction origins or unique occurrence tags for it. Given a successful
earlier execution, the prefix theorems retain its existing boundary-or-issue
origins; an empty original queue boundary gives actual issue witnesses. This
constructs one finite schedule. Fairness, completion of running code and eventual
publication along other schedules are separate obligations.

## Reuse a stronger memory-order proof

`EDSL.Concurrency.C23Atomic.Weakening` proves `Legal.weaken` for the same finite
graph with acquire/release flags removed. It preserves access kinds, values,
live and absent event indices, objects, threads, RF selections and modification
ranks. Either flag on an RMW can be removed independently.

The relation assumes neither legality nor happens-before inclusion. Its proof
derives weaker synchronization and happens-before, then transports all existing
well-formedness, coherence, acyclicity, no-future-RF and RMW-predecessor clauses.
It cannot add flags, change a selected writer or establish a stronger execution
from a relaxed one. Establishing operational legality at stronger labels remains
a separate proof obligation.

All three APIs retain their underlying modeled resource and platform
assumptions. They establish no universal machine-to-C23 preservation, source or
compiler preservation, native CPU/Linux correspondence, general liveness or
whole-kernel result. See [checked finite traces](checked-atomic-traces.md) for
the separate checker-based admission API.
