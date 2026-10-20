# Managed mixed-operation workers

`EDSL.OS.AtomicSetThreads64` models finite bodies of strict full64 locked
AND/OR/XOR on `[RDI], RSI`, followed by one RET. Bodies, masks and registered
cells may differ between workers. Each selection executes one actual instruction
against the current shared RAM and retains its AF choice and optional event. RET occupies
an observation position and emits no RMW event. RET-only bodies are supported.

This is a checked managed machine/OS model. Native kernel thread creation,
source memory orders, physical LOCK refinement and whole-OS safety require
separate correspondence proofs. The existing OR-only scheduler and atomic
graders retain their separate contracts.

## Current authority and lifetime

`Layout` recognizes exactly zero or more `f0 48 {21,09,31} 37` encodings and
one terminal `c3`. Checker soundness/completeness and current `CodeAt` bind
every complete fetch to the original literal extent. Alternate encodings,
truncation and trailing bytes are refused.

`SpawnReady` describes present root-owned cell authority, code/stack tickets,
valid readable regions, both reservation scans, current literal bytes and
the original caller read. Canonical return, strict stack nonwrap and canonical
post-RET RSP are explicit checked conditions. It assumes no future borrow,
issuance, dispatch or final result. Availability remains an explicit spawn
choice. Failed functional transactions expose no partial handle or loan.

A worker retains immutable entry/body/resource identities, private context,
cursor and captured event list. Its handle and code/stack loans remain live
through completion. Each RMW uses the actual decoded operation and current
authority; CPU/OS coupling exposes full RAM, operand footprint, flags, registers
and original-byte coverage. Peer dispatch preserves the worker's private record
while updating shared RAM. RET reads the retained original caller slot, advances
RSP once and keeps the entire current shared world.

Join closes precisely that handle and its two loans, returns the completed
private context, and preserves current RAM and peer resources. It can collect
one worker while another remains unfinished. The cell's allocation reservation
persists until explicit retirement after every handle closes. Checked managed
histories preserve revocation through monotone thread, handle and loan IDs.
Generic updates project through their actual checked borrowing stores;
AND/XOR are never relabeled as old OR-only history steps.

## Finite schedules and independent results

`Legal state selections` requires only present worker membership and each
selection count to fit that worker's remaining rank. Running rank counts its
remaining logical instructions plus RET; completed rank is zero. Rank
conservation proves this admission condition both necessary and sufficient
for a successful finite schedule from a well-formed state, for every supplied
AF list. A legal prefix need not finish a worker. No fairness or future-success
premise is hidden in admission.

The cohort construction enumerates current worker IDs, selects each remaining
instruction and collects all completed workers. It retains observation
positions and collection records, leaves no live cohort workers, and preserves
current post-schedule RAM through collection. Finite construction provides no
infinite fairness or parent-collection guarantee.

`Logical64.OrderedMathematicalResult` independently specifies one natural-bit
set operation at each ordered intermediate word. The adapter from actual event
tags is outside that mathematical contract. Actual chains/current readback
establish the relation, including no-change updates and cancelling XOR pairs.
Mixed operation order can change the answer. Homogeneous union/intersection/
parity conclusions need their explicit uniform-tag premises.

Dispatch-only fixed-cell epochs admit a genuine lower `LogicalTrace`.
`FixedCellEpoch` also handles actual spawn/join/mutate/retire positions: the same
registered cell remains live at every intermediate state, every emitted event
selects it, and administrative reads stutter by checked resource frames.
Administrative metadata changes are not erased into a fabricated lower trace
with the same endpoints. Projection past another cell's RMW or across target
retirement/re-enrollment is outside this value theorem.

Stored audit prefixes and actual observations are distinguished. Arbitrary
`WellFormed` alone does not authenticate an unobserved past. Exact accounting
proves `final.events = initial.events ++ ownObservedEvents`; instruction-origin
theorems bind the new suffix to real selected CPU/OS transitions. An entirely
authenticated list additionally needs checked spawn with its empty prefix or
separate evidence for the earlier prefix. Cohort records retain that distinction.
A captured event's after-word need not remain current after a peer writes.

## Evidence and limits

The domain constructor performs checked allocation, initialization, executable
image installation, adoption, enrollment and spawn for arbitrary full64 inputs
and every supported finite body within its explicit 4096-byte loader capacity.
The general scheduler instead depends on valid extents and has no such witness
capacity restriction. Zero/equal operands and empty logical bodies remain
covered. Supported-body readiness is distinct from the arbitrary-byte admission
of the [uninterrupted proof grader](atomic-set64-grading.md).

`Programs.arbitrary_body_execution` connects that checked setup and spawn to
production scheduling, the actual RET, checked join, current full64 readback and
an independent ordered result for the supplied body's requests. It covers all
old words, masks, caller registers/flags and AF lists of the required length.
`BodyExecution` retains exact instruction/event counts, CPU return evidence,
ABI frames and resource revocation. Separate corollaries cover RET-only bodies
and uninterrupted OR/XOR/XOR union without erasing either XOR occurrence.

Independent regressions use actual setup/spawn/schedule/RET/join paths, literal
full64 event and byte results, all GPRs, flags and neighboring memory. They check
noncommuting orders, unchanged RMWs, peers before RET and after completion,
collection during unfinished peer execution, failed second-borrow retries,
resource pinning and explicit retirement. Adversarial tests reject complete-code
window truncation despite executable adjacent bytes, unsupported aliases,
current permission/epoch changes and caller-boundary faults. Hostile raw-state
injections are explicitly outside the managed well-formed history.

The owned synthetic OR/XOR/XOR body solves union uninterrupted. A peer OR
between its XORs can change the global result to zero even though no ordering
of two abstract union calls yields zero. The model retains that actual history;
uninterrupted acceptance supplies no compound-call linearizability theorem.

Instruction counts concern successful selected instructions in this strict
profile. Spawn/join/idle are administrative actions. These results establish
no global x86 optimum, micro-op bound, latency or operating-system cost. Physical
interpretation retains the locked profile's coherent ordinary WB RAM, stable
translations/permissions/private context, supported controls/CET and alias,
layout and atomic-object lifetime assumptions.

Build and run the focused Lean checks with the pinned toolchain:

```sh
lake build EDSL.OS.AtomicSetThreads64 EDSL.Audit
lake env lean -DwarningAsError=true tests/Logical64Ordered.lean
lake env lean -DwarningAsError=true tests/AtomicSetThreads64.lean
lake env lean -DwarningAsError=true tests/AtomicSetThreads64Adversarial.lean
```

The main Lean workflow also audits transitive theorem dependencies and replays
the library through a fresh kernel environment. Native observations are separate
from these scheduler theorems; this increment adds no native kernel refinement.
