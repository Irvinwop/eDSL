# Managed store identities

The managed scheduler records a buffered store's full authority descriptor,
value and per-thread occurrence at issue time. A drain publishes that existing
entry. Issue and publication are separate events, and their positions in the
schedule can differ.

Import `EDSL.OS.TSO64.C23Projection.Origins` for the execution facts needed to
relate those positions. They use the existing scheduler and checked queue
operations. They do not introduce a second executor or assign source memory
orders to machine instructions.

## Issue identity

`StoreHistory.IssuedAt profile tid entry index initial actions result` retains
an actual successful store issue at action position `index`. Positions include
every action, including blocked attempts and drains. `prestate` exposes the
successful prefix, selected action, successful step and original admission.
`IssuedIn.indexed` adds an exact position to an existing existential history;
`IssuedAt.lift_prefix` retains it in a complete successful schedule.

Each successful ordinary store increments its worker's `nextStore` counter.
Other successful actions preserve or increase that counter. A drain does not
reset it when the FIFO becomes empty. The counter counts all ordinary store
issues, including stores through ordinary ownership, so managed occurrences
can have gaps.

`IssuedAt.managed_identity_unique` proves that `(tid, occurrence)` identifies
one issue position and one complete managed entry within an actual schedule.
The theorem does not require matching values or current FIFO membership.
It continues to apply after publication has removed the entry. Occurrence
numbers alone are not global identities: two workers may each issue occurrence
zero. Worker indices are the scheduler's fixed slots, distinct from resource
actor labels.

These counter and issue-position facts need neither an empty initial queue nor
an assumed queue-order invariant. They establish uniqueness among actual issues
in the supplied run. They do not invent origins for arbitrary initial entries.

## Publication correspondence

`C23Projection.buffered_issue_unique` connects an actual `PublishedHistory.WriteAt`
buffered stamp to its unique earlier `IssuedAt` position in the same successful
schedule. It requires an empty initial FIFO boundary, which excludes stores
issued before the run. The stamp still retains its publication position; it is
not replaced by the earlier issue position.

In the other direction, `IssuedIn.pending_or_published` proves that every actual
issued entry remains pending at the end or occurs in a real drain observation.
`C23Projection.issued_is_published` removes the pending alternative when the
final queues are empty. A returned worker can still have pending stores, so
return alone is insufficient.

The current forward theorem establishes that a publication exists. A theorem
that drain positions are unique, an executable source-graph extractor and
source modification-order correspondence remain separate work. Source acquire
and release annotations must come from an explicit verified interface: MOV
bytes alone do not distinguish relaxed accesses from acquire/release accesses.

## Validation and scope

The [regression](../tests/TSO64StoreIdentities.lean) executes actual decoded
same-value stores with a drain between issues, peer interleaving and return
before the final drain. It checks that emptying a FIFO does not recycle IDs,
that separate workers retain separate identities and that neighboring memory
is preserved. The generic theorems quantify over successful scheduler steps
and schedules rather than only this fixture.

These are execution-origin facts for the existing fixed-world profiles and
their explicit authority and architectural assumptions. They do not establish
C23 legality, source/compiler preservation, physical CPU or Linux behavior,
publication exactly once, fairness or liveness. They add no frozen compiler
function certification.
