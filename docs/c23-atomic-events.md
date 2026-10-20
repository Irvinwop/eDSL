# C23 atomic event graphs

`Concurrency.C23Atomic` supplies a shared contract vocabulary for atomic reads,
writes, read-modify-write operations and release/acquire synchronization.
Import `EDSL.Concurrency.C23Atomic`.

This is an atomic-only event-graph fragment based on the C23 working draft
[N3096, §5.1.2.4 and §7.17.3](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf).
It is separate from the [machine-level TSO projection](word-tso-refinement.md).
There is no theorem yet connecting arbitrary machine schedules to these source
constraints, and this layer certifies no additional frozen compiler functions.

## Events and independent relations

An event records its object, thread and typed access. Loads admit relaxed or
acquire order; stores admit relaxed or release order; RMWs also admit combined
acquire/release order. An RMW has one identity with both an observed value and a
written value. Initialization is a synthetic boundary write without a thread. The represented
objects have already been validly initialized before the modeled interval;
object identities and lifetimes remain stable, and thread identifiers name
distinct thread instances. These events do not execute `atomic_init`, thread
creation or join. External synchronization and initialization-to-thread HB
require a separately justified boundary; they are not inferred from list order.
The object and value types are parameters, so the graph rules do not depend on
an OS resource representation or a particular word width.

A finite event list assigns identities. Its order supplies sequencing within
each thread; it does not impose a global source modification order. Explicit
reader-to-writer indices identify read-from edges. Numeric ranks order actual
writes to each object, with unique ranks within an object. Different objects
have independent orders; rank gaps are allowed.

Matching bits validate a selected read-from edge. They cannot identify its
writer: two equal-valued writes remain different events.

## Release sequences and synchronization

A release heads a contiguous prefix of its object's modification order. Each
subsequent member must be a write by the head's thread or an atomic RMW by any
thread. This is the C23 rule. A foreign plain write breaks the sequence, and a
later RMW cannot rejoin the sequence across that write. Membership checks every
actual intervening modification, including unchanged-value writes.

An acquire synchronizes with a release only when its explicit read-from edge
selects a member of that release's sequence. Initial reads and relaxed reads
establish no such synchronization by themselves. Happens-before is the
transitive closure of sequencing and these qualifying synchronization edges.
The API applies the atomic rule without an additional thread-inequality filter;
raw candidates still need all coherence and RMW-predecessor obligations.

## Consistency and reusable proof rules

Structural `WellFormed` validates event/thread kinds, initial writes,
per-object rank uniqueness and actual read-from sources. `Legal` additionally
requires:

- Acyclic happens-before, with no read from a modification ordered after that
  read by happens-before.
- Write-write, read-read, read-write and write-read coherence.
- An RMW read from its immediate predecessor in the object's modification order.

A structurally valid graph alone establishes none of those additional facts.
Clients prove consistency for their actual event graph; no unchecked solver or
caller-supplied relation is treated as an established theorem.

`publication_chain` composes a prior payload write, a release-sequence source,
a qualifying acquire and subsequent payload access. `Legal.message_passing_not_older`
then rules out a payload read from an older modification. With no later payload
write, `Legal.message_passing_value` identifies the actual payload value.
These rules are independent of the instruction sequence and event numbering.
An optional timestamp certificate proves acyclicity from strictly increasing
sequencing and synchronization edges.

## Scope and remaining obligations

The fragment covers finite atomic evaluations that are fully sequenced within
each thread. It excludes
consume, sequential consistency, fences, non-atomic accesses and data-race
semantics. Unsupported orders have no access constructor. Full C expressions,
control/value dependencies, object/provenance rules, GNU extensions and program
consistency need separate source semantics and mapping proofs.

Graph identities do not grant OS authority. A machine-to-source connection must
retain actual issue/publication/RMW identities, resource validity, per-thread
ordering, modification order and selected read-from origins. Equal values are
insufficient evidence for that connection. Native CPU/Linux correspondence and
progress remain separate obligations.

The frozen acquire/release corpus contracts keep these requirements. Their
coverage remains unchanged until actual compiler-output executions are tied
to the required source constraints and machine-model assumptions.

The [event regressions](../tests/C23AtomicEvents.lean) include a constructive
nonempty legal release/acquire graph and equal-valued writer/release-sequence
cases. The [message-passing regression](../tests/C23MessagePassing.lean) rejects
the stale-payload outcome through the reusable theorem.
