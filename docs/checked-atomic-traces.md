# Checked atomic execution traces

`EDSL.OS.TSO64.C23Projection.AtomicTrace.verify` constructs and checks a finite
C23 atomic-fragment graph from an actual managed x86-64 execution. Clients supply
the initial machine/resource state, scheduler actions, and typed interface memory
orders. They do not supply initial values, event lists, read-from indices,
publication histories, modification ranks, or graph-legality proofs.

This API connects two existing models: the resource-checked TSO scheduler and
the [C23 atomic-fragment checker](c23-atomic-checker.md). Its result concerns
the supplied finite schedule. Proving that every schedule of a program has the
required behavior remains a separate verification obligation.

## Inputs and result

The verifier performs these operations:

1. Check that initial store queues are empty.
2. Enumerate every live cell in the initial registry and read its published word.
   Retired identifier gaps are skipped; cells absent from worker handles are
   still included. A failed cell read is propagated.
3. Run the production scheduler, recording actual managed MOV64 loads, buffered
   store issues, and completed RMWs. Ordinary owned accesses are excluded from
   the atomic graph. All actions, including blocked attempts and drains, retain
   their original positions.
4. Check that final queues are empty, then enumerate all actual managed
   publications and RMW writes.
5. Resolve read-from edges by writer identity, derive modification ranks from
   publication positions, and validate the graph's structural correspondence.
6. Apply the proved finite C23 atomic-fragment checker.

`Output` contains the complete initial manifest, annotated execution, and checked
table. `Failure` distinguishes initial/final queue boundaries, initial RAM reads,
execution faults, graph-mapping failures, and graph-legality rejection. A rejected
or unsupported execution does not establish a security defect.

## Proof contract

The following example uses the same public contract for every input program:

```lean
import EDSL.OS.TSO64.C23Projection.AtomicTrace
open EDSL.OS.TSO64
open EDSL.OS.TSO64.C23Projection

example {initial : State} {actions : List Action} {orders : AtomicTrace.Orders}
    {profile : Profile} {output : AtomicTrace.Output}
    (valid : WellFormed initial profile)
    (checked : AtomicTrace.verify initial actions orders profile = .ok output) :
    AtomicTrace.Verification initial actions orders profile output :=
  AtomicTrace.verify_sound valid checked
```

`Verification` combines complete live-cell enumeration, exact successful
execution, strictly ordered and complete access annotations, real read-source
origins, structural graph correspondence, and the independent `C23Atomic.Legal`
predicate. Well-formed initial resources remain an explicit theorem premise;
empty queue boundaries are checked by the executable verifier.

A buffered writer is identified by its original thread and store occurrence.
An RMW is identified by its original action position. Forwarding retains the
exact newest own-buffer tag and its real earlier issue. Published sources retain
the latest real publication or the initialized boundary when no write occurred.
Equal words do not merge writers. Loads consume graph indices, and buffered
stores receive ranks from their later publication positions rather than their
issue positions. Missing or ambiguous identities and omitted publications reject.

## Published position order

`EDSL.OS.TSO64.PublishedOrder` proves that published writer positions cannot
move backward when an observation stream is extended. A suffix either leaves
the exact stamp unchanged with no same-cell publication, or supplies a strictly
later stamp tied to an actual suffix observation. Equal-valued writes still
count, and silent actions retain their positions. Arbitrary incoming stamps must
predate the stream's offset; this position bound supplies no pre-run provenance.

These lemmas apply across arbitrarily many publications. The managed
[call adapter](managed-plain-methods.md) separately derives
whole-list scanner/call correspondence for one invocation per initial worker.
The [position-view regression](../tests/PublishedPositionViews.lean) follows the
actual six-action run at offset 37: its view changes at managed publication,
then survives both returns and the final ordinary drain.

## Pending writers and FIFO order

`EDSL.OS.TSO64.PendingViews` connects the production newest-qword selection at
any actual execution cut to its unique later publication. A complete successful
run and final empty queues supply that publication; a caller does not choose
its position. Nonempty initial queues are allowed when their occurrence numbers
are ordered. Their earlier issues remain an explicit boundary.

`StoreHistory.Order` proves that actual issue positions, managed occurrences
and actual drain positions have the same strict order for a worker. This covers
arbitrarily many accesses, different references and cells, equal words, ordinary
entries between managed stores, and interleaved peer actions. Publication stamps
retain their full causes and original action positions.

`PendingPublication.rank` is one plus the actual publication position. At a cut,
the newest own managed selection dominates all same-address pending managed
writers by that rank. Every already-published position view is strictly below a
still-pending writer's future rank. For example, this bound uses the same API
for every program:

```lean
import EDSL.OS.TSO64.PendingViews
open EDSL.OS.TSO64
open EDSL.OS.TSO64.StoreHistory

example {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {cut tid occurrence : Nat} {reference : Queue.ManagedRef} {value : EDSL.X86.Word}
    (writer : PendingPublication initial actions result profile cut tid reference value occurrence)
    (cell : EDSL.OS.Atomics64.CellId64) :
    PublishedOrder.view
      (PublishedHistory.after 0 (result.2.take cut) PublishedHistory.empty) cell <
        writer.rank 0 :=
  writer.published_view_lt_rank (PublishedOrder.prior_empty 0) cell
```

The [execution client](../tests/PendingPublicationViews.lean) uses repeated
equal-valued stores, mixed ordinary/managed queues and two interleaved threads.
It also checks the bound after a peer has published, when the published view is
already nonzero and the selected own writer remains pending.

These ranks describe actual future publications in the supplied finite run;
they do not promise that every scheduler completes. Exact-address queue selection
alone does not establish a byte load's value under partial overlaps: the existing
resource and whole-qword compatibility premises still apply. Monotonicity through
all pending/published transitions, release/acquire transfer and universal C23
legality remain open.

## Scope

Objects are already initialized and stable for the finite run. The scheduler
does not model C object initialization/lifecycle or dynamic thread creation.
Memory orders are declared primitive/interface annotations; MOV bytes alone
do not establish relaxed, acquire, or release source intent.

Successful checking is conditional finite trace certification. It does not
establish universal TSO-to-C23 preservation, source/compiler preservation,
physical CPU or native Linux correspondence, fairness, or liveness. It adds no
frozen compiler-corpus function credit. See the [store-history API](managed-store-trace.md)
and [trust model](trust.md) for the supporting boundaries.
