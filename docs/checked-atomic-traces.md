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
resource and whole-qword compatibility premises still apply.

## Execution views

`EDSL.OS.TSO64.ExecutionViews` proves that a thread's own-pending/published view
cannot decrease across any two ordered cuts of one actual finite execution.
Views measure publication positions; the stored words remain unconstrained by
this order. A view retains the newest own pending writer's actual future rank,
or the published-prefix rank when no own writer is pending for that target.

The proof uses exact-entry conservation over the intervening execution. A writer
that remains pending is dominated by the later newest selection. A writer that
drains is covered by the later published history and precedes every publication
still pending at that cut. The result covers arbitrarily many accesses per
worker, equal payloads, different handles, mixed ordinary entries, RMWs, peer
interleavings, returns and cuts past the end.

```lean
import EDSL.OS.TSO64.ExecutionViews
open EDSL.OS.TSO64

example {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {first last tid offset a b : Nat} {target : Queue.ManagedRef}
    (execution : ExecutionViews.Execution initial actions result profile)
    (ordered : first ≤ last)
    (earlier : ExecutionViews.At initial actions result profile first tid target offset
      PublishedHistory.empty a)
    (later : ExecutionViews.At initial actions result profile last tid target offset
      PublishedHistory.empty b) : a ≤ b :=
  earlier.monotone execution (PublishedOrder.prior_empty offset) ordered later
```

`Execution` retains actual scheduler success, well-formed initial resources,
sequenced initial queues and final quiescence. `exists_at` constructs a view for
an existing worker and a current managed target; the target authority may belong
to any original resource record. Connecting every actual access to this domain
and to its exact read-source rank is described below.

`query` computes a view from a prefix state and the complete observation list.
`query_sound` connects its answer to an actual `At` witness under the execution,
prefix and current-target premises. The pending branch searches for the complete
writer tag, preserving thread, reference, value and occurrence. Missing or
inexact publications and ordinary selected entries reject. The raw metadata
function supplies no execution or authority certificate by itself.

`PublishedHistory.InstructionWriteAt` also proves that same-thread instruction
writes and their publication ranks have the same strict order across all
store/store, store/RMW, RMW/store and RMW/RMW combinations. Buffered writes need
actual issue witnesses; incoming queue entries receive no invented instruction
positions. The RMW's own-empty gate forces preceding stores to publish first.
This order-only theorem requires no final quiescence.

Release/acquire view transfer, totality of graph construction and universal
operational C23 legality remain open.

## Actual access and source ranks

`AtomicTrace.AccessDomain` derives a managed access's target authority from its
actual instruction origin. Loads and stores retain their complete selected
reference. An RMW recovers its checked handle, persistent cell and operand
address. The successful prefix preserves that authority and the worker's full
resource record back to the initial state. `EventAt.views` then constructs views
at arbitrary cuts without a supplied view-domain assumption.

`AtomicTrace.ReadRanks` connects an actual load's source identity to the exact
writer publication rank of its prestate view. Published reads use the real
prefix's latest writer or initial boundary. Forwarded reads retain the newest
selected tag and its unique future publication in the complete execution.
The incoming publication map starts empty; initial pending queues may be
nonempty, and their entries receive no invented earlier instruction issues.

```lean
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadRanks
open EDSL.OS.TSO64
open EDSL.OS.TSO64.C23Projection.AtomicTrace

example {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {index offset : Nat} {target : Queue.ManagedRef}
    {word : EDSL.X86.Word} {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset PublishedHistory.empty)
    (loaded : event.access = .load target word source) :
    ∃ rank, Nonempty (ExecutionViews.At initial actions result profile index event.tid
      target offset PublishedHistory.empty rank) ∧
      WriterRank initial actions result profile offset target.handle.cell source rank :=
  actual.load_view_rank execution loaded
```

An actual RMW reads a published-prefix writer and publishes its own write at
its original action position. `EventAt.rmw_view_rank` proves that the source
rank is strictly below its own rank. Gaps are expected because ranks count
silent actions and other-cell publications too.

`AtomicTrace.GraphRanks` connects these actual writer ranks to a finite graph
that retains the complete publication list. `EventAt.load_graph_rank` equates a
load view with the rank of the exact writer selected by its semantic RF edge.
The load's own graph row retains rank zero. This correspondence requires
`Graph.Built`; it proves neither graph-construction totality nor C23 legality.
`load_graph_rank_at` accepts a computed event lookup and derives its index bound.
Cross-cell release/acquire view transfer remains separate.

The [access clients](../tests/AccessSourceRanks.lean) use actual annotated scans
with equal-valued stores and unchanged-value RMWs. The [RMW boundary clients](../tests/RMWSourceRanks.lean)
also cover an initialized source and a peer action between publication and RMW,
with a peer store still pending. The [graph clients](../tests/AccessGraphRanks.lean)
compute their initial manifest and graph, then distinguish source writer rows,
publication ranks, original action cuts and rank-zero load rows.

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
