# Checked atomic execution traces

`EDSL.OS.TSO64.C23Projection.AtomicTrace.verify` constructs and checks a finite
C23 atomic-fragment graph from an actual managed x86-64 execution. Clients supply
the initial machine/resource state, scheduler actions, and typed interface memory
orders. They do not supply initial values, event lists, read-from indices,
publication histories, modification ranks, or graph-legality proofs.

This API connects two existing models: the resource-checked TSO scheduler and
the [C23 atomic-fragment checker](c23-atomic-checker.md). Its result concerns
the supplied finite schedule. Alongside the executable verifier, generic
theorems establish structural well-formedness and sequencing coherence for
mapped graphs, and [finite-fragment legality without acquiring annotations](#universal-no-acquire-legality)
for every actual run satisfying the stated execution and mapping premises.
General acquiring interfaces require further synchronization and happens-before
proofs.

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

These views support the [universal graph sequencing](#universal-graph-sequencing)
results below. General release/acquire interface mappings and graph-construction
totality remain open; universal legality is available for the explicit
[no-acquire fragment](#universal-no-acquire-legality).

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

`AtomicTrace.RMWPredecessor` strengthens this to an exact same-cell predecessor
result. `EventAt.rmw_predecessor` retains both writer identities and proves that
every actual earlier publication to the RMW's cell has rank at most its source
rank. There is no same-cell publication between that source and the RMW, even
when their global ranks have gaps. If the source is the initialized boundary,
`rmw_initial_no_prior_write` excludes every earlier same-cell publication in
the run. An unchanged value or zero-delta RMW still has its own writer identity.

`AtomicTrace.GraphRanks` connects these actual writer ranks to a finite graph
that retains the complete publication list. `EventAt.load_graph_rank` equates a
load view with the rank of the exact writer selected by its semantic RF edge.
The load's own graph row retains rank zero. This correspondence requires
`Graph.Built`; it proves neither graph-construction totality nor C23 legality.
`load_graph_rank_at` accepts a computed event lookup and derives its index bound.
Its graph correspondence does not establish declared-interface synchronization;
exact-source numerical transfer is described below.

The [access clients](../tests/AccessSourceRanks.lean) use actual annotated scans
with equal-valued stores and unchanged-value RMWs. The [RMW boundary clients](../tests/RMWSourceRanks.lean)
also cover an initialized source and a peer action between publication and RMW,
with a peer store still pending. The [graph clients](../tests/AccessGraphRanks.lean)
compute their initial manifest and graph, then distinguish source writer rows,
publication ranks, original action cuts and rank-zero load rows.

## Publication coverage

`PublishedHistory.InstructionWriteAt.covers_after` bounds every actual target
view of the writing thread immediately after its instruction by that write's
publication position plus one. The target may be a different managed cell.
Buffered writes retain their actual issue and eventual publication; an RMW
retains its own action position and empty-queue gate. Coverage uses an actual
`At` witness and imposes no same-cell restriction.

`EventAt.covered_by_write` derives the view domain from an actual access's full
authority. For any cut at or before a same-thread write's successor cut, it
constructs that target's view and bounds it by the write's publication rank.
The access authenticates the target; its own action index need not be the
queried cut. Stable resources and the fixed worker universe remain part of
this scheduler's scope.

For a load, `EventAt.load_source_le_write` also retains the exact source writer
identity. The following contract applies to any actual load followed by an
actual instruction write from the same thread, including a write to another
cell:

```lean
import EDSL.OS.TSO64.C23Projection.AtomicTrace.PublicationViews
open EDSL.OS.TSO64
open EDSL.OS.TSO64.C23Projection.AtomicTrace

example {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {accessIndex writeIndex offset : Nat}
    {stamp : PublishedHistory.Stamp} {target : Queue.ManagedRef}
    {word : EDSL.X86.Word} {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event accessIndex initial actions result offset PublishedHistory.empty)
    (loaded : event.access = .load target word source)
    (written : PublishedHistory.InstructionWriteAt initial actions result profile
      offset writeIndex stamp)
    (sameThread : event.tid = stamp.cause.tid) (ordered : accessIndex ≤ writeIndex) :
    ∃ rank, WriterRank initial actions result profile offset target.handle.cell source rank ∧
      rank ≤ stamp.position + 1 :=
  actual.load_source_le_write execution loaded written sameThread ordered
```

General view coverage permits arbitrary incoming publication metadata under
the explicit `PublishedOrder.Prior` position bound. The exact load-source
corollary starts that map empty, because a numerical bound alone does not
authenticate incoming writer identities. Both APIs permit nonempty initial
mixed FIFOs with well-formed resources and sequenced occurrences; incoming
entries receive no invented issue origins. These execution-level results are
separate from `AtomicTrace.verify`, which checks an empty initial FIFO boundary.

Related clients cover [cross-cell views](../tests/PublicationCoverage.lean),
[incoming queues](../tests/PublicationCoverageBoundary.lean) and
[actual load sources](../tests/PublicationCoverageLoads.lean). Publication
coverage is numerical: it does not establish source release/acquire intent,
cross-thread view transfer, happens-before or full C23 legality.

## Exact-source view transfer

`EventAt.transfers_view` transfers a writer's actual target view immediately
after its instruction to a load's prestate view when that load reads the exact
writer. The viewed target may differ from the loaded cell. The proof derives
instruction order from actual source provenance. A different thread's source
must already have published; own forwarding instead uses same-thread view
monotonicity and does not require publication before the load.

`transfers_view_alias` supports different current handles to the same cell.
Authorization supplies their shared descriptor and address; equal words do not
identify writers or handles. The reader may have a pending write to the viewed
cell, so a transferred rank does not imply that its next load returns the
writer's payload.

`transfers_access_views` constructs both views from actual access authority.
For a new program, a client can provide scan-derived events and the actual
instruction/publication witness, without proving a new view-order invariant:

```lean
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ViewTransfer
open EDSL.OS.TSO64
open EDSL.OS.TSO64.C23Projection.AtomicTrace

example {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event targetEvent : Event} {accessIndex writeIndex targetIndex offset : Nat}
    {readTarget : Queue.ManagedRef} {word : EDSL.X86.Word} {source : WriterId}
    {stamp : PublishedHistory.Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event accessIndex initial actions result offset PublishedHistory.empty)
    (loaded : event.access = .load readTarget word source)
    (written : PublishedHistory.InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (readFrom : source = Graph.publicationKey stamp)
    (targetActual : EventAt profile targetEvent targetIndex initial actions result offset PublishedHistory.empty)
    (targetThread : targetEvent.tid = stamp.cause.tid) :
    ∃ target earlierRank laterRank, AccessTarget targetEvent target ∧
      Nonempty (ExecutionViews.At initial actions result profile (writeIndex + 1)
        stamp.cause.tid target offset PublishedHistory.empty earlierRank) ∧
      Nonempty (ExecutionViews.At initial actions result profile accessIndex event.tid
        target offset PublishedHistory.empty laterRank) ∧ earlierRank ≤ laterRank :=
  actual.transfers_access_views execution loaded written readFrom targetActual targetThread
```

The target access authenticates a domain, not a transferred value assertion.
The incoming publication map starts empty; initial mixed FIFOs may be nonempty,
but an incoming entry receives no invented instruction origin. These finite
numerical results supply no source memory-order inference, synchronizes-with or
happens-before graph, C23 legality, fairness, or native refinement.
The [execution clients](../tests/ViewTransfer.lean) exercise actual source
identities and other-cell views through the shared API.

## Writer successor views and operational coherence

`PublishedHistory.InstructionWriteAt.self_view` constructs the writing thread's
view of its written cell immediately after the instruction, at exactly the
write's publication position plus one. For a buffered store, that rank refers
to its actual later drain; for an RMW, publication happens in the instruction's
own step. The result derives the original worker and complete current target
from the actual instruction. It permits arbitrary incoming publication metadata,
without a `PublishedOrder.Prior` bound. `post_view_rank` gives the same endpoint
through a current alias. An alias requires real `Queue.Current` authority;
an unauthenticated same-cell view alone is insufficient.

`AtomicTrace.Coherence` combines that endpoint with view monotonicity and exact
load sources. Clients reuse these operational constraints without a new
instruction-by-instruction proof:

| API | Constraint on actual same-thread accesses |
| --- | --- |
| `EventAt.write_read_rank` | A write before a same-cell load has rank at most the load's source rank |
| `EventAt.read_read_rank` | Ordered same-cell loads have nondecreasing source ranks |
| `EventAt.read_write_rank_lt` | A load's source rank is strictly below any later instruction write's rank, including a write to another cell |

For example, the strict read/write contract retains the actual source writer:

```lean
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Coherence
open EDSL.OS.TSO64
open EDSL.OS.TSO64.C23Projection.AtomicTrace

example {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {readIndex writeIndex offset : Nat}
    {target : Queue.ManagedRef} {word : EDSL.X86.Word} {source : WriterId}
    {stamp : PublishedHistory.Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event readIndex initial actions result offset PublishedHistory.empty)
    (loaded : event.access = .load target word source)
    (written : PublishedHistory.InstructionWriteAt initial actions result profile
      offset writeIndex stamp)
    (sameThread : event.tid = stamp.cause.tid) (ordered : readIndex ≤ writeIndex) :
    ∃ rank, WriterRank initial actions result profile offset target.handle.cell source rank ∧
      rank < stamp.position + 1 :=
  actual.read_write_rank_lt execution loaded written sameThread ordered
```

The predecessor and coherence APIs use an empty incoming publication map.
All these execution-level results allow nonempty initial mixed FIFOs and require
a finite successful execution, well-formed initial resources, sequenced initial
queues and final quiescence. Incoming queued writes retain their real later
publications without invented instruction origins. The
[writer-rank clients](../tests/WriteViewRanks.lean) include a zero-delta RMW,
an actual suffix with an incoming queued store, forwarding and published reads.
These numerical constraints lift to all-row sequencing coherence through the
actual structural graph context below. Their execution-level contracts alone
do not classify source orders or establish synchronizes-with or happens-before
constraints.

## Read sides of loads and RMWs

`AtomicTrace.ReadAccess event source` identifies either an actual load or the
read side of an actual RMW, retaining its complete source writer identity.
A pure store has no such witness. `EventAt.read_view_rank` recovers the current
target and exact source-rank view at the instruction prestate from the actual
access and execution; the caller supplies neither a desired rank nor target
authority.

The generic APIs include RMW reads in all three operational constraints:

| API | Constraint on actual same-thread accesses |
| --- | --- |
| `EventAt.write_read_source_rank` | A write before a same-cell load or RMW read has rank at most that read's source rank |
| `EventAt.read_read_source_rank` | Ordered same-cell read sides have nondecreasing source ranks; either or both may be RMWs |
| `EventAt.read_write_source_rank_lt` | A read side's source rank is strictly below any later instruction write's rank, including a write to another cell |

These APIs retain the execution-view premises above and an empty incoming
publication map. Initial queues may contain sequenced entries. Operational
views may concern current targets without corresponding graph access events;
view authority and publication ranks alone do not supply source-order intent.

## Structural graph well-formedness

`Graph.Built.wellFormed` proves `C23Atomic.WellFormed table.toCandidate` from
`Graph.Built inputs orders table` alone. It needs no execution, queue boundary,
interface-order restriction or graph-legality checker result. The conclusion
covers all seven structural fields: initializer/thread classification, unique
and present initializers, initial and noninitial rank bounds, same-object write
rank uniqueness, valid read sources and absence of sources on nonreads,
including indices outside the live table.

This is a structural result about supplied data. Registry completeness and
the actual initial RAM values require a separate successful
`Initials.enumerate initial.world = .ok initials` and its provenance theorems.
Neither `Built` nor the execution context below authenticates that manifest.
Structural well-formedness alone does not establish coherence or `Legal`.

## Universal graph sequencing

`AtomicTrace.GraphAccess` defines `Graph.runInputs initials run offset` as the
supplied manifest, every event from `run.events`, and the complete managed
publication list `writes offset run.observations`. `Graph.Executed` connects
those exact inputs to one actual scan through five explicit premises:

| Field | Required evidence |
| --- | --- |
| `valid` | Well-formed initial scheduler resources for the selected profile |
| `sequenced` | Sequenced initial queue occurrences |
| `scanned` | Successful `scan initial actions profile offset PublishedHistory.empty = .ok run` |
| `quiescent` | Empty final queues: `Quiescent run.state` |
| `mapped` | `Graph.Built (Graph.runInputs initials run offset) orders table` |

The scan certificate supplies actual event origins and their original action
order, including positions occupied by silent actions and drains. The complete
publication list supplies actual write origins; matching a buffered publication
to its real store event recovers the instruction issue. Initializer rows retain
their supplied manifest identities and rank zero. No coherence or legality
proof is an input to this context.

`AtomicTrace.GraphCoherence` derives universal constraints over all mapped rows:

| API | Conclusion |
| --- | --- |
| `executed.sequencedCoherent` | All four same-object coherence constraints along `SeqBefore`: write/write ranks increase strictly, read/read source ranks do not decrease, read/write source ranks precede the write strictly, and a write's rank is at most a later read's source rank |
| `executed.noFutureSequenced source` | An RF source cannot be sequenced after its reader |
| `executed.rmwPredecessor rmw source` | Every RMW reads the immediately preceding modification of its object, with no intervening same-object graph write |

RMWs participate in both read and write roles. The predecessor may be an
initializer or an actual write; global publication ranks may have gaps.
These theorems cover every related graph-row pair, rather than a selected list
of pairs. `C23Atomic.CoherentAlong` records the four constraints for a specified
relation, and `SequencedCoherent` specializes it to sequencing. General
synchronizes-with (SW) edges and composed happens-before (HB) paths require
additional obligations.

Initial quiescence is not an `Executed` premise. Ordinary incoming queue
entries and views outside the graph's access events remain permitted. However,
`Built` requires every managed publication to be represented by a matching
in-run write event. Incoming managed entries have no such issue, so this graph
mapping excludes them; their drains receive no invented instruction origins.
Successful scans and nonempty-queue view theorems therefore do not establish
graph-build totality or a graph adapter for incoming managed stores.

The [operational graph clients](../tests/GraphOperationalCoherence.lean) use the
real initial registry/RAM manifests obtained through `Initials.enumerate`.
They reuse the computed equal-valued-store graph and construct a graph with
initial A/B, a store to A, a zero-delta RMW of B and peer loads of B/A. Literal
source rows, ranks, objects and threads distinguish writers despite equal words.
Generic read-side clients also retain initialized RMW sources and source-rank
gaps. Their universal conclusions use the production `Executed` methods and
`Built.wellFormed`.

## Universal no-acquire legality

`AtomicTrace.GraphNoAcquire` proves `C23Atomic.Legal` for every `Graph.Executed`
context whose declared event annotations satisfy
`orders.noAcquire run.events = true`. This Boolean inspects each actual event's
declared interface order, not machine bytes. It checks for the absence of an
acquiring access and performs no order weakening. Release annotations can remain
when no event acquires. `Orders.relaxed` declares every primitive relaxed;
`Orders.noAcquire_relaxed` proves that it passes for any event list, and
`executed.relaxed_legal` supplies the corresponding legality theorem.

The proof excludes every acquiring row, so no SW edge exists. In
`C23Atomic.OrderCoherence`, `HappensBefore.sequenced_of_no_synchronization`
reduces every nonempty HB path to sequencing because sequencing is transitive.
`legal_of_no_synchronization` then combines structural well-formedness,
sequencing coherence, no-future sequencing and RMW predecessors into all fields
of `Legal`: well-formedness, all four HB coherence constraints, HB acyclicity,
no-future-HB reads and immediate RMW predecessors.

The same contract applies to any actual structurally mapped finite run:

```lean
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphNoAcquire
open EDSL.OS.TSO64
open EDSL.OS.TSO64.C23Projection.AtomicTrace

example {initial : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {run : Result} {initials : List Initials.Entry}
    {orders : Orders} {table : Graph.Table}
    (executed : Graph.Executed initial actions profile offset run initials orders table)
    (checked : orders.noAcquire run.events = true) :
    EDSL.Concurrency.C23Atomic.Legal table.toCandidate :=
  executed.legal_without_acquire checked
```

This theorem uses execution constraints and structural correspondence without
running the graph-legality checker or assuming its success. `AtomicTrace.verify`
continues to call the full `C23Atomic.Check.certify` checker and to check empty
initial and final queues; it does not call this no-acquire theorem as a shortcut.

A false `noAcquire` result leaves the synchronization and HB proof obligations
open and establishes no program defect. Acquiring semantics are never silently
lowered. General release/acquire and release-sequence mappings remain separate
from the universal no-acquire result.
The operational graph clients apply this theorem to both computed graphs;
acquiring-load and acquiring-RMW controls on the same actual cross-cell scan
produce false `noAcquire` results.

## Scope

Objects are already initialized and stable for the finite run. The scheduler
does not model C object initialization/lifecycle or dynamic thread creation.
Memory orders are declared primitive/interface annotations; MOV bytes alone
do not establish relaxed, acquire, or release source intent.

Successful checking certifies the supplied finite trace. The universal
no-acquire theorem additionally covers every finite run satisfying its actual
execution, structural mapping and annotation premises. It proves neither
graph-construction totality nor completion of every schedule. General acquiring
TSO-to-C23 preservation, full C23 semantics, a source frontend and source/compiler
preservation remain open. Physical CPU, native Linux and kernel correspondence,
fairness and liveness remain separate obligations.

Frozen compiler-corpus coverage remains **16/40 functions and 32/80 artifacts**,
including **one distinct concurrent function**. See the
[store-history API](managed-store-trace.md) and [trust model](trust.md) for the
supporting boundaries.
