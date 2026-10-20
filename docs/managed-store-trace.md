# Computed store traces

Import `EDSL.OS.TSO64.C23Projection.StoreTrace` to record store issues while
running the existing managed scheduler. The scanner derives annotations from
actual instruction decoding and queue admission; clients supply no issue list
or history oracle.

`StoreHistory.Trace.scan initial actions profile offset` returns either the
same fault as `schedule`, or a `Trace.Result` containing the actual final state,
actual observations and computed store issues. Every action consumes a position,
including blocked attempts and drains. The offset names the run's initial
position and changes no execution behavior.

## Successful scans

`scan_certificate` derives the following from successful scanning alone:

- Erasing annotations gives precisely the existing successful schedule.
- Each recorded issue corresponds to an actual `IssuedAt` instruction position,
  retaining the full ordinary ticket or managed descriptor, value and occurrence.
- Every actual store issue appears in the computed list.
- Issue positions are strictly increasing, which also excludes duplicate entries.

`scan_error_iff` establishes exact fault preservation, including fault payloads.
A failed scan does not produce a successful truncated issue list. `capture` on
its own is only a prestate classification; it cannot replace successful
execution, current-authority checks or any other scheduler gate.

This complete API example retains the successful computation as its sole
substantive premise:

```lean
import EDSL.OS.TSO64.C23Projection.StoreTrace
open EDSL.OS.TSO64

example {initial : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {result : StoreHistory.Trace.Result}
    (checked : StoreHistory.Trace.scan initial actions profile offset = .ok result) :
    StoreHistory.Trace.Certificate initial actions profile offset result :=
  StoreHistory.Trace.scan_certificate checked
```

The classifier records both ordinary and managed stores. Ordinary stores also
consume the per-worker counter, so managed occurrence numbers can have gaps.
RMW instructions are retained in the actual observation stream and are not
misclassified as ordinary buffered issues.

## Publications

`C23Projection.writes offset observations` enumerates every managed publication
and RMW using the existing write classifier. It retains complete causes and
original action positions. Identical values and identical RMW event records
remain separate writes. Issuing a buffered store emits no publication stamp.
`writes_origin` connects each computed stamp to the existing actual-prefix
`PublishedHistory.WriteAt` contract when its observations come from a successful
schedule; `writeAt_mem_writes` proves that no such write is omitted.

`scan_issue_published_once` connects a computed managed issue to exactly one
later drain and its computed write stamp. It requires initial `Sequenced` and
final `Quiescent`. Those premises concern numerical FIFO integrity and an
already completed finite run; they do not assert that every scheduler finishes.

`scan_publication_origin` connects every computed buffered publication to a
unique earlier computed issue with the same complete identity. It requires
empty initial queues to exclude pre-run stores. Empty initial queues imply
`Sequenced` through `quiescent_sequenced`; they do not imply world or authority
well-formedness. Returning from a function does not empty its pending FIFO.

## Validation and remaining work

The [regressions](../tests/TSO64StoreTrace.lean) run actual decoded stores,
blocked attempts, drains, unchanged-value RMWs and returns. They distinguish
issue positions from publication positions, retain counter gaps across mixed
authority, check both memory effects, and reject a scan at the exact managed
policy fault after an earlier ordinary issue.

These interfaces annotate finite runs of the existing fixed-world scheduler.
The [checked atomic-trace API](checked-atomic-traces.md) adds managed loads,
identity-based read-from sources, complete initial-object coverage, declared
interface orders and publication-based modification ranks. No full source/compiler preservation,
physical CPU/Linux correspondence, fairness, liveness or additional frozen
compiler-function certification follows from this store trace alone.
