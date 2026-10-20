# Finite counter call linearizability

`EDSL.Concurrency.Linearizability` defines a reusable finite invocation/response
protocol with abstract identity, thread, input and output types.
`EDSL.OS.TSO.CounterCalls` binds it to actual production `OS.TSO.step` schedules
for the existing **32-bit modular** fetch-add counter. These modules are imported
directly; this change does not modify umbrella imports or shared workflows.

A call has a globally unique identity, a thread, an invocation input and a
response output. The internal `point` carries that same identity and the actual
operation. `publicHistory` erases internal points. The finite protocol requires
exactly one invocation, one point and one response for each identity, matching
thread/input/output, with strictly increasing invocation/point/response positions.
It also excludes overlapping call intervals on a single thread. Distinct threads
may overlap, and invocation, RMW and response orders may differ.

`intervals` computes the proposed serial list by filtering chronological points;
it does not accept an arbitrary permutation. `check` validates finite lifecycle
facts, not sequential results or real-time linearizability. `linearize` proves
that these intervals are chronological and that a response preceding another
call's invocation forces the first point before the second. Its pairwise
`extendsRealTime` field prohibits the reverse order in the serial list. The
caller must independently prove the sequential object specification on `calls`.

## Actual TSO32 binding

An `Entry.invoke` is an **external environmental annotation** at a finite schedule
boundary. It asserts a call identity, thread and input; it is not inferred from
native instructions, a language ABI, CPU behavior, or OS authority. Successful
admission proves agreement of that input with the actual RMW source register.
It does not establish that the annotated boundary is a native function entry.

Every `Entry.execute` selects an actual `TSO.Action`. `replay` checks the existing
`CounterCheck.checkPermitted` byte-footprint policy against the current state and
runs production `TSO.step`. Quiet selections can execute ordinary stores/loads,
blocked locked issues, drains and disjoint atomic operations. Store buffers and
interleaving remain active. A target-cell RMW must carry an `rmw id` mark. Its
thread, input and result are extracted from the actual observation and pre-state
RAX, and `emit_sound` derives a `Counter.Origin` from successful scheduling and
the checked policy. That origin retains the decoded `LOCK XADD`, empty issuing
FIFO, actual architectural execution, exact installed context and atomic event.
No input is reconstructed by subtracting counter values. `replay` and
`checkComplete` fail closed: their option/Boolean results do not distinguish
machine faults, policy failures and malformed annotations. Raw `TSO.schedule`
retains machine faults when a caller needs that diagnostic.

A response mark supplies identity, thread and claimed 32-bit ticket. It must be
on an actual successful issue of decoded `RET`; `checkReturn_sound` retains its
architectural execution on the forwarded local view, installed returned context,
and full RAX equal to the zero-extended ticket. Matching the response to the
point ensures this is the old value returned by that call's XADD. A label on a
MOV, drain, blocked issue or another thread's return is not a response witness.
The current production scheduler has terminal returned workers; this adapter
therefore describes complete one-shot calls by its workers, with no respawn or
caller reentry mechanism added here.

`checked_linearization` needs an actual initial four-byte RAM read and a true
`checkComplete`. It yields actual successful scheduling, `Run`,
`Counter.MachineHistory`, final RAM, the independent `Counter.Sequential`
relation on the completed call list, a generic `Linearization`, and the modular
sum theorem. Sequential results are derived from origins and RAM continuity;
they are not premises of annotation admission. `Run.backed` additionally exposes
an `Occurs` witness for every point and response: the origin is tied to an
actual successful prefix of the same action list. `Run.event_at` provides the
stronger indexed correspondence: it splits the actual entry list at that exact
event, retains the earlier `Run`, and proves that its emitted-label count equals
the event index. `Run.interval_boundaries` applies this to the invocation, RMW and
response positions of each complete call. Invocation boundaries remain explicitly
environmental; point/response boundaries retain actual singleton step emissions.
No future origin is supplied. Together with unique lifecycle coverage and strict
interval bounds, this gives
one actual target RMW inside each complete call and preserves nonoverlapping
completed calls' real-time order.

## Pending prefixes and limits

The exported whole-call theorem covers **finite complete histories only**.
`replay` can succeed on an incomplete prefix, and `Pending` explicitly describes
an invocation without a response. `Protocol.no_pending` proves that complete
admission excludes it. `checkComplete` rejects missing invocation/point/response
labels, duplicate lifecycle events, mismatched inputs or outputs, and invalid
bounds. This change does not claim the standard extension theorem for arbitrary
pending calls and does not invent future returns.

The counter policy is a checked noninterference restriction on the actual finite
schedule, including partial byte overlap. It preserves ordinary buffering; it
does not promise the same property for unexecuted future drains. A final RET
need not imply global FIFO quiescence. Addressability, permissions, fixed-code
checks and scheduler failure remain those of the production TSO model. The
initial state may be arbitrary: this theorem assumes neither `BuffersValid`
nor reachability from `TSO.initial`. Preserving the fixed-code invariant for
arbitrary initial buffered stores needs that separate initial-state obligation;
a disjoint initial buffer could otherwise publish to executable bytes. The
counter theorem still derives its origins from each actual current decode.

Complete annotations do not imply `Returned`, `Quiescent`, or `Finished` for all
workers. Unannotated workers may still run, and the empty history is complete.
Relating the supplied labels to all external native calls requires faithful
environmental annotation. Failure, unsupported code and proof timeout do not establish a security defect.

No progress, termination, fairness, source memory orders, published Owens
x86-TSO refinement, physical CPU behavior, or OS ownership theorem is established.
The generic layer has no width restriction, but this concrete adapter does not
support 64-bit counter instructions, certify any frozen 64-bit corpus entry, or
change the 0/40 grading score. The broad repository goal remains incomplete.

## Validation

`tests/TSOCounterCalls.lean` runs independently encoded synthetic machine code
through the production scheduler. Two overlapping schedules vary RMW order and
reverse RMW and response order; one also reverses invocation and RMW order. Both threads buffer stores
and experience blocked locked issues. A separate nonoverlap case fixes ticket
order, and a wraparound case checks modular ticket behavior. Negative cases cover
duplicate invocation, wrong invocation input, response before invocation, wrong
returned ticket, a real RET after overwriting the RMW result, wrong invocation
thread, overlapping generic calls on one thread, missing RMW label or operation,
response without a RET, pending calls, and two actual RMWs using one call identity
(including zero additions with identical tickets). No native tests are needed for this logical
protocol extension. Build and audit receipts are kept in the ignored owned work
directory and reported separately from development failures.
