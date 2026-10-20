# Counter histories over buffered execution

`EDSL.OS.TSO.Counter` relates actual locked fetch-add retirements in the
[buffered scheduler](store-buffers.md) to an independent sequential counter
contract. The main theorem, `schedule_linearization`, covers a successful finite
schedule satisfying an explicit noninterference policy. Its operations are
modeled machine instructions at retirement.

The API is defined in
[`CounterHistory.lean`](../EDSL/OS/TSO/CounterHistory.lean) and
[`Counter.lean`](../EDSL/OS/TSO/Counter.lean), with finite checking in
[`CounterCheck.lean`](../EDSL/OS/TSO/CounterCheck.lean). It is separate from the
[counted-worker protocol](counter-workers.md), which tracks published loop
counts, worker completion and resource collection.

## Independent sequential contract

`Operation` records a worker index, a 32-bit argument `delta` and a 32-bit
old-value `result`. `Sequential before operations after` specifies that each
operation returns the current word and updates it by its argument:

```text
v₀ = before
operationᵢ.result = vᵢ
vᵢ₊₁ = vᵢ + operationᵢ.delta   (modulo 2^32)
after = vₙ
```

This relation does not execute machine code or derive an argument by subtracting
event values. `Sequential.total` gives
`after = before + totalDelta operations`, also in `BitVec 32`. The returned-word
chain is stronger than the aggregate sum: every recorded addition reads the
word left by its predecessor, so no recorded update is lost. Wraparound and
zero deltas remain valid; natural-number counting needs a separate overflow
bound.

If every operation has delta one, `Sequential.unit_updates` specializes the
result to `after = before + BitVec.ofNat 32 operations.length`. This counts
recorded increments modulo 2^32, without assuming that a worker completed its
requested loop count.

## Exact schedule premises

`schedule_linearization` takes three premises:

- `loadDWord before.memory address = .ok initialValue`, independently observing
  the initial shared word;
- `SchedulePermitted address before actions`, imposing the policy below at
  each successful schedule prefix;
- `TSO.schedule before actions = .ok result`, supplying actual execution of
  the complete supplied finite action list.

For a selected `.issue identifier`, `IssuePermitted` examines the worker and
the instruction decoded from its current context and shared executable memory.
Whenever that instruction is locked and the worker's own FIFO is empty, it
requires either:

1. RDI equals the counter address and the decoded instruction is exactly
   `.fetchAddEaxRdi`; or
2. `DWordDisjoint RDI address 4`.

Thus a retiring RMW on the counter must be an actual decoded
`LOCK XADD DWORD PTR [RDI], EAX` (`f0 0f c1 07`). Every other retiring RMW must
have a four-byte footprint disjoint from the counter. An XCHG at the counter is
excluded even if its observed values happen to match an addition.

For a selected `.drain identifier`, `DrainPermitted` requires
`DWordDisjoint head.address address 4` for the selected worker's actual FIFO
head. Every scheduled publication must therefore avoid every counter byte.

Precisely, `DWordDisjoint write address 4` means that for each natural offset
`i < 4`,

```text
4 ≤ ((address + BitVec.ofNat 64 i) - write).toNat
```

Address arithmetic here is modular 64-bit arithmetic. Merely having different
starting addresses is insufficient. Both RMW and drain obligations concern
byte footprints, including partial overlaps.

`SchedulePermitted` is a proof premise on the supplied schedule, not an extra
runtime gate in `TSO.step`. It recurses through every successful prefix; it does
not assume a final counter value. Blocked locked issues have nonempty local
FIFOs and perform no RMW. Ordinary store issues may enqueue overlapping writes,
but the policy excludes draining those writes during this schedule. Such a
write can remain pending at the endpoint, and an ordinary load can see it
through forwarding. The counter theorem describes shared RAM and recorded
RMWs; it supplies no sequential specification for those ordinary loads.

## Actual execution and chronological provenance

The existing scheduler continues to buffer ordinary stores, forward each load
from its worker's newest matching pending bytes, and publish FIFO heads through
independent drains. A locked instruction waits for its own FIFO to empty and
then operates indivisibly on shared RAM. Peer FIFOs need not be empty, and a
locked issue does not drain them. RET keeps its ordinary execution and does not
flush a queue. These rules come from `TSO.Model`, not a counter-specific
replacement scheduler.

`Origin` binds each counter operation to the actual issuing action, a present
unreturned worker, shared instruction decoding, an empty local FIFO, successful
architectural fetch-add execution, the installed context/memory and the exact
retirement observation. Its argument is the low 32 bits of that worker's
**pre-instruction RAX**. Its result is the event's old word.

`Origin.effects` connects that independent interface to the pre-step shared
word, the post-step modular sum and the exact event. It also identifies the
issuing worker's immediate post-step RAX as the zero-extended old word. Later
instructions may change that register.

`MachineHistory` follows successful scheduler steps in chronological order.
Each addition carries `Origin`; each quiet step preserves the counter's shared
word and emits no target event. `eventsAt` filters only actual
`.retired identifier (some event)` observations whose starting address equals
the selected counter address. The footprint policy separately excludes foreign
overlaps that this exact-address filter would not detect.

The theorem returns a final shared word and an operation list with:

- the successful final shared-memory read;
- `Sequential initialValue operations finalValue`;
- `MachineHistory` for the exact supplied actions, observations and final state;
- `operations.map (Operation.event address) = eventsAt address result.2`;
- `finalValue = initialValue + totalDelta operations` modulo 2^32.

`MachineHistory.trace` projects to `TSO.Trace`. `MachineHistory.events` retains
the exact target event list, with no sorting or permutation.
`MachineHistory.issued_sublist` embeds the operation worker indices as a
subsequence of the supplied action list's issue selections (`issuedThreads`).
`MachineHistory.thread_order` preserves that chronology when filtering by
worker index. It concerns machine-operation order in this trace.

The result accepts finite prefixes without assuming `Returned`, `Quiescent` or
`Finished`. It supplies neither execution success nor an eventual drain,
completion, fairness or timing bound. It also does not require initial empty
buffers or `BuffersValid`: those are separate admission facts when interpreting
a state as a reachable execution in the scheduler's aligned, fixed-code
profile. Raw state construction alone establishes no such admission.

## Finite schedule checking

`checkDisjoint` checks the four byte-footprint bounds. `checkPermitted` checks
the selected issue or drain against the current state. `checkSchedule` combines
that policy check with successful execution through the production `TSO.step`
at every action; it does not implement a separate counter executor.

`checkSchedule_sound` supplies both successful `TSO.schedule` execution and
`SchedulePermitted`. `checked_linearization` combines this with an independently
observed initial word: a proof that `checkSchedule address before actions = true`
supplies the same sequential history, event provenance and modular total as
`schedule_linearization`, together with the successful schedule. A false result
establishes no defect; no completeness theorem for the checker is supplied.

## Boundaries of the claim

**Whole-function linearizability.** This API has no invocation/response history,
call identity or correspondence between function-entry arguments and the
pre-XADD argument. It does not connect a function's eventual return value to the
old value captured at the instruction, or prove the real-time order of
nonoverlapping calls. Establishing those properties requires a surrounding
routine and call-history refinement. Here, the linearization point is the
modeled atomic retirement itself.

**Formal x86-TSO refinement.** The framing reference is Owens, Sarkar and
Sewell's [*A better x86 memory model: x86-TSO*, Sections 3 and 3.1](https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.pdf).
Their abstract machine describes FIFO buffering, forwarding and explicit
lock/unlock transitions. This Lean scheduler packages each supported locked RMW
into one indivisible step. No simulation or equivalence theorem connects this
implementation to the paper's HOL4 machine or axiomatic model. Finite-prefix
safety also supplies no eventual-publication progress condition.

**Physical execution.** `X86.atomicAddressable` restricts successful RMWs to
canonical, nonwrapping, naturally aligned four-byte operands without virtual
64-byte-line or 4-KiB-page crossing. Physical interpretation additionally needs
the coherent write-back RAM, stable translation and alias/access restrictions
described in the [atomic profile](atomic-exchange.md) and
[buffered execution profile](store-buffers.md). Physical CPU behavior, devices,
exceptions, self-modifying code and unsupported instructions receive no new
conformance theorem here. An unsupported or failed execution establishes no
defect.

**GNU source atomic orders.** `Operation` has no GNU C/C++ atomic memory-order
field. The theorem does not establish source-language relaxed, acquire,
release, acquire-release or sequentially consistent semantics, compiler
preservation, or argument publication. Those need their own source and runtime
contracts even when compilation produces these instruction bytes.

**OS resource ownership.** `TSO.State` stores memory and machine workers; this
counter policy carries no allocation owner, actor handle, read loan or checked
spawn/join authority. Worker indices do not authenticate native threads.
`SchedulePermitted` states environmental noninterference and does not derive it
from ownership. Connecting it to the repository's resource protocols and native
thread lifecycle remains a separate obligation.
