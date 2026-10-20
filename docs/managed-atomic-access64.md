# Managed shared-cell loads and publication

[`EDSL.OS.AtomicAccess64`](../EDSL/OS/AtomicAccess64.lean) provides reusable
full64 load and publication operations for the existing managed-cell resource
model. The buffered scheduler's explicit `sharedCell` profile uses these
operations for managed qword MOV access. These interfaces add no compiler-corpus
certificate or source-language synchronization guarantee.

```lean
import EDSL.OS.AtomicAccess64

#check EDSL.OS.Atomics64.load
#check EDSL.OS.Atomics64.publishStore
```

Both operations select a cell through a current actor/handle identity. They
recheck the live cell, allocation owner and epoch, full eight-byte containment,
alignment, mapping, read/write permissions and nonexecutable data. The initial
profile conservatively requires RW access even for a load. Handles represent
logical authority; native authentication and enforcement remain environmental
obligations.

`load` returns the actual current published qword and leaves the complete
resource state unchanged. `publishStore` writes a supplied full64 value to the
selected cell and preserves its managed reservation. Neither operation accepts
a substitute address or ownership ticket. Ordinary owner mutations of the
reserved allocation remain rejected, including writes to neighboring bytes in
that allocation.

## Reusable proof interface

Clients can use the following theorems without unfolding the resource
implementation:

| Obligation | API |
| --- | --- |
| Actual current read and checked identities | `load_context`, `load_read` |
| Unchanged complete state after a load | `load_unchanged` |
| Success from present authority | `load_enabled`, `publishStore_enabled` |
| Exact checked store and whole memory projection | `publishStore_primitive`, `publishStore_projection` |
| Full64 readback | `publishStore_readback` |
| Immediate peer load through its original same-cell handle | `publishStore_load` |
| All unrelated byte cells and permissions | `publishStore_frame`, `publishStore_effect` |
| Current ownership, handles and allocation invariants | `publishStore_current_retained`, `publishStore_authority_retained`, `publishStore_wellFormed` |
| Live code/caller loan contents and other allocations | `publishStore_loan_contents`, `publishStore_loan_read`, `publishStore_preserves_other` |

Enabledness follows from current authorization and resource invariants. It
does not assume a desired value, a future successful mutation, or a valid
successor state. Faults carry no partial state or successful access event.

The [regressions](../tests/AtomicAccess64.lean) exercise actual checked setup and
cross-actor access, full64 byte order, neighboring memory, code/caller loans,
continued reservation, stale epochs, wrong actors, closed handles and invalid
permissions on the last operand byte.

## Publication and concurrency

[`WholeQWord`](../EDSL/X86/StoreBuffer/WholeQWord.lean) relates the existing
mixed-width buffer projection to a single full64 store. It requires an
addressable qword and a compatible buffer: every pending store must either
replace that complete qword or be disjoint from all eight bytes. A DWORD must
be disjoint. The theorem identifies the newest matching entry and proves that
all later stores miss the operand. With no matching entry, the load uses the
actual current published memory, including any read fault.

`QWordOrigin.index` names a position in the supplied buffer snapshot. Equal
values at different positions remain distinct; draining the FIFO can change
the index. It is not a persistent issue identifier or a source reads-from
witness. The [regressions](../tests/WholeQWordProvenance.lean) include repeated
values, disjoint mixed-width stores, FIFO publication, current-memory faults
and a partial DWORD overlap that fails the compatibility condition. These
buffer facts grant no OS access authority. A scheduler must derive
compatibility and current permissions from its resource invariants.

[`ManagedPublication`](../EDSL/OS/TSO64/ManagedPublication.lean) connects a
checked `publishStore` to the existing scheduler's complete-memory publication
contract: stable resource metadata and exactly the production qword update.
It derives enabledness from current authorization and world invariants.

[`TSO64.Queue`](../EDSL/OS/TSO64/Queue.lean) provides the checked FIFO policy
used by that instruction engine:

- `admit` prefers the existing ordinary `StoreGate`. The explicit `sharedCell`
  profile permits an exact-address managed qword fallback. DWORDs and neighboring
  addresses have no managed fallback; `ownedOnly` remains the default.
- A managed `Entry` retains its original handle identifier, complete handle and
  cell descriptors, full64 value and occurrence. `publish` checks current grant
  membership and exact reauthorization before calling the OS primitive. Even a
  valid replacement descriptor at the same address cannot replace the original.
- `publishHead` publishes exactly one FIFO head. Its effect proves equality of
  the complete memory projection, unchanged metadata, preservation of live loan
  bytes and the issuing buffer's actual Mixed view after removing the head.
  Every managed publication retains its store event, including unchanged values.
- `Cursor.enqueue` allocates a per-worker store sequence number only after
  successful admission. Ordinary stores consume numbers too. Draining never
  resets the counter or renumbers remaining entries. Its ordering invariant
  rules out duplicate managed occurrences and relates a newest-qword buffer
  position to its actual tagged entry.

The [queue regressions](../tests/ManagedQueue64.lean) use checked OS setup and
independent memory observations to cover peer visibility, FIFO order, repeated
equal values, descriptor replacement, policy denials and current permissions.
The lower-level `enqueueOrdinary`, `enqueueManaged` and `dropHead` operations
only update bookkeeping; they do not grant authority or perform publication.

## Buffered instruction execution

Import [`EDSL.OS.TSO64`](../EDSL/OS/TSO64.lean) and select `sharedCell` explicitly
on `issue`, `drain`, `step` or `schedule`. The same instruction engine, decoder
and Mixed byte semantics serve both profiles. Every recursive schedule call
retains the selected profile. `ownedOnly` remains the default; its existing
fetch-add history and method/ABI adapters keep their original scope.

Plain accesses prefer ordinary authority. Only an exact-address full64 MOV load
or store may use the managed fallback. A store enters the one mixed FIFO and
advances its worker counter only when real instruction execution succeeds.
Loads use the actual newest matching own qword or current published memory.
Whole-qword compatibility follows from current allocation/handle invariants;
neither a pending overlay nor a caller-supplied compatibility premise grants
access. Original code and caller-loan bytes remain protected.

LOCK waits for the entire issuing FIFO to empty, including either entry tag.
Peer FIFOs do not block it. RET can complete with stores still pending;
collection requires the returned worker to be quiescent. Finite publication
derives enabledness from present authority and world invariants.

[`Occurrences`](../EDSL/OS/TSO64/Occurrences.lean) proves numerical queue integrity
from empty setup through actual steps and schedules, separately from resource
validity. A per-worker sequence number must be paired with the scheduler thread
identifier. An arbitrary nonempty initial queue or its ordering invariant
establishes no prior issue events or global reads-from relation.

[`StoreHistory`](../EDSL/OS/TSO64/StoreHistory.lean) proves that every pending
entry after a successful schedule either belonged to that thread's initial
queue or came from an actual store issue in the schedule. The issue witness
retains the decoded instruction, prestate operands, checked admission and
committed FIFO update. Managed occurrences equal the issuing worker's original
counter. The same provenance holds for the exact tag subsequently published
by a drain. Starting from empty queues removes the initial-boundary alternative.

[`ReadHistory`](../EDSL/OS/TSO64/ReadHistory.lean) connects an actual MOV64 load
to the exact newest managed occurrence in its own queue, including that
occurrence's issue provenance, or to current published memory when no matching
own store exists. It derives queue compatibility from current resources and
preserves the actual destination-register result. Equal values do not identify
writers; queue positions may change after a drain while occurrence numbers
remain attached to their original entries.

| Client obligation | Reusable theorem |
| --- | --- |
| Pending tag's initial or actual issue origin | `StoreHistory.schedule_pending_origin` |
| Actual issue from empty initial queues | `StoreHistory.schedule_pending_issued` |
| Origin of a subsequently published tag | `StoreHistory.drain_after_schedule_origin` |
| Tagged source of an actual managed MOV64 | `OrdinaryEffect.managed_read_source` |
| Forwarded source and actual issue history after a prefix | `schedule_loadMem64_history` |

These theorems annotate the existing executor; they introduce no alternative
execution engine or postcondition checks in instruction admission.

[`PublishedHistory`](../EDSL/OS/TSO64/PublishedHistory.lean) records each managed
cell's newest actual publication or RMW. A stamp includes its global scheduler
position and thread. Buffered publications also retain the original complete
reference and per-worker occurrence; RMWs retain the full checked event. Every
write updates the stamp, including equal-value stores and zero-delta RMWs.
Silent actions still consume schedule positions, so equal event payloads do
not merge distinct RMW occurrences. RET preserves the map and does not publish.

The writer map is an observation annotation, not an alternative executor.
`schedule_read` proves agreement with actual published whole-word memory.
`newest_write_at` exposes the real prefix and successful step for the stamp,
and proves that no later observation writes that cell. A buffered stamp's
`WriteAt.buffered_origin` recovers its initial-queue or actual instruction-issue
origin. `loadMem64_origin` combines this history with an actual MOV64 effect:
the load forwards its newest own entry, reads the initial RAM boundary, or
reads the newest actual publication/RMW, and installs that exact word.

An empty initial writer map does not invent a pre-run writer for RAM. Arbitrary
initial maps and nonempty queues remain explicit boundaries. Current resource
validity and the original cell descriptor are separate premises; the ghost map
grants no authority and performs no memory mutation. The
[managed-word trace refinement](word-tso-refinement.md) additionally preserves
actual read/write labels against an independent uniform64 TSO fragment.
Source-language orders, synchronization and physical x86-TSO/Linux refinement
remain separate.

The [instruction regressions](../tests/TSO64SharedCells.lean) execute real MOV,
LOCK XADD and RET bytes in two checked actor contexts. They cover repeated equal
stores, publication after return, mixed FIFO blocking, peer visibility and current
RAM fallback through a nonempty own buffer.

`publishStore` is a shared-memory publication operation. A buffered instruction
may issue a store and return before that store publishes. The default
[managed scheduler](managed-fetch-add64.md) profile continues to exclude plain
access to registered atomic allocations; the explicit shared-cell profile uses
the checked access and publication rules above.

The typed events retain checked actor, handle, cell, address and value. A value
alone cannot identify the write a load observed: separate writes can store
the same value. Source acquire/release synchronization,
source-to-machine preservation, and physical x86-TSO/Linux correspondence
remain separate proof obligations. See the [platform model](platform-model.md)
and [trust ledger](trust.md).
