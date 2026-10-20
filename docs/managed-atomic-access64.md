# Managed shared-cell loads and publication

[`EDSL.OS.AtomicAccess64`](../EDSL/OS/AtomicAccess64.lean) provides reusable
full64 load and publication operations for the existing managed-cell resource
model. It is a foundation for shared-memory execution contracts. It does not
add a compiler-corpus certificate or extend the buffered scheduler.

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
needed for integration with that instruction engine:

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

This is a reusable policy library, not yet the scheduler's managed MOV API.
The instruction engine still needs profile threading, mixed-entry invariants,
derived whole-qword compatibility and a shared history. A per-worker sequence
number must be paired with the scheduler thread identifier; neither an arbitrary
nonempty initial queue nor its ordering invariant establishes prior issue events
or a global reads-from relation.

`publishStore` is a shared-memory publication operation. A buffered instruction
may issue a store and return before that store publishes. The existing
[managed scheduler](managed-fetch-add64.md) still excludes ordinary access to
registered atomic allocations; integrating these new operations requires
checked FIFO entries, reauthorization at drain, whole-word load provenance and
an extended history projection.

The typed events retain checked actor, handle, cell, address and value. A value
alone cannot identify the write a load observed: separate writes can store
the same value. Reads-from identities, source acquire/release synchronization,
source-to-machine preservation, and physical x86-TSO/Linux correspondence
remain separate proof obligations. See the [platform model](platform-model.md)
and [trust ledger](trust.md).
