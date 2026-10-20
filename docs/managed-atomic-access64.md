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
