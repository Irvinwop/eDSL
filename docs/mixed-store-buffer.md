# Mixed-width functional store buffers

`EDSL.X86.StoreBuffer.Mixed` provides one oldest-first queue of dword and qword
values at `Word` addresses. Publication uses the existing production
`writeDWordUnchecked` / `writeQWordUnchecked` functions. Per-store byte lookup
uses those same writes against empty memory; it has no independent slicing
table. A worker's functional `view` overlays its queue onto global memory.
`forward` selects the newest matching store separately for every byte, including
partial overlaps of different widths. `publishOldest` publishes the head only.

`view_read` equates the overlay byte with `forward buffer query` followed by
the global-memory fallback. `forward_enqueue` and `view_enqueue_read` state the
newest-store rule without requiring equal addresses or widths. `drain_view` and
`publishOldest_view` preserve the entire issuing worker's view when the oldest
store publishes. They impose no claim on a peer's intermediate observations.

`view_executable` and `view_writable` preserve the complete permission functions.
`Store.Disjoint` describes modular byte footprints. `view_frame`, `view_agrees`,
`view_readDataByte_frame`, `view_loadDWord_frame`, `view_loadQWord_frame`,
`view_readWord_frame` and `view_code` transport byte/region, DATA, stack and code
observations outside those footprints, including failed reads. The load frame
lemmas reuse the production congruence lemmas. `loadDWord_enqueue` and
`loadQWord_enqueue` reuse the production self-load proofs with their exact
`dwordAddressable` / `qwordAddressable` premises. `loadQWord_enqueue_frame` allows
subsequent independent writes.

`embedStore32` and `embed32` embed the existing four-byte store and queue.
`publish_embedStore32`, `byte_embedStore32`, `view_embed32`, `forward_embed32`
and `enqueue_embed32` prove exact equality with the existing operations for
arbitrary old stores, queues, memories and queries. These theorems have no
admission or nonoverlap premise: they include the old unchecked modular
semantics. Existing production interfaces are unchanged.

This is an unchecked functional byte-overlay layer, matching the role of
`X86.StoreBuffer`. Raw stores do not validate canonicality, nonwrapping operands,
alignment, accessibility, writability, fixed code, resource ownership or
synchronization. Scheduler/OS admission must establish those independently.
Unchecked writes can make absent bytes readable; permission functions are
unchanged. Self-forwarding through a checked load requires that production
load's addressability premise and grants no permission or atomicity admission.

There is no new actual TSO64 scheduler. The layer makes no claim of indivisibility
for arbitrary unaligned/mixed accesses, source atomic orders, refinement to the
published Owens/Sarkar/Sewell x86-TSO model, hardware conformance, whole-call
linearizability or frozen corpus certification. Unsupported architecture behavior
is not made safe by this layer. Corpus inputs, sources and compiler flags are
unchanged.

`tests/MixedStoreBuffer.lean` checks literal observations through production
`loadDWord`, `loadQWord`, `readWord`, byte reads, `fetchByte` and
checked store preflights. In particular, qword `0x1122334455667788` followed by
dword `0xaabbccdd` at offset two yields `0x1122aabbccdd7788`; reversing order,
shifting a qword, and retaining an older write's tail check distinct overlap
cases. FIFO observations distinguish peer global reads at all three publication
stages while retaining the issuer's own value. Other cases cover disjoint
writes, outside missing bytes, DATA versus STACK faults, high-byte permission
denial, executable-byte preservation and wrapped/noncanonical load rejection.
Literal expected results are independent of the byte-slicing implementation;
kernel reduction checks them without native evaluation or a solver.

Lean is pinned to 4.35.0. Targeted checks (each invocation holds the shared
build lock) are:

```sh
PATH=${HOME}/.elan/bin:$PATH LEAN_NUM_THREADS=1 flock /tmp/edsl-lean-build.lock lake build EDSL.X86.StoreBuffer.Mixed EDSL.Audit
PATH=${HOME}/.elan/bin:$PATH LEAN_NUM_THREADS=1 flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true tests/MixedStoreBuffer.lean
```

The suite runs `#audit_edsl`, which transitively permits only `propext`,
`Quot.sound` and `Classical.choice` for project declarations. Fresh kernel replay
additionally checks the stored test proof and all imports using
`leanchecker --fresh tests.MixedStoreBuffer` after writing its `.olean` to an
importable `tests/MixedStoreBuffer.olean` path. A compiled artifact alone does
not establish those separate validation results. Validation receipts bind
source and dependency hashes to the checks actually completed.
