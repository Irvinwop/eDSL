# Shared read loans and stable machine reads

`EDSL.OS.Borrowing` adds checked shared read loans over the existing ownership
registry. A loan names one live allocation ticket, lender, borrower and readable
subregion. Multiple overlapping loans are allowed. While any loan references an
allocation, **the entire allocation is frozen**: managed stores, permission
changes, transfer (including self-transfer) and release reject. This is an
explicit first policy; splitting, mutable borrows and synchronization-controlled
writes remain future work.

The implementation, validators and proofs are Lean 4. This is a sequential
logical resource discipline. Principal names, tickets and loan IDs are
constructible, copyable proof data. Raw machine instructions do not check them,
and the model does not authenticate runtime callers or enforce isolation.

## State and checked operations

`State` contains the ownership `resources`, a monotone `nextLoan` frontier and
an optional stored `Loan` for each natural ID. `WellFormed` requires ownership
well-formedness, every live loan ID below that frontier, and `ValidLoan` for
every live record. Validity requires the referenced allocation to retain the
lender and ticket epoch, a nonempty canonical nonwrapping loan region contained
in the allocation, and actual mapped readable cells throughout that region.
A loan does not assert any caller-supplied byte snapshot.

| API | Behavior |
| --- | --- |
| `empty resources` | Empty loan registry over a supplied ownership world; validity requires that world's invariant |
| `readBorrow state lender ticket borrower region` | Check allocation authority, valid contained range and every byte's readability; issue a fresh loan ID |
| `authorize state borrower id` | Look up a stored live record and check its borrower |
| `finishLoan state borrower id` | Authorize the stored record and remove only that ID; retain the frontier |
| `mutate state operation` | Check all live loans, then perform an existing ownership mutation and return any issued ticket |
| `loadWord state borrower id address` | Authorize the stored loan, check all four operand bytes inside it, then read the projected machine memory |

`Ownership.Mutation` packages allocate, adopt, transfer, release, protect and
store operations. `Mutation.run_step` connects its successful executions to the
existing ownership history; `run_wellFormed` preserves that invariant.
`run_preserves` proves exact allocation metadata and cell preservation for every
live allocation other than the named target. Fresh allocate/adopt have no
existing target and preserve all old registered allocations.

The mutation guard scans `[0,nextLoan)`. Its completeness relies on the explicit
`WellFormed` premise. Arbitrary malformed constructed states are not globally
validated. The guard runs before allocation authorization, so any operation
naming a borrowed allocation ID returns `borrowed` first, even with an invalid
epoch or owner. Underlying ownership failures otherwise remain explicit.

`readBorrow`, `finishLoan` and `mutate` return `Except Fault`; `loadWord` uses
`ReadFault` to distinguish authority failure, an operand outside the loan and
an underlying machine error. Failure returns no updated state. These functional
contracts do not establish Linux transactionality or concurrent atomicity.
`loadWord_exists` proves every contained word in a well-formed,
authorized loan has a successful read. Construction helpers such as `installLoan`
are pure functions; use checked operations or prove their conditions.

## Histories and binary composition

`Step` contains precisely successful borrow, finish and guarded mutation
operations. `History` is their arbitrary finite closure. Their preservation
proofs retain `WellFormed`. `Advances` proves the frontier never decreases,
old IDs cannot be reissued, and every surviving loan retains its stored record
and exact cells, including permissions. `History.loan_stable` needs only an
initially issued ID and endpoint liveness: an ID cannot disappear and return.

`finishLoan_revokes` establishes removal below the frontier. `Revoked.persists`
and `finished_for_history` prove permanent removal through every subsequent
admitted finite history. `Revoked.unauthorized` excludes authority for all
borrowers at that ID, including after new loans are issued to the same borrower.

`History.loadWord_stable` retains the value of a successful authorized word read
through any admitted history in which its loan remains live.
`History.buffer_stable` transports an independently established `X86.BufferAt`
snapshot across such a history, when the byte window lies inside the loan.
The initial snapshot must actually match memory. This supplies a buffer-stability
rule for later syscall/thread composition; it does not yet replace the standalone
write profile's buffer premise automatically.

`borrowed_load32_correct` combines checked read authority with the actual
`8b 07 c3` load/RET profile. It proves the loaded value, unique final state/count,
termination in two modeled instructions and no ordinary-step divergence.
Executable code, readable return stack and canonical return address remain
explicit premises at the execution state. `borrowed_load32_after_history` combines this binary contract with arbitrary
guarded histories and an initially successful read whose loan survives.
Borrowing freezes its data allocation;
it does not implicitly protect unrelated code or the caller's stack.

These results quantify **Borrowing histories**, not arbitrary Ownership histories,
raw cell replacement or unconstrained external writes. They establish sequential
composition under this discipline. The [managed read-worker scheduler](threads.md) now supplies a specific
load/RET lifecycle composition using three internal loans per worker. Broader
concurrent safety still needs interference semantics, mutable worker protocols
and an adequacy argument for concrete thread/runtime execution. Physical aliases, DMA/MMIO, stale raw pointer enforcement,
linear/fractional permissions and concrete OS implementation refinement remain
outside this claim. The certificate CLI does not infer loan registries.

## Evidence

```sh
lake build EDSL.All
lake env lean -DwarningAsError=true tests/Borrowing.lean
bash scripts/check-audit.sh
```

Owned synthetic regressions cover overlapping loans, the newest scan ID,
finishing only one of several loans, every frozen mutation kind, mutations to a
different word of the same allocation, wrong borrowers, double/stale completion,
later issuance, invalid/empty/outside ranges and a final unreadable byte.
All mutation kinds also succeed on disjoint allocations while borrowed data is
retained. Checked reads reject operands beyond the loan despite readable
neighbors. An adopted caller-space witness proves actual load execution for
every 32-bit value, and a symbolic theorem retains that value across every
admitted finite history with endpoint liveness. This adds no native runtime
enforcement or new compiler encoding support.
