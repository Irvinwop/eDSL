# Shared atomic handles and reservations

`EDSL.OS.Atomics` adds shared atomic authority over the existing ownership,
read-loan and XCHG models. An allocation owner can issue distinct stored handles
to several logical actors for the same four-byte word. Each exchange checks
the caller's actor against its handle and uses the handle's stored owner,
allocation ticket and address. The returned old word comes from current shared
cells, including replacements made by peers after handle issuance.

This is an implemented Lean resource contract. The
[mutable atomic-worker layer](atomic-workers.md) adds private contexts,
per-instruction dispatch and spawn/join over these handles. Lock protocols and
a concrete OS runtime remain future work. The separate read-worker module
retains its load/RET profile.

## Operations and interference

`State` wraps `Borrowing.State` with a monotone `nextHandle` frontier and stored
`Handle` records. A handle contains `owner`, `ticket`, `actor` and `address`.
While any handle remains, its entire allocation is reserved. Multiple handles
on one allocation must refer to the same owner/ticket/address; different actors
are allowed. Different allocations can reserve independent words.

| Operation | Checked behavior |
| --- | --- |
| `issue` | Check current owner/epoch, contained operand, aligned atomic-RAM support, accessible writable bytes, no conflicting read loan, compatible existing handles and fresh ID; install a handle for the selected actor |
| `authorize` | Require a stored handle with the caller's actor |
| `exchange` | Read current cells and perform the checked XCHG/OS-cell update at the stored address; retain every handle |
| `close` | Remove exactly the caller's authorized handle; retain the ID frontier |
| `mutate` | Reject targeted ordinary store, protection change, transfer or release on every reserved allocation; allow independently checked unrelated operations |
| `readBorrow` | Reject any ordinary read loan on a reserved allocation, including a disjoint subregion |
| `finishLoan` | Complete an existing ordinary loan through its stored borrower authority |

The implicit reservation ends when the last handle closes. Ordinary checked
stores, protection changes, transfer, release and new read loans may then be
possible again, subject to their existing contracts. Reissuing authority for
the same address creates a new handle ID. Copying a closed ID does not restore
its record or change the stored actor.

Ordinary read loans retain their original whole-allocation freeze semantics.
They cannot coexist with atomic handles on that allocation, in either creation
order. Code and return-stack loans can use separate allocations and retain
their bytes and permissions during exchanges.

## Invariants and checked results

`WellFormed` requires the underlying borrowing invariant, every live handle
below its frontier, current stored owner/ticket authority, a contained supported
writable operand, absence of ordinary readers on that allocation, and agreement
between handles sharing an allocation. Each successful operation preserves it.
Finite scans are complete under this explicit invariant; manually constructed
malformed states are not globally validated.

Named proof entry points:

- `issue_wellFormed`, `close_wellFormed`, `mutate_wellFormed`,
  `readBorrow_wellFormed`, `finishLoan_wellFormed`, `exchange_wellFormed` and
  `History.wellFormed` preserve the invariant.
- `mutate_reserved`, `readBorrow_reserved` and `issue_reader_excluded` state
  the exclusions for live reservations and ordinary loans.
- `History.advances` preserves every surviving handle's exact record and
  prevents old IDs from returning. `closed_for_history` proves permanent
  revocation after every later admitted finite history, including new issuance.
- `History.borrowing` projects every admitted operation into the original
  guarded borrowing history. `History.loan_stable` retains surviving loan cells
  and permissions across mixed issue/close/exchange/resource/loan operations.
- `exchange_sound` binds the current OS-cell update to `ExchangeTransition`.
  `exchange_step` proves the actual decoded XCHG produces the same old/new
  event, register state and projected final memory. `exchange32_updates_space`
  composes the exact MOV/XCHG/RET routine, singleton event trace, three-instruction
  count, termination and unique result with the handle-authorized OS update.
- `exchange_enabled` proves every well-formed authorized handle admits an
  exchange for every replacement word. This is an operation-existence result;
  it does not require or prove scheduler progress.

`ExchangeTrace` represents arbitrary finite exchange-only schedules at one
cell, retaining each actual actor, handle ID, stored handle and old/new words.
Its OS projection reuses the existing exchange-history proof. `chain` proves
each old return is the preceding new word, starting at an independently
observed initial value. `conservation` proves a permutation between the initial
cell plus all inserted words and the final cell plus all returned words,
counting duplicates. Replacement arguments may be arbitrary; no feedback from
an actor's earlier return is assumed.

This value-flow theorem concerns exchange-only traces. A mixed history that
closes every handle may admit an ordinary store before later exchanges, so it
cannot silently inherit the same chain. Extending value flow across mixed
histories needs a continuously surviving reservation or explicit framing of
every intervening operation. The invariant/revocation/loan-stability results
already cover all admitted mixed histories.

## Evidence and boundary

```sh
lake build EDSL.All edsl-certify edsl-certify-process
lake env lean -DwarningAsError=true tests/Atomics.lean
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL.All
```

Regressions cover both orders of two distinct actors, peer updates after handle
issuance, neighboring-word framing, wrong actors, conflicting cell addresses,
all targeted mutation kinds, multiple handles and final closure,
closed IDs after same-cell reacquisition, ordinary-loan conflicts in both
creation orders, unrelated allocations and read loans, stale owner epochs,
unsupported alignment and a denied final operand byte. A compiler-byte
composition check retains separate code/return-stack loans while one actor
changes the value before the other's actual MOV/XCHG/RET execution. Symbolic
witnesses exhibit well-formed exchange entries for every old and new 32-bit
word, and enabledness covers every replacement.

The existing owned compiler fixtures and eight-thread native token observations
continue to validate the selected machine behavior. There is no native handle
registry or thread-creation/join refinement in this milestone. Principal names
and IDs are constructible proof data, not authentication or linear capabilities.
Raw Borrowing/Ownership writes, ordinary machine accesses and unmanaged aliases
bypass this discipline and are excluded from its admitted histories. The
certificate CLI retains its machine contracts and does not infer handles.

The [aligned coherent-WB-RAM physical profile](atomic-exchange.md) still applies.
General x86 ordering, C/C++ memory-model preservation and concrete OS/hardware
conformance remain separate obligations. A reservation supplies no unconditional
reclamation or completion guarantee: a handle holder may never close it.

The mutable-worker layer now executes each MOV/XCHG/RET instruction against
current shared cells. Its captured old value survives peer exchanges through
join, and the lifecycle owns and revokes each worker's handle and code/stack
loans. Arbitrary successful dispatch-only schedules at one address have actual
event chaining and multiset conservation. See [its exact scope](atomic-workers.md)
for the distinction between schedule value flow and mixed-history result safety.
