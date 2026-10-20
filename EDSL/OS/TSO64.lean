/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Run
import EDSL.OS.TSO64.Access
import EDSL.OS.TSO64.Occurrences

/-!
Reusable checked fixed-world scheduler for the explicitly admitted Sequential
MOV/register/padding/RET and aligned scalar32/64 forms, plus the production
full64 LockedAdd64 family and current Atomics64 fetchAdd bridge. Source/base
aliases and source RSP inherit that family unchanged. All other instructions
fail closed. The default `ownedOnly` profile conservatively requires full RW
ordinary ownership for plain data access. Explicit `sharedCell` also admits
exact-address managed qword MOV loads/stores through current handle authority.
Read-only DATA-loan loads are not currently an API. RET has its separate
original caller loan and actual current stack read.

Only `issue tid af` and `drain tid` change a run. Setup attaches existing current
loans/tickets/handles. Collection observes a returned, quiescent caller without
releasing authority. There are no external writes, permission/mapping changes,
releases, transfers, enrollment/revocation or loan finishing during a run.
Each plain store consumes a per-worker sequence number only on successful
instruction execution; managed FIFO entries retain the full original authority
descriptor and occurrence. Publication reauthorizes the head at the current
world. Returning does not publish pending stores. Numerical queue integrity is
proved separately from authority and supplies no complete shared event history.
As for the underlying resource models, actor labels are logical principals and
copyable tickets are registry authority, not native authentication/linear tokens.

The concurrent ordinary profile is naturally aligned non-crossing scalar RAM;
unaligned forms fail closed. The long-mode/CET-disabled/multi-byte-NOP and
WB/translation/alias/environmental assumptions of Sequential and LockedAdd64
remain explicit environmental obligations. This core establishes neither a
frozen-function certificate nor linearizability, published x86-TSO equivalence,
physical LOCK, native Linux, ABI preservation, or source-language ordering.
-/
