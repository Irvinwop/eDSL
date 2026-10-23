/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Run
import EDSL.OS.TSO64.Access
import EDSL.OS.TSO64.Occurrences
import EDSL.OS.TSO64.ReadHistory
import EDSL.OS.TSO64.PublishedHistory
import EDSL.OS.TSO64.PublishedOrder
import EDSL.OS.TSO64.PendingViews
import EDSL.OS.TSO64.ExecutionViews
import EDSL.OS.TSO64.WordProjection
import EDSL.OS.TSO64.C23Projection.Origins
import EDSL.OS.TSO64.C23Projection.StoreTrace
import EDSL.OS.TSO64.C23Projection.AtomicTrace
import EDSL.OS.TSO64.Return
import EDSL.OS.TSO64.DrainClosure

/-!
Reusable checked fixed-world scheduler for the Sequential Bool-choice scalar
and control-flow profile, including padding/RET and admitted aligned scalar32/64
data access, plus the production full64 LockedAdd64 family and current Atomics64
fetchAdd bridge. Legacy DWORD atomics, syscalls, independently undefined-flag
vector forms and DATA1 reads fail closed. Source/base aliases and source RSP
inherit the locked family unchanged. The default `ownedOnly` profile conservatively requires full RW
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
world. Returning does not publish pending stores. StoreHistory connects retained
and published tags to actual issues or an explicit initial queue boundary;
ReadHistory connects forwarded MOV values to those exact tagged origins.
PublishedHistory identifies each cell's newest actual publication or RMW by
global schedule position and thread, and connects it to actual managed loads.
Initial RAM and initial pending queues retain explicit provenance boundaries.
Source memory ordering and physical machine correspondence remain separate.
As for the underlying resource models, actor labels are logical principals and
copyable tickets are registry authority, not native authentication/linear tokens.

The concurrent ordinary profile is naturally aligned non-crossing scalar RAM;
unaligned forms fail closed. The long-mode/CET-disabled/multi-byte-NOP and
WB/translation/alias/environmental assumptions of Sequential and LockedAdd64
remain explicit environmental obligations. This core establishes neither a
frozen-function certificate nor linearizability, published x86-TSO equivalence,
physical LOCK, native Linux, ABI preservation, or source-language ordering.
-/
