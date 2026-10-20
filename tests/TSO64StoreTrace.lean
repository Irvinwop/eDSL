/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64PublishedWriters
import EDSL.OS.TSO64.C23Projection.StoreTrace
import tests.TSO64SharedCells
import tests.TSO64StoreIdentities
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.TSO64StoreTrace
open X86 OS.TSO64 OS.TSO64.C23Projection

/-- Summarize complete computed stamps for independent literal comparisons.
Two identical causes remain separate observations when their positions differ. -/
def writeSummary (stamp : PublishedHistory.Stamp) : Nat × Nat × Nat × Option Nat × Word :=
  match stamp.cause with
  | .buffered tid _ value occurrence => (stamp.position, tid, 0, some occurrence, value)
  | .rmw tid event => (stamp.position, tid, 1, none, event.arithmetic.event.after)

/-- Actual MOV-store, blocked LOCK, publication, two zero-delta RMWs and RET.
Only the three actual writes appear; blocked attempts and RET still consume
positions. The store issue itself is not a publication. -/
def equalWriteEvents : Except Fault
    (List (Nat × Nat × Nat × Option Nat × Word) × Except Error Word) := do
  let initial ← TSO64PublishedWriters.start
  let result ← schedule initial [.issue 0 false, .issue 0 false, .drain 0,
    .issue 0 false, .issue 0 true, .issue 0 false] .sharedCell
  pure ((writes 20 result.2).map writeSummary,
    loadQWord (published result.1.world) 65536)

/-- Equal words and identical zero-RMW event records do not erase writes.
The explicit offset counts every original scheduler action, including blocking. -/
theorem unchanged_writes_retain_all_original_positions : equalWriteEvents = .ok
    ([(22, 0, 0, some 0, 0), (23, 0, 1, none, 0), (24, 0, 1, none, 0)], .ok 0) := by rfl

/-- Issue metadata comes from actual admissions. Ordinary stores consume issue
numbers too, although their entries do not retain a managed occurrence. -/
def issueSummary (issue : StoreHistory.Trace.Issue) :
    Nat × Nat × Option Nat × StoreBuffer.Mixed.Value :=
  match issue.entry with
  | .ordinary _ store => (issue.position, issue.tid, none, store.value)
  | .managed _ value occurrence => (issue.position, issue.tid, some occurrence, .qword value)

def scannedBlocked : Except Fault
    (List (Nat × Nat × Option Nat × StoreBuffer.Mixed.Value) ×
      List (Nat × Nat × Nat × Option Nat × Word)) := do
  let initial ← TSO64PublishedWriters.start
  let result ← StoreHistory.Trace.scan initial [.issue 0 false, .issue 0 false, .drain 0,
    .issue 0 false, .issue 0 true, .issue 0 false] .sharedCell 20
  pure (result.issues.map issueSummary, (writes 20 result.observations).map writeSummary)

/-- The original store is captured at issue20, its publication at22. Blocked
LOCK and later real RMWs do not become extra plain-store issues. -/
theorem scanner_separates_issue_from_publication_and_rmw : scannedBlocked = .ok
    ([(20, 0, some 0, .qword 0)],
      [(22, 0, 0, some 0, 0), (23, 0, 1, none, 0), (24, 0, 1, none, 0)]) := by rfl

/-- Bytes: MOV [RDX],RAX; MOV [RDI],RSI; RET. The first write has ordinary
ownership; the second has managed authority. The queue contains both kinds. -/
def mixedStart : Except Fault OS.TSO64.State :=
  TSO64SharedCells.start 0x00c3378948028948 0 0 7 0 0 0

def scannedMixed : Except Fault
    (List (Nat × Nat × Option Nat × StoreBuffer.Mixed.Value) ×
      List (Nat × Nat × Nat × Option Nat × Word) × Except Error Word × Except Error Word) := do
  let initial ← mixedStart
  let result ← StoreHistory.Trace.scan initial
    [.issue 0 false, .issue 0 true, .drain 0, .drain 0, .issue 0 false] .sharedCell 40
  pure (result.issues.map issueSummary, (writes 40 result.observations).map writeSummary,
    loadQWord (published result.state.world) 131072,
    loadQWord (published result.state.world) 65536)

/-- Capturing only managed instructions would omit the first issue, and
allocating from pending managed IDs would assign the second issue the wrong ID.
Ordinary publication changes owned memory but is not a managed-cell write. -/
theorem scanner_covers_mixed_authority_and_counter_gaps : scannedMixed = .ok
    ([(40, 0, none, .qword 5), (41, 0, some 1, .qword 7)],
      [(43, 0, 0, some 1, 7)], .ok 5, .ok 7) := by rfl

def deniedMixed : Except Fault Nat := do
  let initial ← mixedStart
  let result ← StoreHistory.Trace.scan initial [.issue 0 false, .issue 0 false] .ownedOnly 40
  pure result.issues.length

/-- An earlier ordinary issue does not let instrumentation swallow a later
managed-policy fault or return a successful truncated annotation list. -/
theorem scanner_preserves_exact_first_policy_fault : deniedMixed = .error .noGrant := by rfl

/-- Peer FIFOs independently reuse local occurrence numbers. The scanner must
retain their distinct tids even when all descriptors point at the same cell
and every payload is zero. Returns occur before the final drains. -/
def scannedPeers : Except Fault
    (List (Nat × Nat × Option Nat × StoreBuffer.Mixed.Value) ×
      List (Nat × Nat × Nat × Option Nat × Word)) := do
  let initial ← TSO64StoreIdentities.start
  let result ← StoreHistory.Trace.scan initial [.issue 0 false, .drain 0,
    .issue 1 false, .issue 0 true, .drain 1, .issue 0 false, .drain 0,
    .issue 1 true, .issue 1 false, .drain 1] .sharedCell 60
  pure (result.issues.map issueSummary, (writes 60 result.observations).map writeSummary)

theorem scanner_keeps_equal_occurrences_at_different_threads : scannedPeers = .ok
    ([(60, 0, some 0, .qword 0), (62, 1, some 0, .qword 0),
      (63, 0, some 1, .qword 0), (67, 1, some 1, .qword 0)],
      [(61, 0, 0, some 0, 0), (64, 1, 0, some 0, 0),
        (66, 0, 0, some 1, 0), (69, 1, 0, some 1, 0)]) := by rfl

end EDSL.Tests.TSO64StoreTrace

#print axioms EDSL.OS.TSO64.C23Projection.mem_writes_iff
#print axioms EDSL.OS.TSO64.C23Projection.writes_ordered
#print axioms EDSL.OS.TSO64.C23Projection.writes_origin
#print axioms EDSL.OS.TSO64.StoreHistory.IssuedAt.managed_drain_exists_unique
#print axioms EDSL.OS.TSO64.StoreHistory.Trace.scan_certificate
#print axioms EDSL.OS.TSO64.StoreHistory.Trace.scan_error_iff
#print axioms EDSL.OS.TSO64.C23Projection.scan_issue_published_once
#print axioms EDSL.OS.TSO64.C23Projection.scan_publication_origin
#audit_edsl
