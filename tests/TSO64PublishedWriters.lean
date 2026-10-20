/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import EDSL.OS.TSO64
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.TSO64PublishedWriters
open X86 OS.TSO64

/-- MOV [RDI],RSI; LOCK XADD [RDI],RAX; LOCK XADD [RDI],RAX; RET.
Both actors start with zero operands and current handles. Every write leaves
RAM unchanged, so writer identity cannot be inferred from value changes. -/
def start : Except OS.TSO64.Fault OS.TSO64.State := do
  let ready ← (TSO64.fixture 0x07c10f48f0378948 0x0000c307c10f48f0 0).mapError Fault.os
  let one ← attach ⟨ready.checked.world, []⟩ 11 (TSO64.context 262144 131072 0 0)
    ready.codeA ready.callerA [ready.dataA] [ready.atomicA]
  attach one 12 (TSO64.context 327680 196608 0 0)
    ready.codeB ready.callerB [ready.dataB] [ready.atomicB]

def summary (observations : List Observation) : Option (Nat × Nat × Nat × Option Nat × Word) := do
  let stamp ← PublishedHistory.after 0 observations PublishedHistory.empty ⟨0⟩
  match stamp.cause with
  | .buffered tid _ value occurrence => pure (stamp.position, tid, 0, some occurrence, value)
  | .rmw tid event => pure (stamp.position, tid, 1, none, event.arithmetic.event.after)

def unchangedWrites : Except OS.TSO64.Fault
    (List (Option (Nat × Nat × Nat × Option Nat × Word)) × Except Error Word × Bool × Bool) := do
  let initial ← start
  let issued ← schedule initial [.issue 0 false, .issue 1 false] .sharedCell
  let first ← step issued.1 (.drain 0) .sharedCell
  let second ← step first.1 (.drain 1) .sharedCell
  let rmwOne ← step second.1 (.issue 0 false) .sharedCell
  let rmwTwo ← step rmwOne.1 (.issue 0 false) .sharedCell
  let returned ← step rmwTwo.1 (.issue 0 false) .sharedCell
  let a := issued.2 ++ [first.2]
  let b := a ++ [second.2]
  let c := b ++ [rmwOne.2]
  let d := c ++ [rmwTwo.2]
  let e := d ++ [returned.2]
  pure ([summary issued.2, summary a, summary b, summary c, summary d, summary e],
    loadQWord (published returned.1.world) 65536,
    decide (rmwOne.2 = rmwTwo.2),
    decide (PublishedHistory.after 0 c PublishedHistory.empty ⟨0⟩ =
      PublishedHistory.after 0 d PublishedHistory.empty ⟨0⟩))

/-- Real equal-valued publications change the last writer's thread; identical
zero-RMW events change its global position. RET preserves the last writer, and
issuing a buffered store alone supplies no published writer. -/
theorem actual_unchanged_writes_keep_distinct_origins : unchangedWrites = .ok
    ([none, some (2, 0, 0, some 0, 0), some (3, 1, 0, some 0, 0),
      some (4, 0, 1, none, 0), some (5, 0, 1, none, 0), some (5, 0, 1, none, 0)],
      .ok 0, true, false) := by rfl

end EDSL.Tests.TSO64PublishedWriters

#print axioms EDSL.OS.TSO64.PublishedHistory.schedule_read
#print axioms EDSL.OS.TSO64.PublishedHistory.published_read_origin
#print axioms EDSL.OS.TSO64.PublishedHistory.newest_write_at
#print axioms EDSL.OS.TSO64.PublishedHistory.loadMem64_origin
#print axioms EDSL.OS.TSO64.PublishedHistory.WriteAt.buffered_origin
#audit_edsl
