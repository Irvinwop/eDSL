/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import EDSL.Audit

namespace EDSL.Tests.ManagedOverlay64
open X86 OS.TSO64 EDSL.Tests.TSO64

/-- Two contexts of one owner share ordinary RAM. Context 0 keeps a DWORD
pending while context 1 publishes a different QWORD into that same region.
The actual load must merge its own four bytes with the current peer bytes. -/
def observe (state : Scheduler) :=
  (loadQWord (published state.world) 131072,
    state.workers[0]?.map (fun worker =>
      (worker.context.registers .rbx, worker.pending.length, worker.phase)),
    (collect state 0).isOk)

def interleaving := do
  -- 0: MOV [RDX],ESI; MOV RBX,[RDX]; RET.
  -- 8: MOV [RDX],RSI; RET.
  let ready ← (fixture 0x9090c31a8b483289 0x90909090c3328948 19).mapError OS.TSO64.Fault.os
  let caller ← (OS.Atomics64.readBorrow ready.checked.world 22 ⟨4,0⟩ 11 ⟨327680,8⟩).mapError OS.TSO64.Fault.os
  let first ← attach ⟨caller.1, []⟩ 11
    (context 262144 131072 0x1111222255667788 0)
    ready.codeA ready.callerA [ready.dataA] [ready.atomicA]
  let second ← attach first 11
    { context 327680 131072 0xaabbccdd11223344 0 with rip := 393224 }
    ready.codeA caller.2 [ready.dataA] [ready.atomicA]
  let loaded ← schedule second
    [.issue 0 false, .issue 1 false, .drain 1, .issue 0 false,
      .issue 0 false, .issue 1 false]
  let published ← schedule loaded.1 [.drain 0]
  return (observe loaded.1, observe published.1,
    (loaded.2 ++ published.2).map Observation.retired)

-- A cached shared-memory snapshot produces the wrong high half. Ignoring
-- forwarding produces the peer's low half; prematurely publishing the store
-- changes the first global read. RET alone must not permit collection.
example : interleaving = .ok
    ((.ok 0xaabbccdd11223344, some (0xaabbccdd55667788, 1, .returned), false),
      (.ok 0xaabbccdd55667788, some (0xaabbccdd55667788, 0, .returned), true),
      [1,1,0,1,1,1,0]) := by rfl

end EDSL.Tests.ManagedOverlay64

#audit_edsl
