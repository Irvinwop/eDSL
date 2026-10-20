/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import EDSL.Audit

namespace EDSL.Tests.TSO64
open X86 OS.TSO64

/-- Two different contexts of the same logical owner may use the same ordinary
allocation. Each still has its own ORIGINAL caller loan and private FIFO. -/
def sharedOwner := do
  let ready ← (fixture 0x90c31a8b48328948 0x9090909090909090 19).mapError OS.TSO64.Fault.os
  let caller ← (OS.Atomics64.readBorrow ready.checked.world 22 ⟨4,0⟩ 11 ⟨327680,8⟩).mapError OS.TSO64.Fault.os
  let first ← attach ⟨caller.1, []⟩ 11 (context 262144 131072 0x1122334455667788 0)
    ready.codeA ready.callerA [ready.dataA] [ready.atomicA]
  let second ← attach first 11 (context 327680 131072 0xaabbccddeeff0011 0)
    ready.codeA caller.2 [ready.dataA] [ready.atomicA]
  let result ← schedule second [.issue 0 false, .issue 1 false, .drain 0, .drain 1,
    .issue 0 true, .issue 1 false, .issue 0 false, .issue 1 false]
  pure (loadQWord (published result.1.world) 131072,
    workerView result.1 0, workerView result.1 1, result.2.map Observation.retired)

-- Context 0's later load observes peer publication AFTER context 0's own
-- drain; a spawn-time or previous-instruction RAM snapshot returns the wrong
-- full64 value. Both RETs must leave the latest published RAM intact.
example : sharedOwner = .ok
    (.ok 0xaabbccddeeff0011,
      some ([0,0xaabbccddeeff0011,65536,0x1122334455667788,262152],0x7000,0x200202,.returned,0),
      some ([0,0xaabbccddeeff0011,65536,0xaabbccddeeff0011,327688],0x8000,0x200202,.returned,0),
      [1,1,0,0,1,1,1,1]) := by rfl

-- Actual decoded base/source alias: each operand is captured before the
-- source register changes. RSI does not supply either delta.
example : (run 0x9090c33fc10f48f0 0x9090909090909090 0x11223344ffff0000 99 123 0
    [.issue 0 false, .issue 1 true, .issue 0 false, .issue 1 false]).map
    (fun result => (events result.2, workerView result.1 0, workerView result.1 1,
      loadQWord (published result.1.world) 65536)) = .ok
    ([(0,65536,0x11223344ffff0000,0x1122334500000000),
      (1,65536,0x1122334500000000,0x1122334500010000)],
      some ([0,0x8877665544332211,0x11223344ffff0000,99,262152],0x7000,0x200206,.returned,0),
      some ([0,0x8877665544332211,0x1122334500000000,123,327688],0x8000,0x200206,.returned,0),
      .ok 0x1122334500010000) := by rfl

example : (run 0x9090c327c10f48f0 0x9090909090909090 131072 1 2 0 [.issue 0 false]).map
    (fun result => (events result.2, workerView result.1 0,
      OS.Borrowing.loadWord64 result.1.world.legacy.shared 11 0 262144,
      loadQWord (published result.1.world) 65536)) = .ok
    ([(0,262144,131072,393216)],
      some ([0,0x8877665544332211,65536,1,131072],393221,0x200206,.running,0),
      .ok 0x7000, .ok 393216) := by rfl

end EDSL.Tests.TSO64

#audit_edsl
