/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import EDSL.Audit

namespace EDSL.Tests.TSO64
open X86 OS.TSO64

def pairView (result : Scheduler × List Observation) :=
  (events result.2, loadQWord (published result.1.world) 65536,
    loadQWord (published result.1.world) 65544, workerView result.1 0, workerView result.1 1,
    collect result.1 0, collect result.1 1, result.2.map Observation.retired)

/-- MOVs and RMWs of TWO actual contexts interleave; the second response is
the current full64 old value after a carry across bit31. RET of context 0
occurs between the two RMWs and must not overwrite shared RAM. -/
example : (run 0x07c10f48f0f08948 0x90909090909090c3 0x11223344ffffffff 1 0x100000001 0
    [.issue 0 false, .issue 1 true, .issue 0 false, .issue 0 false,
      .issue 1 false, .issue 1 false]).map pairView = .ok
    ([(0,1,0x11223344ffffffff,0x1122334500000000),
      (1,0x100000001,0x1122334500000000,0x1122334600000001)],
      .ok 0x1122334600000001, .ok 0xabcdef0123456789,
      some ([0x11223344ffffffff,0x8877665544332211,65536,1,262152],0x7000,0x200216,.returned,0),
      some ([0x1122334500000000,0x8877665544332211,65536,0x100000001,327688],0x8000,0x200202,.returned,0),
      .ok 0x11223344ffffffff, .ok 0x1122334500000000, [1,1,1,1,1,1]) := by rfl

-- The default-like prefix variant exercises the ordinary ENDBR dispatch too.
example : (run 0xf0f08948fa1e0ff3 0x909090c307c10f48 0x11223344ffffffff 1 0x100000001 0
    [.issue 0 false, .issue 1 true, .issue 0 true, .issue 1 false,
      .issue 0 false, .issue 1 true, .issue 0 false, .issue 1 false]).map
      (fun result => (events result.2, collect result.1 0, collect result.1 1,
        loadQWord (published result.1.world) 65536)) = .ok
    ([(0,1,0x11223344ffffffff,0x1122334500000000),
      (1,0x100000001,0x1122334500000000,0x1122334600000001)],
      .ok 0x11223344ffffffff, .ok 0x1122334500000000, .ok 0x1122334600000001) := by rfl

def bufferedActions : List Action :=
  [.issue 0 false, .issue 1 false, .issue 0 false, .issue 1 false,
    .issue 0 false, .drain 0, .issue 0 false, .issue 1 false, .issue 0 false]

-- Both workers have pending ordinary writes. Own write blocks, drain retires
-- zero, and context 0's RMW succeeds while context 1's FIFO is still nonempty.
example : (run 0x48f0f08948328948 0x90909090c307c10f 0x11223344ffffffff 1 2 0 bufferedActions).map
    (fun result => (events result.2, result.2.map Observation.retired,
      loadQWord (published result.1.world) 131072, loadQWord (published result.1.world) 196608,
      workerView result.1 1, collect result.1 0, collect result.1 1)) = .ok
    ([(0,1,0x11223344ffffffff,0x1122334500000000)], [1,1,1,1,0,0,1,0,1], .ok 1, .ok 0,
      some ([2,0x8877665544332211,65536,2,327680],393222,0x200202,.running,1),
      .ok 0x11223344ffffffff, .error .resource) := by rfl

-- Peer publication and RMW preserve the already returned context's old64
-- response, caller stack, code, and its independently retained resources.
example : (run 0x48f0f08948328948 0x90909090c307c10f 0x11223344ffffffff 1 2 0
    (bufferedActions ++ [.drain 1, .issue 1 false, .issue 1 false])).map
    (fun result => (events result.2, collect result.1 0, collect result.1 1,
      loadQWord (published result.1.world) 65536,
      loadQWord (published result.1.world) 196608,
      readWord (published result.1.world) 262144,
      loadQWord (published result.1.world) 393216)) = .ok
    ([(0,1,0x11223344ffffffff,0x1122334500000000), (1,2,0x1122334500000000,0x1122334500000002)],
      .ok 0x11223344ffffffff, .ok 0x1122334500000000, .ok 0x1122334500000002,
      .ok 2, .ok 0x7000, .ok 0x48f0f08948328948) := by rfl

end EDSL.Tests.TSO64

#audit_edsl
