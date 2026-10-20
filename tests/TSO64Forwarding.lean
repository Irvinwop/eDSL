/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import EDSL.Audit

namespace EDSL.Tests.TSO64
open X86 OS.TSO64

def forwardingActions : List Action :=
  [.issue 0 false, .issue 1 false, .issue 0 true, .issue 1 true,
    .issue 0 false, .issue 0 false, .issue 0 false]

def forwarding (suffix : List Action) :=
  run 0x1a8b480189328948 0x9090909090c30a8b 19 0x1122334455667788 0x99aabbccddeeff00
    0xdeadbeef (forwardingActions ++ suffix)

def forwardingView (result : Scheduler × List Observation) :=
  (loadQWord (published result.1.world) 131072,
    result.1.workers[0]?.map (fun worker => loadQWord (localCPU result.1 worker).memory 131072),
    workerView result.1 0, workerView result.1 1, collect result.1 0,
    result.2.map Observation.retired)

-- Newest-byte forwarding merges an overlapping DWORD with the older qword.
-- The real load writes RBX with the mixed full64 value; neither store has
-- reached RAM. RET is observable while both publication obligations remain.
example : (forwarding []).map forwardingView = .ok
    (.ok 0, some (.ok 0xdeadbeef55667788),
      some ([0xdeadbeef,0xdeadbeef55667788,65536,0x1122334455667788,262152],0x7000,0x200202,.returned,2),
      some ([0xdeadbeef,0x8877665544332211,65536,0x99aabbccddeeff00,327680],393221,0x200202,.running,2),
      .error .resource, [1,1,1,1,1,1,1]) := by rfl

-- FIFO drains the full-width head first. The private view retains the later
-- DWORD overlay while global RAM exposes the older qword exactly.
example : (forwarding [.drain 0]).map forwardingView = .ok
    (.ok 0x1122334455667788, some (.ok 0xdeadbeef55667788),
      some ([0xdeadbeef,0xdeadbeef55667788,65536,0x1122334455667788,262152],0x7000,0x200202,.returned,1),
      some ([0xdeadbeef,0x8877665544332211,65536,0x99aabbccddeeff00,327680],393221,0x200202,.running,2),
      .error .resource, [1,1,1,1,1,1,1,0]) := by rfl

-- The second drain publishes precisely four bytes and enables collection.
-- The returned context and peer queue survive both publications unchanged.
example : (forwarding [.drain 0, .drain 0]).map forwardingView = .ok
    (.ok 0xdeadbeef55667788, some (.ok 0xdeadbeef55667788),
      some ([0xdeadbeef,0xdeadbeef55667788,65536,0x1122334455667788,262152],0x7000,0x200202,.returned,0),
      some ([0xdeadbeef,0x8877665544332211,65536,0x99aabbccddeeff00,327680],393221,0x200202,.running,2),
      .ok 0xdeadbeef, [1,1,1,1,1,1,1,0,0]) := by rfl

-- Independent byte origins: own pending bytes override only their footprint;
-- a later CURRENT global qword supplies the other four bytes of this load.
def mixedCurrent : Memory :=
  StoreBuffer.Mixed.view
    (writeQWordUnchecked (writeQWordUnchecked
      { read := fun _ => none, executable := fun _ => false } 4096 0x0102030405060708)
      4096 0xaabbccdd11223344)
    [⟨4100,.dword 0x8899aabb⟩]

example : loadQWord mixedCurrent 4096 = .ok 0x8899aabb11223344 := by rfl

-- Reverse overlap order: the newest qword replaces all bytes of an older
-- DWORD, rather than retaining a stale 32-bit overlay after it.
example : loadQWord (StoreBuffer.Mixed.view mixedCurrent
    [⟨4096,.dword 0xffffffff⟩,⟨4096,.qword 0x123456789abcdef0⟩]) 4096 =
    .ok 0x123456789abcdef0 := by rfl

end EDSL.Tests.TSO64

#audit_edsl
