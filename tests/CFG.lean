/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.CFGTransport
import EDSL.X86.Sequential.Execution
import EDSL.Audit

namespace EDSL.Tests.CFG
open X86 Sequential

-- Two independent loops sum [RDI] and then [RDX]. The second count is RCX,
-- which the initialization must retain. This is actual final GCC13 code.
def pairBytes : List Byte := [0x31, 0xc0, 0x48, 0x85, 0xf6, 0x74, 0x0b,
  0x03, 0x07, 0x48, 0xff, 0xce, 0x48, 0x83, 0xc7, 0x04, 0xeb, 0xf0,
  0x48, 0x85, 0xc9, 0x74, 0x0b, 0x03, 0x02, 0x48, 0xff, 0xc9,
  0x48, 0x83, 0xc2, 0x04, 0xeb, 0xf0, 0xc3]

def pairGraph : Sequential.CFG.Graph := (Sequential.CFG.discover pairBytes).getD ⟨[], 0⟩

example : Sequential.CFG.check pairBytes pairGraph = true := by decide
example : Sequential.CFG.Valid pairBytes pairGraph := Sequential.CFG.check_sound (by decide)

-- The taken branch reaches the SECOND RET. Truncating at the first RET loses
-- a reachable exit and must not count as a complete closed graph.
def earlyBytes : List Byte := [0x31, 0xc0, 0x48, 0x85, 0xf6, 0x74, 0x06,
  0xb8, 1, 0, 0, 0, 0xc3, 0xc3]
def earlyGraph : Sequential.CFG.Graph := (Sequential.CFG.discover earlyBytes).getD ⟨[], 0⟩

example : Sequential.CFG.check earlyBytes earlyGraph = true := by decide
example : Sequential.CFG.analyze (earlyBytes.take 13) = .error .invalidGraph := by rfl

-- Omitting a loop-header cutpoint leaves a real cycle in the purported
-- acyclic interior. Entry remains a cutpoint, isolating the depth obligation.
def missingCut : Sequential.CFG.Graph := { pairGraph with nodes := pairGraph.nodes.map fun node =>
  { node with cutpoint := decide (node.offset = 0) } }
example : Sequential.CFG.check pairBytes missingCut = false := by decide

-- A claimed instruction with the same length cannot override actual bytes.
def forgedInstruction : Sequential.CFG.Graph := { pairGraph with nodes := pairGraph.nodes.map fun node =>
  if node.offset = 12 then { node with instruction := .addImm64 .rdi 8 } else node }
example : Sequential.CFG.check pairBytes forgedInstruction = false := by decide

-- A real branch into the middle of JMP's displacement and a branch outside
-- the supplied window both decode but fail edge closure.
def middleTarget : List Byte := pairBytes.set 6 0x0a
def outsideTarget : List Byte := pairBytes.set 6 0x7f
example : Sequential.CFG.analyze middleTarget = .error .invalidGraph := by rfl
example : Sequential.CFG.analyze outsideTarget = .error .invalidGraph := by rfl

-- Wrong-depth certificate data must not disable the checked decrease test.
def flatDepth : Sequential.CFG.Graph := { earlyGraph with nodes := earlyGraph.nodes.map fun node =>
  { node with depth := 0 } }
example : Sequential.CFG.check earlyBytes flatDepth = false := by decide

example : Sequential.CFG.analyze [] = .error .empty := by rfl
example : Sequential.CFG.analyze [0x48, 0x85] =
    .error (.decode 0 (.inaccessibleInstruction 2)) := by rfl
example : Sequential.CFG.analyze [0x89, 0x37, 0xc3] = .error (.unsupportedInstruction 0) := by rfl
example : Sequential.CFG.analyze [0x87, 0x07, 0xc3] = .error (.unsupportedInstruction 0) := by rfl
example : Sequential.CFG.analyze [0x0f, 0x05] = .error (.unsupportedInstruction 0) := by rfl

-- A cutpoint self-loop is a valid finite CFG. It cannot obtain a totality
-- theorem without the separate dynamic decrease VC: its actual trace diverges.
def spinBytes : List Byte := [0xeb, 0xfe]
def spinGraph : Sequential.CFG.Graph := (Sequential.CFG.discover spinBytes).getD ⟨[], 0⟩
example : Sequential.CFG.check spinBytes spinGraph = true := by decide

def spinMemory : Memory where
  read address := if 4096 ≤ address.toNat ∧ address.toNat < 4098 then
    spinBytes[address.toNat - 4096]? else none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4098)

def spinState : State := ⟨fun _ => 0, 4096, 0, spinMemory⟩

theorem spin_step (af : Bool) :
    Sequential.step af spinState = .ok ⟨.next spinState, []⟩ := by rfl

theorem spin_diverges (choices : Choices) : DivergesWith choices spinState := by
  refine ⟨fun _ => spinState, rfl, ?_⟩
  intro index
  exact ⟨[], .next spinState, spin_step (choices index), rfl⟩

end EDSL.Tests.CFG

#audit_edsl
