/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.StructuralCFG
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.StructuralCFG
open X86 Sequential

/-!
These checks exercise the shared decoder and structural checker on owned literal
bytes. They establish structure and decoding only: no lock behavior, termination,
security property, execution result, or native acceptance is claimed.
-/

namespace SpinlockAcquire

-- Frozen Clang c_spinlock_acquire window: b801000000870785c075f5c3.
-- MOV EAX,1; XCHG [RDI],EAX; TEST EAX,EAX; JNE -11; RET.
def bytes : List Byte :=
  [0xb8, 0x01, 0x00, 0x00, 0x00, 0x87, 0x07, 0x85, 0xc0, 0x75, 0xf5, 0xc3]

def graph : CFG.Graph := ⟨[
  ⟨0, .legacy (.mov32 .rax 1), true, 4⟩,
  ⟨5, .legacy .exchangeEaxRdi, false, 3⟩,
  ⟨7, .test32 .rax .rax false, false, 2⟩,
  ⟨9, .legacy (.jnz 0xf5), false, 1⟩,
  ⟨11, .legacy .ret, false, 0⟩], 4⟩

-- Expected constructors come from the byte encodings, independently of graph
-- annotations. In particular, the memory XCHG must retain its legacy effect.
theorem decoded :
    Sequential.decodeAt (codeState bytes 0) = .ok (.legacy (.mov32 .rax 1)) ∧
    Sequential.decodeAt (codeState bytes 5) = .ok (.legacy .exchangeEaxRdi) ∧
    Sequential.decodeAt (codeState bytes 7) = .ok (.test32 .rax .rax false) ∧
    Sequential.decodeAt (codeState bytes 9) = .ok (.legacy (.jnz 0xf5)) ∧
    Sequential.decodeAt (codeState bytes 11) = .ok (.legacy .ret) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- The production signed relative-target calculation must reach the entry.
theorem backedge : graph.Edge ⟨3, by decide +kernel⟩ ⟨0, by decide +kernel⟩ := by
  decide +kernel

theorem checked : CFG.Structural.check bytes graph = true := by decide +kernel

theorem valid : CFG.Structural.Valid bytes graph := CFG.Structural.check_sound checked

-- Structural decoding transports to actual current executable memory without
-- adding any claim about the behavior of the authenticated XCHG.
theorem exchange_decoded {memory : Memory} {base : Word}
    (code : CodeAt memory base bytes) (state : State)
    (currentMemory : state.memory = memory) (currentPC : state.rip = base + 5) :
    Sequential.decodeAt state = .ok (.legacy .exchangeEaxRdi) :=
  valid.decoded code ⟨1, by decide +kernel⟩ state currentMemory currentPC

-- The existing consumer must still reject this real memory effect.
theorem readOnly_rejected : CFG.check bytes graph = false := by decide +kernel

-- Mutate the actual JNE operand to -10, targeting byte +1 inside MOV's
-- immediate. Update the proposal too: rejection must not rely on stale bytes.
def interiorBytes : List Byte := bytes.set 10 0xf6

def interiorGraph : CFG.Graph := { graph with nodes := graph.nodes.map fun node =>
  if node.offset = 9 then { node with instruction := .legacy (.jnz 0xf6) } else node }

theorem interior_decodes :
    ∀ i : interiorGraph.Index, CFG.nodeMatches interiorBytes (interiorGraph.node i) = true := by
  decide +kernel

theorem interior_partition :
    CFG.linearFrom 0 interiorGraph.nodes interiorBytes.length = true := by decide +kernel

theorem interior_rejected : CFG.Structural.check interiorBytes interiorGraph = false := by
  decide +kernel

-- A same-length CMP proposal cannot replace the actual TEST instruction.
def wrongInstruction : CFG.Graph := { graph with nodes := graph.nodes.map fun node =>
  if node.offset = 7 then { node with instruction := .cmp32 .rax .rax false } else node }

theorem wrong_instruction_rejected : CFG.Structural.check bytes wrongInstruction = false := by
  decide +kernel

-- The opcode at +9 remains present, but its displacement byte cannot be fetched.
theorem truncated_operand : Sequential.decodeAt (codeState (bytes.take 10) 9) =
    .error (.inaccessibleInstruction 10) := by rfl

theorem truncated_rejected : CFG.Structural.check (bytes.take 10) graph = false := by
  decide +kernel

-- Omitting RET loses the fallthrough exit and the complete selected partition.
theorem missing_ret_rejected :
    CFG.Structural.check bytes { graph with nodes := graph.nodes.take 4 } = false := by
  decide +kernel

-- A complete closed graph for the original window cannot authenticate an extra
-- selected suffix, even though its final RET needs no outgoing graph edge.
theorem unpartitioned_suffix_rejected :
    CFG.Structural.check (bytes ++ [0xc3]) graph = false := by decide +kernel

-- Acyclic interiors require strict decreases; entry remains the loop cutpoint.
theorem flat_depth_rejected : CFG.Structural.check bytes
    { graph with nodes := graph.nodes.map fun node => { node with depth := 0 } } = false := by
  decide +kernel

theorem depth_bound_rejected :
    CFG.Structural.check bytes { graph with maxDepth := 3 } = false := by decide +kernel

-- Explicit admission caps remain independent of structural and effect policy.
theorem exact_caps_checked :
    CFG.Structural.checkWith ⟨12, 5, by decide +kernel⟩ bytes graph = true := by decide +kernel

theorem byte_cap_rejected :
    CFG.Structural.checkWith ⟨11, 5, by decide +kernel⟩ bytes graph = false := by decide +kernel

theorem node_cap_rejected :
    CFG.Structural.checkWith ⟨12, 4, by decide +kernel⟩ bytes graph = false := by decide +kernel

end SpinlockAcquire

namespace ReadOnly

-- The small existing read-only shape: MOV EAX,1; RET.
def bytes : List Byte := [0xb8, 1, 0, 0, 0, 0xc3]

def graph : CFG.Graph := ⟨[
  ⟨0, .legacy (.mov32 .rax 1), true, 1⟩,
  ⟨5, .legacy .ret, false, 0⟩], 1⟩

theorem old_valid : CFG.Valid bytes graph := CFG.check_sound (by decide +kernel)

theorem structural_valid : CFG.Structural.Valid bytes graph :=
  CFG.Structural.Valid.ofReadOnly old_valid

theorem structural_checked : CFG.Structural.check bytes graph = true :=
  CFG.Structural.checkWith_complete structural_valid

theorem restored_valid : CFG.Valid bytes graph :=
  structural_valid.toReadOnly (by decide +kernel)

-- Exercise the general policy equivalence at the unchanged default profile.
theorem old_checked : CFG.check bytes graph = true :=
  (CFG.Structural.checkWith_readOnly_iff (profile := CFG.defaultProfile)).mpr
    ⟨structural_checked, by decide +kernel⟩

-- No cycle is involved here: omitting the entry cutpoint alone must reject.
theorem missing_entry_rejected : CFG.Structural.check bytes
    { graph with nodes := graph.nodes.map fun node => { node with cutpoint := false } } = false := by
  decide +kernel

end ReadOnly
end EDSL.Tests.StructuralCFG

#print axioms EDSL.Tests.StructuralCFG.SpinlockAcquire.decoded
#print axioms EDSL.Tests.StructuralCFG.SpinlockAcquire.backedge
#print axioms EDSL.Tests.StructuralCFG.SpinlockAcquire.valid
#print axioms EDSL.Tests.StructuralCFG.SpinlockAcquire.exchange_decoded
#print axioms EDSL.Tests.StructuralCFG.SpinlockAcquire.readOnly_rejected
#print axioms EDSL.Tests.StructuralCFG.SpinlockAcquire.interior_decodes
#print axioms EDSL.Tests.StructuralCFG.SpinlockAcquire.interior_rejected
#print axioms EDSL.Tests.StructuralCFG.SpinlockAcquire.truncated_operand
#print axioms EDSL.Tests.StructuralCFG.ReadOnly.structural_valid
#print axioms EDSL.Tests.StructuralCFG.ReadOnly.restored_valid
#print axioms EDSL.Tests.StructuralCFG.ReadOnly.old_checked
#audit_edsl
