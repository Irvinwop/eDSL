/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.StructuralDiscovery
import tests.StructuralCFG

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.StructuralDiscovery
open X86 Sequential

private instance {α β : Type} [DecidableEq α] [DecidableEq β] :
    DecidableEq (Except α β)
  | .error left, .error right =>
    if same : left = right then .isTrue (congrArg Except.error same)
    else .isFalse (fun equal => same (Except.error.inj equal))
  | .ok left, .ok right =>
    if same : left = right then .isTrue (congrArg Except.ok same)
    else .isFalse (fun equal => same (Except.ok.inj equal))
  | .error _, .ok _ => .isFalse (by intro equal; cases equal)
  | .ok _, .error _ => .isFalse (by intro equal; cases equal)

/-!
Discovery regressions over owned literal windows, using actual production output
rather than hand-assigned graphs. Admission proves structure and decoding only;
these tests supply no lock behavior, termination, execution, or corpus credit.
-/

namespace SpinlockAcquire
open EDSL.Tests.StructuralCFG.SpinlockAcquire (bytes)

-- Frozen Clang bytes b801000000870785c075f5c3. Expected offsets,
-- instructions and successors follow from their encodings, not annotations.
theorem actual_nodes :
    (CFG.Structural.analyze bytes).map (fun graph => graph.nodes.map
      (fun node => (node.offset, node.instruction, node.successors))) =
    .ok [(0, .legacy (.mov32 .rax 1), [5]),
      (5, .legacy .exchangeEaxRdi, [7]),
      (7, .test32 .rax .rax false, [9]),
      (9, .legacy (.jnz 0xf5), [11, 0]),
      (11, .legacy .ret, [])] := by decide +kernel

-- The witness comes from analyze itself. Both successful entry points expose
-- checked structure for this actual graph, including the real memory XCHG.
theorem accepted :
    ∃ graph, CFG.Structural.analyze bytes = .ok graph ∧
      CFG.Structural.discover bytes = some graph ∧
      CFG.Structural.check bytes graph = true ∧ CFG.Structural.Valid bytes graph := by
  cases result : CFG.Structural.analyze bytes with
  | error fault =>
    have observed := actual_nodes
    rw [result] at observed
    cases observed
  | ok graph =>
    have found : CFG.Structural.discover bytes = some graph := by
      simp only [CFG.Structural.discover, result, Except.toOption]
    exact ⟨graph, rfl, found, CFG.Structural.analyze_checked result,
      CFG.Structural.discover_sound found⟩

def exactProfile : CFG.Profile := ⟨12, 5, by decide +kernel⟩

-- Twelve bytes and five nodes fit exactly; the explicit-profile API returns
-- the same actual graph and certifies validity under that precise profile.
theorem exact_caps :
    ∃ graph, CFG.Structural.analyzeWith exactProfile bytes = .ok graph ∧
      CFG.Structural.discoverWith exactProfile bytes = some graph ∧
      CFG.Structural.checkWith exactProfile bytes graph = true ∧
      CFG.Structural.Valid bytes graph exactProfile := by
  obtain ⟨graph, analyzed, _, _⟩ := accepted
  have same : CFG.Structural.analyzeWith exactProfile bytes =
      CFG.Structural.analyze bytes := by decide +kernel
  have profiled : CFG.Structural.analyzeWith exactProfile bytes = .ok graph :=
    same.trans analyzed
  have found : CFG.Structural.discoverWith exactProfile bytes = some graph := by
    simp only [CFG.Structural.discoverWith, profiled, Except.toOption]
  exact ⟨graph, profiled, found, CFG.Structural.discoverWith_checked found,
    CFG.Structural.analyzeWith_sound profiled⟩

theorem readOnly_rejected :
    CFG.analyzeWith exactProfile bytes = .error (.unsupportedInstruction 5) ∧
      CFG.analyze bytes = .error (.unsupportedInstruction 5) := by
  exact ⟨by decide +kernel, by decide +kernel⟩

def interiorBytes : List Byte := bytes.set 10 0xf6

-- Stage equality synthesis without local instances in kernel reflection.
private instance : DecidableEq (Sequential.Instruction × List Word) := inferInstance
private instance : DecidableEq (Option (Sequential.Instruction × List Word)) := inferInstance
private instance : DecidableEq (Bool × Bool) := inferInstance
private instance : DecidableEq (Bool × Bool × Bool) := inferInstance
private instance : DecidableEq (Option (Sequential.Instruction × List Word) × Bool × Bool × Bool) :=
  inferInstance
private instance : DecidableEq
    (List Nat × Option (Sequential.Instruction × List Word) × Bool × Bool × Bool) :=
  inferInstance
private instance : DecidableEq (Except CFG.DiscoveryError
    (List Nat × Option (Sequential.Instruction × List Word) × Bool × Bool × Bool)) :=
  inferInstance
private instance : DecidableEq (Except CFG.DiscoveryError CFG.Graph) := inferInstance

-- JNE -10 at +9 targets 9+2-10=1, inside MOV's immediate. Inspect the fresh
-- proposal: all five starts survive, its actual operand/successors reflect
-- the mutation, and decoding and the full partition still match. No node is
-- at +1, so successor closure must reject at the final structural gate.
theorem interior_rejected :
    ((CFG.proposeWith (fun _ => true) CFG.defaultProfile interiorBytes).map
      (fun graph => (graph.nodes.map (·.offset),
        (graph.nodes.find? (fun node => node.offset == 9)).map
          (fun node => (node.instruction, node.successors)),
        graph.nodes.all (fun node => CFG.nodeMatches interiorBytes node),
        CFG.linearFrom 0 graph.nodes interiorBytes.length,
        CFG.Structural.check interiorBytes graph)),
      CFG.Structural.analyze interiorBytes) =
    (.ok ([0, 5, 7, 9, 11], some (.legacy (.jnz 0xf6), [11, 1]), true, true, false),
      .error .invalidGraph) := by
  decide +kernel

-- Taking ten bytes retains the JNE opcode at +9 but loses its displacement
-- at +10. Structural analysis reaches that fetch; read-only stops at XCHG.
theorem truncated_priority :
    CFG.Structural.analyze (bytes.take 10) =
        .error (.decode 9 (.inaccessibleInstruction 10)) ∧
      CFG.analyze (bytes.take 10) = .error (.unsupportedInstruction 5) := by
  exact ⟨by decide +kernel, by decide +kernel⟩

-- The byte cap takes priority even over read-only's earlier effect rejection.
-- Four node slots cannot consume the fifth instruction (RET at +11).
theorem cap_priority :
    CFG.Structural.analyzeWith ⟨11, 5, by decide +kernel⟩ bytes = .error .byteLimit ∧
      CFG.analyzeWith ⟨11, 5, by decide +kernel⟩ bytes = .error .byteLimit ∧
      CFG.Structural.analyzeWith ⟨12, 4, by decide +kernel⟩ bytes =
        .error .instructionLimit := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end SpinlockAcquire

-- Empty input wins before either zero cap, for both admission policies.
theorem empty_priority :
    CFG.Structural.analyzeWith ⟨0, 0, by decide +kernel⟩ [] = .error .empty ∧
      CFG.analyzeWith ⟨0, 0, by decide +kernel⟩ [] = .error .empty := by
  exact ⟨by decide +kernel, by decide +kernel⟩

namespace CompleteWindow

-- RET has no successors, but discovery must still consume the selected suffix.
theorem two_rets :
    (CFG.Structural.analyze [0xc3, 0xc3]).map (fun graph => graph.nodes.map
      (fun node => (node.offset, node.instruction))) =
    .ok [(0, .legacy .ret), (1, .legacy .ret)] := by decide +kernel

-- EVEX lead byte 62 is unsupported by the production decoder, with no suffix
-- fetch needed. A valid RET prefix cannot hide this actual decode failure.
theorem unsupported_suffix :
    CFG.Structural.analyze [0xc3, 0x62] =
        .error (.decode 1 (.unsupportedOpcode 0x62)) ∧
      CFG.analyze [0xc3, 0x62] = .error (.decode 1 (.unsupportedOpcode 0x62)) := by
  exact ⟨by decide +kernel, by decide +kernel⟩

end CompleteWindow

namespace ReadOnly
open EDSL.Tests.StructuralCFG.ReadOnly (bytes)

-- Preserve normal MOV EAX,1; RET discovery through the old explicit API.
theorem actual_nodes :
    (CFG.analyzeWith CFG.defaultProfile bytes).map (fun graph => graph.nodes.map
      (fun node => (node.offset, node.instruction))) =
    .ok [(0, .legacy (.mov32 .rax 1)), (5, .legacy .ret)] := by decide +kernel

theorem accepted :
    ∃ graph, CFG.analyzeWith CFG.defaultProfile bytes = .ok graph ∧
      CFG.discover bytes = some graph ∧ CFG.check bytes graph = true ∧
      CFG.Valid bytes graph := by
  cases result : CFG.analyzeWith CFG.defaultProfile bytes with
  | error fault =>
    have observed := actual_nodes
    rw [result] at observed
    cases observed
  | ok graph =>
    have found : CFG.discover bytes = some graph := by
      simp only [CFG.discover, CFG.analyze, result, Except.toOption]
    exact ⟨graph, rfl, found, CFG.discover_checked found, CFG.analyzeWith_sound result⟩

end ReadOnly
end EDSL.Tests.StructuralDiscovery

#print axioms EDSL.Tests.StructuralDiscovery.SpinlockAcquire.actual_nodes
#print axioms EDSL.Tests.StructuralDiscovery.SpinlockAcquire.accepted
#print axioms EDSL.Tests.StructuralDiscovery.SpinlockAcquire.exact_caps
#print axioms EDSL.Tests.StructuralDiscovery.SpinlockAcquire.readOnly_rejected
#print axioms EDSL.Tests.StructuralDiscovery.SpinlockAcquire.interior_rejected
#print axioms EDSL.Tests.StructuralDiscovery.SpinlockAcquire.truncated_priority
#print axioms EDSL.Tests.StructuralDiscovery.SpinlockAcquire.cap_priority
#print axioms EDSL.Tests.StructuralDiscovery.empty_priority
#print axioms EDSL.Tests.StructuralDiscovery.CompleteWindow.two_rets
#print axioms EDSL.Tests.StructuralDiscovery.CompleteWindow.unsupported_suffix
#print axioms EDSL.Tests.StructuralDiscovery.ReadOnly.actual_nodes
#print axioms EDSL.Tests.StructuralDiscovery.ReadOnly.accepted
#audit_edsl
