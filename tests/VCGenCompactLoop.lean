/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Tactics
import Lean

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.VCGenCompactLoop
open X86 Sequential X86.VCGen

/-- MOV RAX,RCX; NOP9; TEST RAX,RAX; LOOP entry; RET. The NOP and
TEST are real generated interior steps, not client transition rules. TEST's
undefined AF is quantified; LOOP branches on its own decremented counter. -/
def bytes : List Byte :=
  [0x48, 0x89, 0xc8, 0x66, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0,
    0x48, 0x85, 0xc0, 0xe2, 0xef, 0xc3]

/-- Keep the checked graph as a reusable definition, as finite clients do. -/
def graph : CFG.Graph := ⟨[
  ⟨0, .movReg64 .rax .rcx, true, 4⟩,
  ⟨3, .nop .nine, false, 3⟩,
  ⟨12, .test64 .rax .rax, false, 2⟩,
  ⟨15, .legacy (.loopRcx 239), false, 1⟩,
  ⟨17, .legacy .ret, false, 0⟩], 4⟩

theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide)

abbrev entry : graph.Index := ⟨0, by decide⟩

/-- A positive-count loop returns the last pre-decrement count, not the
initial count. The protected caller slot is its only operand read. -/
def Post (initial : State) (target : Word) (final : State) : Prop :=
  final.registers .rax = 1 ∧ final.registers .rcx = 0 ∧
  final.registers .rsp = initial.registers .rsp + 8 ∧
  final.rip = target ∧ final.memory = initial.memory

def AllowedRead (initial : State) (_ : State) (read : Read) : Prop :=
  read = ⟨.stack, initial.registers .rsp, 8⟩

def Inv (initial : State) (node : graph.Index) (state : State) : Prop :=
  node = entry ∧ state.memory = initial.memory ∧
  state.registers .rsp = initial.registers .rsp ∧ state.registers .rcx ≠ 0

def rank (_ : graph.Index) (state : State) : Nat := (state.registers .rcx).toNat

def annotations (initial : State) (base target : Word)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) :
    Cutpoints.Annotations bytes graph base (Post initial target) (AllowedRead initial) where
  Inv := Inv initial
  rank := rank
  blocks cut state isCut binding admitted := by
    have onlyCut : ∀ node : graph.Index, graph.cutpoint node = true → node = entry := by decide
    have same := onlyCut cut isCut
    subst cut
    obtain ⟨_, memory, rsp, nonzero⟩ := admitted
    have pc : state.rip = base := by
      simpa [CFG.Graph.node, graph, entry] using binding.2
    have canonicalBase : canonical base = true := by
      simpa [CFG.Graph.node, graph, entry] using valid.canonical_node binding.1 entry
    have decreased : (state.registers .rcx - 1).toNat < (state.registers .rcx).toNat := by
      have positive : 0 < (state.registers .rcx).toNat := by
        have naturalNonzero : (state.registers .rcx).toNat ≠ 0 := by
          intro zero
          apply nonzero
          apply BitVec.eq_of_toNat_eq
          simpa using zero
        omega
      have oneLe : (1 : Word) ≤ state.registers .rcx := by
        change 1 ≤ (state.registers .rcx).toNat
        omega
      rw [BitVec.toNat_sub_of_le oneLe]
      change (state.registers .rcx).toNat - 1 < (state.registers .rcx).toNat
      omega
    change Cutpoints.wp graph base (Post initial target) (AllowedRead initial)
      (Inv initial) rank (rank entry state) 5 entry state
    by_cases last : state.registers .rcx - 1 = 0
    · have one : state.registers .rcx = 1 :=
        (BitVec.sub_eq_iff_eq_add.mp last).trans (by decide)
      vcgen_block graph entry simp [AllowedRead, pc, memory, rsp, stack,
        canonicalTarget, one, BitVec.add_assoc]
      all_goals simp [Post]
    · have condition : state.registers .rcx - (1#64) ≠ (0#64) := last
      have decrease : (state.registers .rcx - (1#64)).toNat <
          (state.registers .rcx).toNat := decreased
      vcgen_block graph entry simp [AllowedRead, pc, memory, condition,
        canonicalBase, BitVec.add_assoc]
      all_goals simp [Inv, rank, rsp, condition]
      simpa only [BitVec.toNat_sub, BitVec.toNat_ofNat] using decrease

/-- The actual production run is total for every positive full64 counter,
arbitrary initial state, relocation and complete choice stream. Executable
bytes, the original readable caller slot and canonical return are premises;
no successful execution or terminal value is assumed. -/
theorem total (initial : State) (base target : Word)
    (code : CodeAt initial.memory base bytes) (pc : initial.rip = base)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) (positive : initial.registers .rcx ≠ 0)
    (choices : Choices) :
    ∃ result, Sequential.run choices (5 * ((initial.registers .rcx).toNat + 1)) initial = .ok result ∧
      Post initial target result.state ∧
      result.instructions ≤ 5 * ((initial.registers .rcx).toNat + 1) := by
  have binding : CFG.At bytes graph base entry initial :=
    ⟨code, by simpa [graph, CFG.Graph.node, entry] using pc⟩
  exact (annotations initial base target stack canonicalTarget).sound valid
    (entry := entry) rfl binding ⟨rfl, rfl, rfl, positive⟩ choices

/-- A no-op callback keeps the original obligation available. A callback
that introduces a hypothesis must be rejected before continuation factoring. -/
theorem callback_contract (proposition : Prop) (evidence : proposition) :
    proposition ∧ (proposition → proposition) := by
  constructor
  · vcgen_factor => skip
    fail_if_success (vcgen_factor => rename proposition => supplied)
    exact evidence
  · fail_if_success (vcgen_factor => intro introduced)
    exact fun supplied => supplied

/-- This real block reaches its header with RCX=1. A constant rank cannot
certify that back edge, even with unrestricted reads and a trivial invariant
and terminal contract. No RET or memory access can discharge the rank check. -/
private def backEdgeState : State where
  registers register := if register = .rcx then 2 else 0
  rip := 4096
  flags := 0
  memory := { read := fun _ => none, executable := fun _ => false }

theorem constant_rank_rejected :
    ¬ Cutpoints.wp graph 4096 (fun _ => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => 0) 0 5 entry backEdgeState := by
  letI := Cutpoints.decidableWP graph 4096 (fun _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 (fun _ => inferInstance)
    (fun _ _ => inferInstance) (fun _ _ => inferInstance) 5 entry backEdgeState
  decide

end EDSL.Tests.VCGenCompactLoop

elab "#audit_compact_loop" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``EDSL.Tests.VCGenCompactLoop.valid,
      ``EDSL.Tests.VCGenCompactLoop.annotations, ``EDSL.Tests.VCGenCompactLoop.total,
      ``EDSL.Tests.VCGenCompactLoop.callback_contract,
      ``EDSL.Tests.VCGenCompactLoop.constant_rank_rejected] do
    for dependency in ← Lean.collectAxioms name do
      unless allowed.contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"
    Lean.logInfo m!"Allowed named audit passed: {name}"

#print axioms EDSL.Tests.VCGenCompactLoop.total
#audit_compact_loop
