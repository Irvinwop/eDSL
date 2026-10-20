/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Cutpoints
import EDSL.Audit

namespace EDSL.Tests.VCGenCutpoints
open X86 Sequential
namespace Loop

/-- Synthetic exact-byte loop: MOV RAX,RCX; TEST RAX,RAX; LOOP entry; RET.
Only the loop header is a cutpoint. TEST exercises both undefined AF choices;
LOOP uses its decremented counter rather than TEST's ZF. -/
def bytes : List Byte := [0x48, 0x89, 0xc8, 0x48, 0x85, 0xc0, 0xe2, 0xf8, 0xc3]

abbrev graph : CFG.Graph := ⟨[
  ⟨0, .movReg64 .rax .rcx, true, 3⟩,
  ⟨3, .test64 .rax .rax, false, 2⟩,
  ⟨6, .legacy (.loopRcx 248), false, 1⟩,
  ⟨8, .legacy .ret, false, 0⟩], 3⟩

theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide)

abbrev entry : graph.Index := ⟨0, by decide⟩

/- Finite search for a generated successor, with kernel-checked PC equality.
The search does not unfold the remaining WP or request an interior assertion. -/
local macro "block_successor_at" index:num : tactic => `(tactic|
  refine ⟨⟨$index:num, by decide⟩, by decide, ?_⟩)

local macro "block_successor" : tactic => `(tactic|
  first
  | block_successor_at 0
  | block_successor_at 1
  | block_successor_at 2
  | block_successor_at 3)

/-- Independent result: a positive-count loop ends with the last pre-decrement
counter in RAX, zero RCX, the protected return target and the ordinary RET stack
advance. Memory is unchanged. It makes no promise about the chosen AF value. -/
def Post (initial : State) (target : Word) (final : State) : Prop :=
  final.registers .rax = 1 ∧ final.registers .rcx = 0 ∧
  final.registers .rsp = initial.registers .rsp + 8 ∧
  final.rip = target ∧ final.memory = initial.memory

def AllowedRead (initial : State) (_ : State) (read : Read) : Prop :=
  read = ⟨.stack, initial.registers .rsp, 8⟩

def Inv (initial : State) (_ : graph.Index) (state : State) : Prop :=
  state.memory = initial.memory ∧ state.registers .rsp = initial.registers .rsp ∧
  state.registers .rcx ≠ 0

def rank (_ : graph.Index) (state : State) : Nat := (state.registers .rcx).toNat

/-- No per-instruction invariant, execute equation or localVC is supplied.
Reduction of the generated block WP composes all three loop instructions and
the exit RET. The arithmetic obligations concern only the cutpoint rank and
the independently stated return value. -/
def annotations (initial : State) (base target : Word)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) :
    VCGen.Cutpoints.Annotations bytes graph base (Post initial target) (AllowedRead initial) where
  Inv := Inv initial
  rank := rank
  blocks cut state isCut binding admitted := by
    have onlyCut : ∀ node : graph.Index, graph.cutpoint node = true → node = entry := by decide
    have same := onlyCut cut isCut
    subst cut
    obtain ⟨memory, rsp, nonzero⟩ := admitted
    have pc : state.rip = base := by
      simpa [CFG.Graph.node, CFG.Graph.cutpoint, graph, entry] using binding.2
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
    by_cases last : state.registers .rcx - 1 = 0
    · have one : state.registers .rcx = 1 := by
        exact (BitVec.sub_eq_iff_eq_add.mp last).trans (by decide)
      change VCGen.Cutpoints.wp graph base (Post initial target) (AllowedRead initial)
        (Inv initial) rank (rank entry state) 4 entry state
      repeat' (
        rw [VCGen.Cutpoints.wp]
        intro af
        simp only [CFG.Graph.node, graph, entry, execute, Instruction.operandReads,
          executeInstruction, executeLoop, executeShortBranch, executeRet,
          State.writeRegister, pure_ok]
        simp [AllowedRead, pc, memory, rsp, stack, canonicalTarget, one, BitVec.add_assoc]
        first | block_successor | skip
        try simp only [CFG.Graph.cutpoint, CFG.Graph.node,
          List.getElem_cons_zero, List.getElem_cons_succ])
      all_goals simp [Post]
    · change VCGen.Cutpoints.wp graph base (Post initial target) (AllowedRead initial)
        (Inv initial) rank (rank entry state) 4 entry state
      have condition : state.registers .rcx - (1#64) ≠ (0#64) := last
      have decrease : (state.registers .rcx - (1#64)).toNat < (state.registers .rcx).toNat := decreased
      repeat' (
        rw [VCGen.Cutpoints.wp]
        intro af
        simp only [CFG.Graph.node, graph, entry, execute, Instruction.operandReads,
          executeInstruction, executeLoop, executeShortBranch, State.writeRegister, pure_ok]
        simp [AllowedRead, pc, memory, condition, canonicalBase, BitVec.add_assoc]
        first | block_successor | skip
        try simp only [CFG.Graph.cutpoint, CFG.Graph.node,
          List.getElem_cons_zero, List.getElem_cons_succ, ↓reduceIte])
      all_goals simp [Inv, rank, rsp, condition]
      simpa only [BitVec.toNat_sub, BitVec.toNat_ofNat] using decrease

/-- Universal over the entire positive 64-bit counter range, all initial
registers/flags/memory, relocation base and complete AF streams. Assumptions
are executable exact code, a readable canonical RET target and nonzero RCX.
Zero is excluded because LOOP would first wrap its counter. -/
theorem total (initial : State) (base target : Word)
    (code : CodeAt initial.memory base bytes) (pc : initial.rip = base)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) (positive : initial.registers .rcx ≠ 0)
    (choices : Choices) :
    ∃ result, Sequential.run choices (4 * ((initial.registers .rcx).toNat + 1)) initial = .ok result ∧
      Post initial target result.state ∧
      result.instructions ≤ 4 * ((initial.registers .rcx).toNat + 1) := by
  have binding : CFG.At bytes graph base entry initial :=
    ⟨code, by simpa [graph, CFG.Graph.node, entry] using pc⟩
  exact (annotations initial base target stack canonicalTarget).sound valid
    (entry := entry) rfl binding ⟨rfl, rfl, positive⟩ choices

end Loop

/-- A usable stack with target zero, independent of any successful run. These
negative tests exercise the production executor inside the generated WP. -/
def ram : Memory where
  read _ := some 0
  executable _ := true

def state : State := ⟨fun _ => 0, 4096, 0, ram⟩

def retGraph : CFG.Graph := ⟨[⟨0, .legacy .ret, true, 0⟩], 0⟩
abbrev retNode : retGraph.Index := ⟨0, by decide⟩

-- The same real RET does meet its independently specified architectural effect.
example : VCGen.Cutpoints.wp retGraph 4096
    (fun final => final.rip = 0 ∧ final.registers .rsp = 8) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 1 retNode state := by
  letI := VCGen.Cutpoints.decidableWP retGraph 4096
    (fun final => final.rip = 0 ∧ final.registers .rsp = 8) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 (fun _ => inferInstance)
    (fun _ _ => inferInstance) (fun _ _ => inferInstance) 1 retNode state
  decide

-- A genuinely false client postcondition must not be inferred from RET success.
example : ¬ VCGen.Cutpoints.wp retGraph 4096 (fun _ => False) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 1 retNode state := by
  letI := VCGen.Cutpoints.decidableWP retGraph 4096 (fun _ => False) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 (fun _ => inferInstance)
    (fun _ _ => inferInstance) (fun _ _ => inferInstance) 1 retNode state
  decide

-- RET reads the stack. Denying that permission rejects an otherwise good return.
example : ¬ VCGen.Cutpoints.wp retGraph 4096 (fun _ => True) (fun _ _ => False)
    (fun _ _ => True) (fun _ _ => 0) 0 1 retNode state := by
  letI := VCGen.Cutpoints.decidableWP retGraph 4096 (fun _ => True) (fun _ _ => False)
    (fun _ _ => True) (fun _ _ => 0) 0 (fun _ => inferInstance)
    (fun _ _ => inferInstance) (fun _ _ => inferInstance) 1 retNode state
  decide

def spinGraph : CFG.Graph := ⟨[⟨0, .jmp 254, true, 0⟩], 0⟩
abbrev spinNode : spinGraph.Index := ⟨0, by decide⟩

-- A cutpoint self-loop with constant rank cannot obtain a termination certificate.
example : ¬ VCGen.Cutpoints.wp spinGraph 4096 (fun _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 1 spinNode state := by
  letI := VCGen.Cutpoints.decidableWP spinGraph 4096 (fun _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 (fun _ => inferInstance)
    (fun _ _ => inferInstance) (fun _ _ => inferInstance) 1 spinNode state
  decide

def afGraph : CFG.Graph := ⟨[
  ⟨0, .test64 .rax .rax, true, 1⟩,
  ⟨3, .legacy .ret, false, 0⟩], 1⟩
abbrev afNode : afGraph.Index := ⟨0, by decide⟩

-- Requiring one concrete undefined AF value is rejected, even though that
-- value is one possible successful execution. Both choices are quantified.
example : ¬ VCGen.Cutpoints.wp afGraph 4096
    (fun final => final.flags.getLsbD 4 = false) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 2 afNode state := by
  letI := VCGen.Cutpoints.decidableWP afGraph 4096
    (fun final => final.flags.getLsbD 4 = false) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 (fun _ => inferInstance)
    (fun _ _ => inferInstance) (fun _ _ => inferInstance) 2 afNode state
  decide

def syscallGraph : CFG.Graph := ⟨[
  ⟨0, .legacy .syscall, true, 1⟩,
  ⟨2, .legacy .ret, false, 0⟩], 1⟩
abbrev syscallNode : syscallGraph.Index := ⟨0, by decide⟩

-- A successful syscall observation is a boundary, not a returning execution.
example : ¬ VCGen.Cutpoints.wp syscallGraph 4096 (fun _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 2 syscallNode state := by
  letI := VCGen.Cutpoints.decidableWP syscallGraph 4096 (fun _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 (fun _ => inferInstance)
    (fun _ _ => inferInstance) (fun _ _ => inferInstance) 2 syscallNode state
  decide

def atomicGraph : CFG.Graph := ⟨[
  ⟨0, .legacy .exchangeEaxRdi, true, 1⟩,
  ⟨2, .legacy .ret, false, 0⟩], 1⟩
abbrev atomicNode : atomicGraph.Index := ⟨0, by decide⟩

def writableState : State := { state with memory := { ram with writable := fun _ => true } }

-- The aligned, accessible, writable XCHG produces an atomic observation.
-- The sequential block profile must reject it even with permissive contracts.
example : ¬ VCGen.Cutpoints.wp atomicGraph 4096 (fun _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 2 atomicNode writableState := by
  letI := VCGen.Cutpoints.decidableWP atomicGraph 4096 (fun _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 (fun _ => inferInstance)
    (fun _ _ => inferInstance) (fun _ _ => inferInstance) 2 atomicNode writableState
  decide

end EDSL.Tests.VCGenCutpoints

#print axioms EDSL.X86.VCGen.Cutpoints.Annotations.sound
#print axioms EDSL.Tests.VCGenCutpoints.Loop.total
#audit_edsl
