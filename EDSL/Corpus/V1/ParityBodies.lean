/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ParityCode
import EDSL.PureCall.Frame
import EDSL.X86.VCGen.Tactics
import EDSL.X86.VCGen.PureCall
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.ParityBodies
open X86 X86.Sequential X86.VCGen

abbrev Compiler := ParityCode.Compiler
abbrev bytes := ParityCode.bytes
abbrev spec := ParityCode.spec

/-- Proposed finite graphs are authenticated against the complete literal
windows by the production checker, independently of the loop annotations. -/
def gccGraph : CFG.Graph := vcgen_graph (bytes .defaultGCC)
def clangGraph : CFG.Graph := vcgen_graph (bytes .defaultClang)

theorem gcc_valid : CFG.Valid (bytes .defaultGCC) gccGraph :=
  CFG.check_sound (by decide +kernel)

theorem clang_valid : CFG.Valid (bytes .defaultClang) clangGraph :=
  CFG.check_sound (by decide +kernel)

abbrev gccEntry : gccGraph.Index := ⟨0, by decide +kernel⟩
abbrev gccLoop : gccGraph.Index := ⟨5, by decide +kernel⟩
abbrev clangEntry : clangGraph.Index := ⟨0, by decide +kernel⟩
abbrev clangLoop : clangGraph.Index := ⟨5, by decide +kernel⟩

/-- Caller-saved scratch for either implementation; the entire memory and
every register outside this set retain their original values at cutpoints. -/
def scratch : List Register := [.rax, .rdx, .rcx, .rdi]

def frame (initial current : State) : Prop :=
  PureCall.ScratchFrame scratch initial current

def gccInv (input : PureCall.Invocation spec) (initial : State)
    (node : gccGraph.Index) (current : State) : Prop :=
  frame initial current ∧
    if node.val = 0 then current.registers .rdi = input.value else
      WordMath.ParityInvariant input.value (current.registers .rdi)
        ((current.registers .rax).setWidth 32).toNat ∧ current.registers .rdi ≠ 0

def clangInv (input : PureCall.Invocation spec) (initial : State)
    (node : clangGraph.Index) (current : State) : Prop :=
  frame initial current ∧
    if node.val = 0 then current.registers .rdi = input.value else
      WordMath.ParityInvariant input.value (current.registers .rdi)
        ((current.registers .rax).setWidth 32).toNat ∧ current.registers .rdi ≠ 0 ∧
          current.registers .rcx = current.registers .rdi

def gccRank (input : PureCall.Invocation spec) (node : gccGraph.Index) (current : State) : Nat :=
  if node.val = 0 then input.value.toNat + 1 else (current.registers .rdi).toNat

def clangRank (input : PureCall.Invocation spec) (node : clangGraph.Index) (current : State) : Nat :=
  if node.val = 0 then input.value.toNat + 1 else (current.registers .rdi).toNat

private theorem low32_extend (value : BitVec 32) :
    (value.setWidth 64).setWidth 32 = value := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

private theorem test_nonzero (old value : Word) (af : Bool) (nonzero : value ≠ 0#64) :
    (logicalFlags64 old (value &&& value) af).getLsbD 6 = false := by
  rw [logicalFlags64_zero, BitVec.and_self]
  exact beq_eq_false_iff_ne.mpr nonzero

private theorem shift_zero (old value : Word) (af : Bool) :
    (shrOneFlags64 old value af).getLsbD 6 = (value >>> 1 == 0#64) :=
  (shrOneFlags64_bits ..).2.2.2.1

/-- Clang compares the old full64 input with one. Its JA decision agrees
exactly with whether the unsigned shifted remainder is nonzero. -/
private theorem above_one (old value : Word) :
    Condition.holds .above (cmpFlags64 old value (1#64)) = decide (value >>> 1 ≠ 0#64) := by
  rw [Condition.cmp_above]
  change decide (1 < value.toNat) = decide (value >>> 1 ≠ 0#64)
  have zero : value >>> 1 = 0#64 ↔ value.toNat / 2 = 0 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, BitVec.toNat_zero,
      Nat.shiftRight_eq_div_pow]
  simp only [decide_eq_decide, ne_eq, zero]
  omega

private theorem saved_protected :
    ∀ register ∈ PureCall.calleeSaved, register ≠ .rsp ∧ register ∉ scratch := by
  decide +kernel

local macro "parity_frame" old:ident : tactic => `(tactic| (
  constructor
  · simp only [State.writeRegister, ($old).memory]
  · simpa only [logicalFlags32_preserves, logicalFlags64_preserves,
      shrOneFlags64_preserves, cmpFlags64_preserves] using ($old).flags
  · intro register untouched
    have previous := ($old).registers register untouched
    simp only [scratch, List.mem_cons, List.mem_singleton, not_or] at untouched
    rcases untouched with ⟨notA, notD, notC, notI⟩
    simpa [State.writeRegister, notA, notD, notC, notI] using previous))

local macro "parity_return" old:ident correct:ident : tactic => `(tactic| (
  vcgen_factor =>
    refine PureCall.ScratchFrame.post_return (scratch := scratch)
      ?_ saved_protected ?_ rfl rfl
    · constructor
      · simp only [State.writeRegister, ($old).memory]
      · simpa only [logicalFlags32_preserves, logicalFlags64_preserves,
          shrOneFlags64_preserves, cmpFlags64_preserves] using ($old).flags
      · intro register untouched
        have separate : register ≠ .rsp ∧ register ∉ scratch := by
          simpa only [List.mem_cons, not_or] using untouched
        have previous := ($old).registers register separate.2
        have outside := separate.2
        simp only [scratch, List.mem_cons, List.mem_singleton, not_or] at outside
        rcases outside with ⟨notA, notD, notC, notI⟩
        simpa [State.writeRegister, separate.1, notA, notD, notC, notI]
          using previous
    · simpa [spec, ParityCode.spec, Arithmetic64.parity64, low32_extend] using $correct))

/-- Initialization and one shift iteration are the only sparse obligations.
The shared independent parity invariant supplies the result; unsigned natural
value supplies strict descent for every nonzero full64 remainder. -/
def gccAnnotations (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultGCC) input initial) :
    Cutpoints.Annotations (bytes .defaultGCC) gccGraph initial.rip
      (PureCall.Post spec input initial)
      (fun _ read => PureCall.RawRead initial read) where
  Inv := gccInv input initial
  rank := gccRank input
  blocks cut state isCut binding admitted := by
    have cuts : cut = gccEntry ∨ cut = gccLoop := by
      have allCuts : ∀ node : gccGraph.Index,
          gccGraph.cutpoint node = true → node = gccEntry ∨ node = gccLoop := by decide +kernel
      exact allCuts cut isCut
    obtain ⟨framed, invariant⟩ := admitted
    have memory := framed.memory
    have rsp := framed.registers .rsp (by decide +kernel)
    have allowed : PureCall.RawRead initial ⟨.stack, initial.registers .rsp, 8⟩ :=
      ⟨rfl, rfl, rfl⟩
    have canonicalLoop : canonical (initial.rip + 16#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using gcc_valid.canonical_node binding.1 gccLoop
    have canonicalEmpty : canonical (initial.rip + 32#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using
        gcc_valid.canonical_node binding.1 (⟨12, by decide +kernel⟩ : gccGraph.Index)
    rcases cuts with same | same
    · subst cut
      have argument : state.registers .rdi = input.value := invariant
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node, gccGraph, gccEntry] using binding.2
      by_cases empty : input.value = 0#64
      · have correct : (0#32).toNat = WordMath.cardinality input.value % 2 := by simp [empty]
        change Cutpoints.wp gccGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (gccInv input initial)
          (gccRank input) (gccRank input gccEntry state) 14 gccEntry state
        vcgen_block gccGraph gccEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp,
          pre.stack, pre.returnCanonical, allowed, argument, empty,
          logicalFlags64_zero, canonicalEmpty, BitVec.add_assoc]
        parity_return framed correct
      · have initialParity := WordMath.parityInvariant_start (w := 64) (input.value : Word)
        have inputZf := fun (flags : Word) (af : Bool) => test_nonzero flags input.value af empty
        change Cutpoints.wp gccGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (gccInv input initial)
          (gccRank input) (gccRank input gccEntry state) 14 gccEntry state
        vcgen_block gccGraph gccEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory,
          argument, inputZf, BitVec.add_assoc]
        dsimp only [gccInv, gccRank]
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · parity_frame framed
        · simpa [argument] using initialParity
        · intro zero
          apply empty
          change state.registers .rdi = 0#64 at zero
          exact argument.symm.trans zero
        · simp [argument]
    · subst cut
      change WordMath.ParityInvariant input.value (state.registers .rdi)
        ((state.registers .rax).setWidth 32).toNat ∧ state.registers .rdi ≠ 0#64 at invariant
      have pc : state.rip = initial.rip + 16#64 := by
        simpa [CFG.Graph.node, gccGraph, gccLoop] using binding.2
      have advanced := Arithmetic64.parity64_step32 invariant.1
      have decreases := WordMath.shiftRight_one_toNat_lt (state.registers .rdi) invariant.2
      by_cases finished : state.registers .rdi >>> 1 = 0#64
      · have correct := WordMath.parityInvariant_finish advanced finished
        change Cutpoints.wp gccGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (gccInv input initial)
          (gccRank input) (gccRank input gccLoop state) 9 gccLoop state
        vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp,
          pre.stack, pre.returnCanonical, allowed, finished,
          shift_zero, LogicalOp.eval, BitVec.add_assoc]
        parity_return framed correct
      · change Cutpoints.wp gccGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (gccInv input initial)
          (gccRank input) (gccRank input gccLoop state) 9 gccLoop state
        vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, finished,
          shift_zero, LogicalOp.eval, canonicalLoop, BitVec.add_assoc]
        dsimp only [gccInv, gccRank]
        refine ⟨⟨?_, ?_, finished⟩, ?_⟩
        · parity_frame framed
        · simpa [low32_extend] using advanced
        · exact decreases

/-- Clang carries the full64 remainder in both RCX and RDI at the loop
cutpoint. CMP observes the old RDI and JA tests the same unsigned descent. -/
def clangAnnotations (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultClang) input initial) :
    Cutpoints.Annotations (bytes .defaultClang) clangGraph initial.rip
      (PureCall.Post spec input initial)
      (fun _ read => PureCall.RawRead initial read) where
  Inv := clangInv input initial
  rank := clangRank input
  blocks cut state isCut binding admitted := by
    have cuts : cut = clangEntry ∨ cut = clangLoop := by
      have allCuts : ∀ node : clangGraph.Index,
          clangGraph.cutpoint node = true → node = clangEntry ∨ node = clangLoop := by decide +kernel
      exact allCuts cut isCut
    obtain ⟨framed, invariant⟩ := admitted
    have memory := framed.memory
    have rsp := framed.registers .rsp (by decide +kernel)
    have allowed : PureCall.RawRead initial ⟨.stack, initial.registers .rsp, 8⟩ :=
      ⟨rfl, rfl, rfl⟩
    have canonicalLoop : canonical (initial.rip + 16#64) = true := by
      simpa [CFG.Graph.node, clangGraph] using clang_valid.canonical_node binding.1 clangLoop
    have canonicalEmpty : canonical (initial.rip + 35#64) = true := by
      simpa [CFG.Graph.node, clangGraph] using
        clang_valid.canonical_node binding.1 (⟨12, by decide +kernel⟩ : clangGraph.Index)
    rcases cuts with same | same
    · subst cut
      have argument : state.registers .rdi = input.value := invariant
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node, clangGraph, clangEntry] using binding.2
      by_cases empty : input.value = 0#64
      · have correct : (0#32).toNat = WordMath.cardinality input.value % 2 := by simp [empty]
        change Cutpoints.wp clangGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (clangInv input initial)
          (clangRank input) (clangRank input clangEntry state) 14 clangEntry state
        vcgen_block clangGraph clangEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp,
          pre.stack, pre.returnCanonical, allowed, argument, empty,
          logicalFlags64_zero, canonicalEmpty, BitVec.add_assoc]
        parity_return framed correct
      · have initialParity := WordMath.parityInvariant_start (w := 64) (input.value : Word)
        have inputZf := fun (flags : Word) (af : Bool) => test_nonzero flags input.value af empty
        change Cutpoints.wp clangGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (clangInv input initial)
          (clangRank input) (clangRank input clangEntry state) 14 clangEntry state
        vcgen_block clangGraph clangEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory,
          argument, inputZf, BitVec.add_assoc]
        dsimp only [clangInv, clangRank]
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · parity_frame framed
        · simpa [argument] using initialParity
        · intro zero
          apply empty
          change state.registers .rdi = 0#64 at zero
          exact argument.symm.trans zero
        · simpa using argument.symm
        · simp [argument]
    · subst cut
      change WordMath.ParityInvariant input.value (state.registers .rdi)
        ((state.registers .rax).setWidth 32).toNat ∧ state.registers .rdi ≠ 0#64 ∧
          state.registers .rcx = state.registers .rdi at invariant
      have sameRemainder := invariant.2.2
      have pc : state.rip = initial.rip + 16#64 := by
        simpa [CFG.Graph.node, clangGraph, clangLoop] using binding.2
      have advanced := Arithmetic64.parity64_step32 invariant.1
      have decreases := WordMath.shiftRight_one_toNat_lt (state.registers .rdi) invariant.2.1
      by_cases finished : state.registers .rdi >>> 1 = 0#64
      · have correct := WordMath.parityInvariant_finish advanced finished
        change Cutpoints.wp clangGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (clangInv input initial)
          (clangRank input) (clangRank input clangLoop state) 9 clangLoop state
        vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp,
          pre.stack, pre.returnCanonical, allowed, finished, sameRemainder,
          above_one, LogicalOp.eval, BitVec.add_assoc]
        parity_return framed correct
      · change Cutpoints.wp clangGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (clangInv input initial)
          (clangRank input) (clangRank input clangLoop state) 9 clangLoop state
        vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, finished,
          sameRemainder, above_one, LogicalOp.eval, canonicalLoop, BitVec.add_assoc]
        dsimp only [clangInv, clangRank]
        refine ⟨⟨?_, ?_, finished, rfl⟩, ?_⟩
        · parity_frame framed
        · simpa [low32_extend] using advanced
        · exact decreases

def graph : Compiler → CFG.Graph
  | .defaultGCC => gccGraph
  | .defaultClang => clangGraph

theorem valid (compiler : Compiler) : CFG.Valid (bytes compiler) (graph compiler) := by
  cases compiler with
  | defaultGCC => exact gcc_valid
  | defaultClang => exact clang_valid

/-- Each binary keeps its own annotations in its direct semantic theorem. -/
theorem gcc_generated (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultGCC) input initial) :
    ∃ annotations : Cutpoints.Annotations (bytes .defaultGCC) gccGraph initial.rip
      (PureCall.Post spec input initial) (fun _ read => PureCall.RawRead initial read),
      annotations.Inv gcc_valid.entry initial := by
  refine ⟨gccAnnotations input initial pre, PureCall.ScratchFrame.refl _ _, ?_⟩
  exact (Arithmetic64.parity64_bound_iff input.value initial).mp pre.arguments

theorem clang_generated (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultClang) input initial) :
    ∃ annotations : Cutpoints.Annotations (bytes .defaultClang) clangGraph initial.rip
      (PureCall.Post spec input initial) (fun _ read => PureCall.RawRead initial read),
      annotations.Inv clang_valid.entry initial := by
  refine ⟨clangAnnotations input initial pre, PureCall.ScratchFrame.refl _ _, ?_⟩
  exact (Arithmetic64.parity64_bound_iff input.value initial).mp pre.arguments

theorem gcc_semantics :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) (bytes .defaultGCC) :=
  pureCall_semantics_of_cutpoints spec (bytes .defaultGCC) gccGraph gcc_valid gcc_generated

theorem clang_semantics :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) (bytes .defaultClang) :=
  pureCall_semantics_of_cutpoints spec (bytes .defaultClang) clangGraph clang_valid clang_generated

/-- For every admitted full64 input and every AF stream, the shared resource
bridge retains original caller/code authority and complete RAM at every prefix,
and gives the mathematical result and ABI frame at return. The target assumes
stable ordinary RAM, CET/IBT/shadow stacks off, supplied logical authority and
no asynchronous interference. No CPU/OS or compiler refinement is asserted. -/
theorem semantics (compiler : Compiler) :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) (bytes compiler) := by
  cases compiler with
  | defaultGCC => exact gcc_semantics
  | defaultClang => exact clang_semantics

#print axioms gcc_semantics
#print axioms clang_semantics
end EDSL.Corpus.V1.ParityBodies
#audit_edsl
