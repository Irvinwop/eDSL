/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.PopcountCode
import EDSL.PureCall.Frame
import EDSL.X86.VCGen.Tactics
import EDSL.X86.VCGen.PureCall

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.PopcountBodies
open X86 X86.Sequential X86.VCGen

abbrev Compiler := PopcountCode.Compiler
abbrev bytes := PopcountCode.bytes
abbrev spec := PopcountCode.spec

/-- Graphs are proposed from the complete unchanged windows. Their finite
shape is independently authenticated by the production checker below. -/
def gccGraph : CFG.Graph := vcgen_graph (bytes .defaultGCC)
def clangGraph : CFG.Graph := vcgen_graph (bytes .defaultClang)

theorem gcc_valid : CFG.Valid (bytes .defaultGCC) gccGraph :=
  CFG.check_sound (by decide +kernel)

theorem clang_valid : CFG.Valid (bytes .defaultClang) clangGraph :=
  CFG.check_sound (by decide +kernel)

abbrev gccEntry : gccGraph.Index := ⟨0, by decide +kernel⟩
abbrev gccLoop : gccGraph.Index := ⟨5, by decide +kernel⟩
abbrev clangEntry : clangGraph.Index := ⟨0, by decide +kernel⟩
abbrev clangLoop : clangGraph.Index := ⟨4, by decide +kernel⟩

def scratch : Compiler → List Register
  | .defaultGCC => [.rax, .rdx, .rdi]
  | .defaultClang => [.rax, .rcx, .rdi]

def counter : Compiler → Register
  | .defaultGCC => .rdx
  | .defaultClang => .rax

def frame (compiler : Compiler) (initial current : State) : Prop :=
  PureCall.ScratchFrame (scratch compiler) initial current

def gccInv (input : PureCall.Invocation spec) (initial : State)
    (node : gccGraph.Index) (current : State) : Prop :=
  frame .defaultGCC initial current ∧
    if node.val = 0 then current.registers .rdi = input.value else
      WordMath.CountInvariant input.value (current.registers .rdi)
        ((current.registers .rdx).setWidth 32).toNat ∧ current.registers .rdi ≠ 0

def clangInv (input : PureCall.Invocation spec) (initial : State)
    (node : clangGraph.Index) (current : State) : Prop :=
  frame .defaultClang initial current ∧
    if node.val = 0 then current.registers .rdi = input.value else
      WordMath.CountInvariant input.value (current.registers .rdi)
        ((current.registers .rax).setWidth 32).toNat ∧ current.registers .rdi ≠ 0

def gccRank (input : PureCall.Invocation spec) (node : gccGraph.Index) (current : State) : Nat :=
  if node.val = 0 then WordMath.cardinality input.value + 1
  else WordMath.cardinality (current.registers .rdi)

def clangRank (input : PureCall.Invocation spec) (node : clangGraph.Index) (current : State) : Nat :=
  if node.val = 0 then WordMath.cardinality input.value + 1
  else WordMath.cardinality (current.registers .rdi)

private theorem low32_extend (value : BitVec 32) :
    (value.setWidth 64).setWidth 32 = value := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

private theorem lea_minus_one (value : Word) :
    value + 18446744073709551615#64 = value - 1 := by
  rw [BitVec.sub_eq_add_neg]
  rfl

private theorem test_nonzero (old value : Word) (af : Bool) (nonzero : value ≠ 0#64) :
    (logicalFlags64 old (value &&& value) af).getLsbD 6 = false := by
  rw [logicalFlags64_zero, BitVec.and_self]
  exact beq_eq_false_iff_ne.mpr nonzero

private theorem saved_protected (compiler : Compiler) :
    ∀ register ∈ PureCall.calleeSaved, register ≠ .rsp ∧ register ∉ scratch compiler := by
  cases compiler <;> decide +kernel

local macro "pop_frame" old:ident : tactic => `(tactic| (
  constructor
  · simp only [State.writeRegister, ($old).memory]
  · simpa only [logicalFlags32_preserves, logicalFlags64_preserves,
      addFlags32_preserves, incFlags32_preserves] using ($old).flags
  · intro register untouched
    have previous := ($old).registers register untouched
    simp only [scratch, List.mem_cons, List.mem_singleton, not_or] at untouched
    rcases untouched with ⟨notA, notB, notC⟩
    simpa only [State.writeRegister, notA, notB, notC, ite_false] using previous))

local macro "pop_return" "[" compiler:term "]" old:ident correct:ident : tactic => `(tactic| (
  vcgen_factor =>
    refine PureCall.ScratchFrame.post_return (scratch := scratch $compiler)
      ?_ (saved_protected $compiler) ?_ rfl rfl
    · constructor
      · simp only [State.writeRegister, ($old).memory]
      · simpa only [logicalFlags32_preserves, logicalFlags64_preserves,
          addFlags32_preserves, incFlags32_preserves] using ($old).flags
      · intro register untouched
        have separate : register ≠ .rsp ∧ register ∉ scratch $compiler := by
          simpa only [List.mem_cons, not_or] using untouched
        have previous := ($old).registers register separate.2
        have outside := separate.2
        simp only [scratch, List.mem_cons, List.mem_singleton, not_or] at outside
        rcases outside with ⟨notA, notB, notC⟩
        simpa only [State.writeRegister, separate.1, notA, notB, notC, ite_false] using previous
    · simpa [spec, PopcountCode.spec, Arithmetic64.populationCount, low32_extend] using $correct))

/-- Entry initialization and one least-set-bit clearing iteration are the
only sparse obligations. The natural invariant bounds the low32 counter and
supplies strict cardinality descent without restricting the input domain. -/
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
    have stack : readWord state.memory (state.registers .rsp) = .ok input.returnAddress := by
      simpa only [memory, rsp] using pre.stack
    have allowed : PureCall.RawRead initial ⟨.stack, initial.registers .rsp, 8⟩ :=
      ⟨rfl, rfl, rfl⟩
    have canonicalLoop : canonical (initial.rip + 16#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using gcc_valid.canonical_node binding.1 gccLoop
    have canonicalExit : canonical (initial.rip + 28#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using
        gcc_valid.canonical_node binding.1 (⟨9, by decide +kernel⟩ : gccGraph.Index)
    rcases cuts with same | same
    · subst cut
      have argument : state.registers .rdi = input.value := invariant
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node, gccGraph, gccEntry] using binding.2
      by_cases empty : input.value = 0#64
      · have correct : (0#32).toNat = WordMath.cardinality input.value := by simp [empty]
        change Cutpoints.wp gccGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (gccInv input initial)
          (gccRank input) (gccRank input gccEntry state) 12 gccEntry state
        vcgen_block gccGraph gccEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp,
          pre.stack, pre.returnCanonical, allowed, argument, empty,
          logicalFlags64_zero, canonicalExit, BitVec.add_assoc]
        pop_return [.defaultGCC] framed correct
      · have initialCount := WordMath.countInvariant_start (w := 64) (input.value : Word)
        have inputZf := fun (flags : Word) (af : Bool) => test_nonzero flags input.value af empty
        change Cutpoints.wp gccGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (gccInv input initial)
          (gccRank input) (gccRank input gccEntry state) 12 gccEntry state
        vcgen_block gccGraph gccEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory,
          argument, inputZf, BitVec.add_assoc]
        dsimp only [gccInv, gccRank]
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · pop_frame framed
        · simpa [argument] using initialCount
        · intro zero
          apply empty
          change state.registers .rdi = 0#64 at zero
          exact argument.symm.trans zero
        · simp [argument]
    · subst cut
      change WordMath.CountInvariant input.value (state.registers .rdi)
        ((state.registers .rdx).setWidth 32).toNat ∧ state.registers .rdi ≠ 0#64 at invariant
      have pc : state.rip = initial.rip + 16#64 := by
        simpa [CFG.Graph.node, gccGraph, gccLoop] using binding.2
      have increment := WordMath.countInvariant_increment32 invariant.1 invariant.2
        ((state.registers .rdx).setWidth 32) rfl
      have advanced : WordMath.CountInvariant input.value
          (state.registers .rdi &&& (state.registers .rdi - 1#64))
          (((state.registers .rdx).setWidth 32) + 1).toNat := by
        rw [increment]
        exact WordMath.countInvariant_step invariant.1 invariant.2
      have decreases := WordMath.cardinality_clear_lt (state.registers .rdi) invariant.2
      by_cases finished : state.registers .rdi &&& (state.registers .rdi - 1#64) = 0#64
      · have correct := WordMath.countInvariant_finish advanced finished
        change Cutpoints.wp gccGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (gccInv input initial)
          (gccRank input) (gccRank input gccLoop state) 7 gccLoop state
        vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp,
          pre.stack, pre.returnCanonical, allowed, finished,
          logicalFlags64_zero, LogicalOp.eval, lea_minus_one, BitVec.add_assoc]
        pop_return [.defaultGCC] framed correct
      · change Cutpoints.wp gccGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (gccInv input initial)
          (gccRank input) (gccRank input gccLoop state) 7 gccLoop state
        vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, finished,
          logicalFlags64_zero, LogicalOp.eval, lea_minus_one, canonicalLoop, BitVec.add_assoc]
        dsimp only [gccInv, gccRank]
        refine ⟨⟨?_, ?_, finished⟩, ?_⟩
        · pop_frame framed
        · simpa [low32_extend] using advanced
        · exact decreases

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
    have stack : readWord state.memory (state.registers .rsp) = .ok input.returnAddress := by
      simpa only [memory, rsp] using pre.stack
    have allowed : PureCall.RawRead initial ⟨.stack, initial.registers .rsp, 8⟩ :=
      ⟨rfl, rfl, rfl⟩
    have canonicalLoop : canonical (initial.rip + 16#64) = true := by
      simpa [CFG.Graph.node, clangGraph] using clang_valid.canonical_node binding.1 clangLoop
    have canonicalExit : canonical (initial.rip + 27#64) = true := by
      simpa [CFG.Graph.node, clangGraph] using
        clang_valid.canonical_node binding.1 (⟨8, by decide +kernel⟩ : clangGraph.Index)
    rcases cuts with same | same
    · subst cut
      have argument : state.registers .rdi = input.value := invariant
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node, clangGraph, clangEntry] using binding.2
      by_cases empty : input.value = 0#64
      · have correct : (0#32).toNat = WordMath.cardinality input.value := by simp [empty]
        change Cutpoints.wp clangGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (clangInv input initial)
          (clangRank input) (clangRank input clangEntry state) 10 clangEntry state
        vcgen_block clangGraph clangEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp,
          pre.stack, pre.returnCanonical, allowed, argument, empty,
          logicalFlags64_zero, canonicalExit, BitVec.add_assoc]
        pop_return [.defaultClang] framed correct
      · have initialCount := WordMath.countInvariant_start (w := 64) (input.value : Word)
        have inputZf := fun (flags : Word) (af : Bool) => test_nonzero flags input.value af empty
        change Cutpoints.wp clangGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (clangInv input initial)
          (clangRank input) (clangRank input clangEntry state) 10 clangEntry state
        vcgen_block clangGraph clangEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory,
          argument, inputZf, BitVec.add_assoc]
        dsimp only [clangInv, clangRank]
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · pop_frame framed
        · simpa [argument] using initialCount
        · intro zero
          apply empty
          change state.registers .rdi = 0#64 at zero
          exact argument.symm.trans zero
        · simp [argument]
    · subst cut
      change WordMath.CountInvariant input.value (state.registers .rdi)
        ((state.registers .rax).setWidth 32).toNat ∧ state.registers .rdi ≠ 0#64 at invariant
      have pc : state.rip = initial.rip + 16#64 := by
        simpa [CFG.Graph.node, clangGraph, clangLoop] using binding.2
      have increment := WordMath.countInvariant_increment32 invariant.1 invariant.2
        ((state.registers .rax).setWidth 32) rfl
      have advanced : WordMath.CountInvariant input.value
          (state.registers .rdi &&& (state.registers .rdi - 1#64))
          (((state.registers .rax).setWidth 32) + 1).toNat := by
        rw [increment]
        exact WordMath.countInvariant_step invariant.1 invariant.2
      have decreases := WordMath.cardinality_clear_lt (state.registers .rdi) invariant.2
      by_cases finished : state.registers .rdi &&& (state.registers .rdi - 1#64) = 0#64
      · have correct := WordMath.countInvariant_finish advanced finished
        change Cutpoints.wp clangGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (clangInv input initial)
          (clangRank input) (clangRank input clangLoop state) 6 clangLoop state
        vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp,
          pre.stack, pre.returnCanonical, allowed, finished,
          logicalFlags64_zero, LogicalOp.eval, lea_minus_one, BitVec.add_assoc]
        pop_return [.defaultClang] framed correct
      · change Cutpoints.wp clangGraph initial.rip (PureCall.Post spec input initial)
          (fun _ read => PureCall.RawRead initial read) (clangInv input initial)
          (clangRank input) (clangRank input clangLoop state) 6 clangLoop state
        vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, finished,
          logicalFlags64_zero, LogicalOp.eval, lea_minus_one, canonicalLoop, BitVec.add_assoc]
        dsimp only [clangInv, clangRank]
        refine ⟨⟨?_, ?_, finished⟩, ?_⟩
        · pop_frame framed
        · simpa [low32_extend] using advanced
        · exact decreases

/-- Uniform checked graph for the unchanged compiler-selected function. -/
def graph : Compiler → CFG.Graph
  | .defaultGCC => gccGraph
  | .defaultClang => clangGraph

theorem valid (compiler : Compiler) : CFG.Valid (bytes compiler) (graph compiler) := by
  cases compiler with
  | defaultGCC => exact gcc_valid
  | defaultClang => exact clang_valid

/-- Per-artifact evidence keeps a packet for one binary independent of another
compiler's annotation proofs. Initialization still uses the shared frame and
argument contract, with no result or execution premise. -/
theorem gcc_generated (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultGCC) input initial) :
    ∃ annotations : Cutpoints.Annotations (bytes .defaultGCC) gccGraph initial.rip
      (PureCall.Post spec input initial) (fun _ read => PureCall.RawRead initial read),
      annotations.Inv gcc_valid.entry initial := by
  refine ⟨gccAnnotations input initial pre, PureCall.ScratchFrame.refl _ _, ?_⟩
  exact (Arithmetic64.populationCount_bound_iff input.value initial).mp pre.arguments

theorem clang_generated (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultClang) input initial) :
    ∃ annotations : Cutpoints.Annotations (bytes .defaultClang) clangGraph initial.rip
      (PureCall.Post spec input initial) (fun _ read => PureCall.RawRead initial read),
      annotations.Inv clang_valid.entry initial := by
  refine ⟨clangAnnotations input initial pre, PureCall.ScratchFrame.refl _ _, ?_⟩
  exact (Arithmetic64.populationCount_bound_iff input.value initial).mp pre.arguments

/-- Cutpoint evidence covers every full64 input. Cardinality supplies progress;
the compiler-indexed convenience family contains both independently proved artifacts. -/
theorem generated (compiler : Compiler) (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes compiler) input initial) :
    ∃ annotations : Cutpoints.Annotations (bytes compiler) (graph compiler) initial.rip
      (PureCall.Post spec input initial) (fun _ read => PureCall.RawRead initial read),
      annotations.Inv (valid compiler).entry initial := by
  cases compiler with
  | defaultGCC => exact gcc_generated input initial pre
  | defaultClang => exact clang_generated input initial pre

theorem gcc_semantics :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) (bytes .defaultGCC) :=
  pureCall_semantics_of_cutpoints spec (bytes .defaultGCC) gccGraph gcc_valid gcc_generated

theorem clang_semantics :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) (bytes .defaultClang) :=
  pureCall_semantics_of_cutpoints spec (bytes .defaultClang) clangGraph clang_valid clang_generated

/-- Universal returning execution and original current caller/code authority
follow from the shared scalar cutpoint/resource bridge. The model's stable-RAM,
CET-off and absent-asynchronous-interference assumptions remain external. -/
theorem semantics (compiler : Compiler) :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) (bytes compiler) := by
  cases compiler with
  | defaultGCC => exact gcc_semantics
  | defaultClang => exact clang_semantics

end EDSL.Corpus.V1.PopcountBodies
