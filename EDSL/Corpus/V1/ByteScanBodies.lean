/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.ByteScan
import EDSL.X86.VCGen.Tactics
import EDSL.Corpus.V1.ByteScanWindows

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.ByteScanBodies
open X86 X86.Sequential X86.VCGen.ByteScan Grading.ByteScan

/-- Complete partitions, checked against the unchanged symbol bytes. Entry
and the byte-comparison header are the only cutpoints. Depth bounds only the
finite blocks between them, including the unreachable GCC padding byte. -/
abbrev gccGraph : CFG.Graph := ⟨[
  ⟨0, .endbr64IbtDisabled, true, 5⟩,
  ⟨4, .movReg64 .rax .rsi, false, 4⟩,
  ⟨7, .xorSelf32 .rdx, false, 3⟩,
  ⟨9, .test64 .rsi .rsi, false, 2⟩,
  ⟨12, .legacy (.jnz 0x0b), false, 1⟩,
  ⟨14, .legacy .ret, false, 0⟩,
  ⟨15, .nop .one, false, 4⟩,
  ⟨16, .addImm64 .rdx 1, false, 3⟩,
  ⟨20, .cmp64 .rax .rdx, false, 2⟩,
  ⟨23, .je 9, false, 1⟩,
  ⟨25, .cmpMemImm8 (.indexed .rdi .rdx 0) 0, true, 5⟩,
  ⟨29, .legacy (.jnz 0xf1), false, 4⟩,
  ⟨31, .movReg64 .rax .rdx, false, 1⟩,
  ⟨34, .legacy .ret, false, 0⟩], 5⟩

abbrev clangGraph : CFG.Graph := ⟨[
  ⟨0, .xorSelf32 .rax, true, 3⟩,
  ⟨2, .test64 .rsi .rsi, false, 2⟩,
  ⟨5, .je 0x1a, false, 1⟩,
  ⟨7, .nop .nine, false, 0⟩,
  ⟨16, .cmpMemImm8 (.indexed .rdi .rax 0) 0, true, 6⟩,
  ⟨20, .je 0x0b, false, 5⟩,
  ⟨22, .inc64 .rax, false, 4⟩,
  ⟨25, .cmp64 .rsi .rax, false, 3⟩,
  ⟨28, .legacy (.jnz 0xf2), false, 2⟩,
  ⟨30, .movReg64 .rax .rsi, false, 1⟩,
  ⟨33, .legacy .ret, false, 0⟩], 6⟩

theorem gcc_valid : CFG.Valid (ByteScanWindows.bytes .defaultGCC) gccGraph :=
  CFG.check_sound (by decide)

theorem clang_valid : CFG.Valid (ByteScanWindows.bytes .defaultClang) clangGraph :=
  CFG.check_sound (by decide)

abbrev gccEntry : gccGraph.Index := ⟨0, by decide⟩
abbrev gccLoop : gccGraph.Index := ⟨10, by decide⟩
abbrev clangEntry : clangGraph.Index := ⟨0, by decide⟩
abbrev clangLoop : clangGraph.Index := ⟨4, by decide⟩

/-- Both layouts use exactly the independent nonzero-prefix assertion. GCC
also retains n in RAX; Clang retains it in the framed argument RSI. -/
def gccInv (input : BufferCall.Invocation spec) (initial : State)
    (node : gccGraph.Index) (state : State) : Prop :=
  CommonFrame initial state ∧
    if node.val = 0 then True else
      NonzeroPrefix input.value.values (state.registers .rdx).toNat ∧
      (state.registers .rdx).toNat < input.value.values.length ∧
      state.registers .rax = BitVec.ofNat 64 input.value.values.length

def clangInv (input : BufferCall.Invocation spec) (initial : State)
    (node : clangGraph.Index) (state : State) : Prop :=
  CommonFrame initial state ∧
    if node.val = 0 then True else
      NonzeroPrefix input.value.values (state.registers .rax).toNat ∧
      (state.registers .rax).toNat < input.value.values.length

def gccRank (input : BufferCall.Invocation spec) (node : gccGraph.Index) (state : State) : Nat :=
  if node.val = 0 then input.value.values.length + 1
  else input.value.values.length - (state.registers .rdx).toNat

def clangRank (input : BufferCall.Invocation spec) (node : clangGraph.Index) (state : State) : Nat :=
  if node.val = 0 then input.value.values.length + 1
  else input.value.values.length - (state.registers .rax).toNat

/- Only finite blocks are reduced. Successor equality is proved in the kernel;
the annotations cannot select an instruction different from the checked bytes. -/
local macro "scan_frame" frame:ident : tactic => `(tactic| (
  simp only [commonFrame_iff, State.writeRegister, logicalFlags32_preserves,
    logicalFlags64_preserves, cmpFlags8_preserves, cmpFlags64_preserves,
    addFlags64_preserves, incFlags64_preserves, ($frame).memory, ($frame).flags,
    true_and, and_true]
  intro register notRax notRdx
  simpa only [notRax, notRdx, ite_false] using
    ($frame).registers register notRax notRdx))

local macro "scan_return" frame:ident correct:ident : tactic => `(tactic| (
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_⟩
  · simpa [BufferCall.Spec.scalarSpec, spec] using $correct
  · intro register saved
    have different := saved_different register saved
    simpa only [State.writeRegister, different.1, different.2.1, different.2.2, ite_false] using
      ($frame).registers register different.2.1 different.2.2
  · simpa only [logicalFlags32_preserves, logicalFlags64_preserves,
      cmpFlags8_preserves, cmpFlags64_preserves, addFlags64_preserves,
      incFlags64_preserves] using ($frame).flags))

/-- GCC's generated blocks: entry initializes i=0; the scan block either
returns i, increments i and returns n, or reaches the next byte comparison.
No interior assertions or instruction-by-instruction proof chain is supplied. -/
def gccAnnotations (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteScanWindows.bytes .defaultGCC) input initial) :
    VCGen.Cutpoints.Annotations (ByteScanWindows.bytes .defaultGCC) gccGraph initial.rip
      (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read) where
  Inv := gccInv input initial
  rank := gccRank input
  blocks cut state isCut binding admitted := by
    have cuts : cut = gccEntry ∨ cut = gccLoop := by
      have allCuts : ∀ node : gccGraph.Index,
          gccGraph.cutpoint node = true → node = gccEntry ∨ node = gccLoop := by decide
      exact allCuts cut isCut
    obtain ⟨frame, cursor⟩ := admitted
    have memory := frame.memory
    have rsp := frame.rsp
    have rdi : state.registers .rdi = input.value.base := frame.rdi.trans (base_argument pre)
    have rsi : state.registers .rsi = BitVec.ofNat 64 input.value.values.length :=
      frame.rsi.trans (count_argument pre)
    have stack : readWord state.memory (state.registers .rsp) = .ok input.returnAddress := by
      simpa only [memory, rsp] using pre.stack
    have stackAllowed : BufferCall.RawRead spec input initial
        ⟨.stack, initial.registers .rsp, 8⟩ := Or.inl ⟨rfl, rfl, rfl⟩
    have canonicalLoop : canonical (initial.rip + 25#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using gcc_valid.canonical_node binding.1 gccLoop
    have canonicalAdd : canonical (initial.rip + 16#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using
        gcc_valid.canonical_node binding.1 (⟨7, by decide⟩ : gccGraph.Index)
    have canonicalRet : canonical (initial.rip + 34#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using
        gcc_valid.canonical_node binding.1 (⟨13, by decide⟩ : gccGraph.Index)
    rcases cuts with same | same
    · subst cut
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node, gccGraph, gccEntry] using binding.2
      by_cases empty : input.value.values.length = 0
      · have correct : BoundedNulLength input.value.values 0 :=
          (NonzeroPrefix.start _).finish_bound empty.symm
        change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (gccInv input initial) (gccRank input) (gccRank input gccEntry state) 6 gccEntry state
        vcgen_block gccGraph gccEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp, rsi, pre.stack, pre.returnCanonical, stackAllowed, empty,
            logicalFlags64_zero, BitVec.add_assoc]
        scan_return frame correct
      · have countNonzero : BitVec.ofNat 64 input.value.values.length ≠ 0#64 := by
          intro zero
          have := congrArg BitVec.toNat zero
          rw [count_nat pre] at this
          exact empty this
        change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (gccInv input initial) (gccRank input) (gccRank input gccEntry state) 6 gccEntry state
        vcgen_block gccGraph gccEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsi, countNonzero,
            logicalFlags64_zero, canonicalLoop, BitVec.add_assoc]
        dsimp only [gccInv, gccRank]
        refine ⟨⟨?_, NonzeroPrefix.start _, ?_, rfl⟩, by simp⟩
        · scan_frame frame
        · change 0 < input.value.values.length
          omega
    · subst cut
      change NonzeroPrefix input.value.values (state.registers .rdx).toNat ∧
        (state.registers .rdx).toNat < input.value.values.length ∧
        state.registers .rax = BitVec.ofNat 64 input.value.values.length at cursor
      have pc : state.rip = initial.rip + 25#64 := by
        simpa [CFG.Graph.node, gccGraph, gccLoop] using binding.2
      obtain ⟨byte, present, loaded, dataAllowed⟩ := read_byte pre frame cursor.2.1
      simp only [memory, BitVec.ofNat_toNat, BitVec.setWidth_eq] at loaded dataAllowed
      have nextNat := next_nat (count_small pre) cursor.2.1
      have nextLe : (state.registers .rdx + 1).toNat ≤ input.value.values.length := by
        rw [nextNat]; omega
      by_cases zero : byte = 0
      · have correct := cursor.1.finish_zero (by simpa [zero] using present)
        change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (gccInv input initial) (gccRank input) (gccRank input gccLoop state) 6 gccLoop state
        vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp, rdi, loaded, dataAllowed, pre.stack, pre.returnCanonical, stackAllowed,
            zero, cmpFlags8_zero, BitVec.add_assoc]
        scan_return frame correct
      · have advanced := advance (count_small pre) cursor.2.1 cursor.1 present zero
        have byteZf : ∀ flags : Word, (cmpFlags8 flags byte 0#8).getLsbD 6 = false := by
          intro flags
          rw [cmpFlags8_zero]
          exact beq_eq_false_iff_ne.mpr zero
        by_cases last : (state.registers .rdx + 1).toNat = input.value.values.length
        · have equal : BitVec.ofNat 64 input.value.values.length = state.registers .rdx + 1 :=
            BitVec.eq_of_toNat_eq ((count_nat pre).trans last.symm)
          have correct : BoundedNulLength input.value.values (state.registers .rax).toNat := by
            rw [cursor.2.2, equal]
            exact advanced.finish_bound last
          change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (gccInv input initial) (gccRank input) (gccRank input gccLoop state) 6 gccLoop state
          vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp, rdi, loaded, dataAllowed, pre.stack, pre.returnCanonical, stackAllowed,
              byteZf, cmpFlags64_zero, cursor.2.2, equal,
              canonicalAdd, canonicalRet, BitVec.add_assoc]
          scan_return frame correct
        · have different : BitVec.ofNat 64 input.value.values.length ≠ state.registers .rdx + 1 := by
            intro equal
            exact last ((congrArg BitVec.toNat equal).symm.trans (count_nat pre))
          have countZf : ∀ flags : Word,
              (cmpFlags64 flags (BitVec.ofNat 64 input.value.values.length)
                (state.registers .rdx + 1#64)).getLsbD 6 = false := by
            intro flags
            rw [cmpFlags64_zero]
            exact beq_eq_false_iff_ne.mpr different
          change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (gccInv input initial) (gccRank input) (gccRank input gccLoop state) 6 gccLoop state
          vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rdi, loaded, dataAllowed, byteZf, countZf,
              cursor.2.2, canonicalAdd, BitVec.add_assoc]
          dsimp only [gccInv, gccRank]
          refine ⟨⟨?_, advanced, ?_, cursor.2.2⟩, ?_⟩
          · scan_frame frame
          · change (state.registers .rdx + 1).toNat < input.value.values.length
            omega
          · exact next_rank (count_small pre) cursor.2.1

/-- Clang's annotation uses the same frame, snapshot reads and prefix step.
Only the register layout and finite generated blocks differ from GCC. -/
def clangAnnotations (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteScanWindows.bytes .defaultClang) input initial) :
    VCGen.Cutpoints.Annotations (ByteScanWindows.bytes .defaultClang) clangGraph initial.rip
      (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read) where
  Inv := clangInv input initial
  rank := clangRank input
  blocks cut state isCut binding admitted := by
    have cuts : cut = clangEntry ∨ cut = clangLoop := by
      have allCuts : ∀ node : clangGraph.Index,
          clangGraph.cutpoint node = true → node = clangEntry ∨ node = clangLoop := by decide
      exact allCuts cut isCut
    obtain ⟨frame, cursor⟩ := admitted
    have memory := frame.memory
    have rsp := frame.rsp
    have rdi : state.registers .rdi = input.value.base := frame.rdi.trans (base_argument pre)
    have rsi : state.registers .rsi = BitVec.ofNat 64 input.value.values.length :=
      frame.rsi.trans (count_argument pre)
    have stackAllowed : BufferCall.RawRead spec input initial
        ⟨.stack, initial.registers .rsp, 8⟩ := Or.inl ⟨rfl, rfl, rfl⟩
    have canonicalLoop : canonical (initial.rip + 16#64) = true := by
      simpa [CFG.Graph.node, clangGraph] using clang_valid.canonical_node binding.1 clangLoop
    have canonicalRet : canonical (initial.rip + 33#64) = true := by
      simpa [CFG.Graph.node, clangGraph] using
        clang_valid.canonical_node binding.1 (⟨10, by decide⟩ : clangGraph.Index)
    rcases cuts with same | same
    · subst cut
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node, clangGraph, clangEntry] using binding.2
      by_cases empty : input.value.values.length = 0
      · have correct : BoundedNulLength input.value.values 0 :=
          (NonzeroPrefix.start _).finish_bound empty.symm
        change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (clangInv input initial) (clangRank input) (clangRank input clangEntry state) 4 clangEntry state
        vcgen_block clangGraph clangEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp, rsi, pre.stack, pre.returnCanonical,
            stackAllowed, empty, logicalFlags64_zero, canonicalRet, BitVec.add_assoc]
        scan_return frame correct
      · have countNonzero : BitVec.ofNat 64 input.value.values.length ≠ 0#64 := by
          intro zero
          have := congrArg BitVec.toNat zero
          rw [count_nat pre] at this
          exact empty this
        change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (clangInv input initial) (clangRank input) (clangRank input clangEntry state) 4 clangEntry state
        vcgen_block clangGraph clangEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsi, countNonzero,
            logicalFlags64_zero, BitVec.add_assoc]
        dsimp only [clangInv, clangRank]
        refine ⟨⟨?_, NonzeroPrefix.start _, ?_⟩, by simp⟩
        · scan_frame frame
        · change 0 < input.value.values.length
          omega
    · subst cut
      change NonzeroPrefix input.value.values (state.registers .rax).toNat ∧
        (state.registers .rax).toNat < input.value.values.length at cursor
      have pc : state.rip = initial.rip + 16#64 := by
        simpa [CFG.Graph.node, clangGraph, clangLoop] using binding.2
      obtain ⟨byte, present, loaded, dataAllowed⟩ := read_byte pre frame cursor.2
      simp only [memory, BitVec.ofNat_toNat, BitVec.setWidth_eq] at loaded dataAllowed
      have nextNat := next_nat (count_small pre) cursor.2
      have nextLe : (state.registers .rax + 1).toNat ≤ input.value.values.length := by
        rw [nextNat]; omega
      by_cases zero : byte = 0
      · have correct := cursor.1.finish_zero (by simpa [zero] using present)
        change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (clangInv input initial) (clangRank input) (clangRank input clangLoop state) 7 clangLoop state
        vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp, rdi, loaded, dataAllowed,
            pre.stack, pre.returnCanonical, stackAllowed, zero, cmpFlags8_zero,
            canonicalRet, BitVec.add_assoc]
        scan_return frame correct
      · have advanced := advance (count_small pre) cursor.2 cursor.1 present zero
        have byteZf : ∀ flags : Word, (cmpFlags8 flags byte 0#8).getLsbD 6 = false := by
          intro flags
          rw [cmpFlags8_zero]
          exact beq_eq_false_iff_ne.mpr zero
        by_cases last : (state.registers .rax + 1).toNat = input.value.values.length
        · have equal : BitVec.ofNat 64 input.value.values.length = state.registers .rax + 1 :=
            BitVec.eq_of_toNat_eq ((count_nat pre).trans last.symm)
          have correct := advanced.finish_bound last
          change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (clangInv input initial) (clangRank input) (clangRank input clangLoop state) 7 clangLoop state
          vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp, rdi, rsi, loaded, dataAllowed,
              pre.stack, pre.returnCanonical, stackAllowed, byteZf, cmpFlags64_zero,
              equal, BitVec.add_assoc]
          scan_return frame correct
        · have different : BitVec.ofNat 64 input.value.values.length ≠ state.registers .rax + 1 := by
            intro equal
            exact last ((congrArg BitVec.toNat equal).symm.trans (count_nat pre))
          have countZf : ∀ flags : Word,
              (cmpFlags64 flags (BitVec.ofNat 64 input.value.values.length)
                (state.registers .rax + 1#64)).getLsbD 6 = false := by
            intro flags
            rw [cmpFlags64_zero]
            exact beq_eq_false_iff_ne.mpr different
          change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (clangInv input initial) (clangRank input) (clangRank input clangLoop state) 7 clangLoop state
          vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rdi, rsi, loaded, dataAllowed,
              byteZf, countZf, canonicalLoop, BitVec.add_assoc]
          dsimp only [clangInv, clangRank]
          refine ⟨⟨?_, advanced, ?_⟩, ?_⟩
          · scan_frame frame
          · change (state.registers .rax + 1).toNat < input.value.values.length
            omega
          · exact next_rank (count_small pre) cursor.2

def graph : ByteScanWindows.Compiler → CFG.Graph
  | .defaultGCC => gccGraph
  | .defaultClang => clangGraph

theorem valid (compiler : ByteScanWindows.Compiler) :
    CFG.Valid (ByteScanWindows.bytes compiler) (graph compiler) := by
  cases compiler
  · exact gcc_valid
  · exact clang_valid

/-- A selector for the two layout annotations, not an additional checker. -/
def annotations (compiler : ByteScanWindows.Compiler) (input : BufferCall.Invocation spec)
    (initial : State) (pre : BufferCall.Pre spec (ByteScanWindows.bytes compiler) input initial) :
    VCGen.Cutpoints.Annotations (ByteScanWindows.bytes compiler) (graph compiler) initial.rip
      (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read) := by
  cases compiler
  · exact gccAnnotations input initial pre
  · exact clangAnnotations input initial pre

theorem entry_invariant (compiler : ByteScanWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteScanWindows.bytes compiler) input initial) :
    (annotations compiler input initial pre).Inv (valid compiler).entry initial := by
  cases compiler <;> exact ⟨CommonFrame.refl initial, True.intro⟩

theorem generated (compiler : ByteScanWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteScanWindows.bytes compiler) input initial) :
    ∃ evidence : VCGen.Cutpoints.Annotations (ByteScanWindows.bytes compiler)
        (graph compiler) initial.rip (BufferCall.Post spec input initial)
        (fun _ read => BufferCall.RawRead spec input initial read),
      evidence.Inv (valid compiler).entry initial :=
  ⟨annotations compiler input initial pre, entry_invariant compiler input initial pre⟩

/-- Universal raw correctness and permitted reads for the unchanged present-only
precondition, every finite list with n < 2^64, arbitrary initial machine state,
code relocation and AF stream. The dynamic rank is proof evidence only. -/
theorem raw (compiler : ByteScanWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteScanWindows.bytes compiler) input initial) :
    AllExecutions initial (fun result => BufferCall.Post spec input initial result.state) ∧
      BufferCall.RawPolicy spec input initial :=
  VCGen.bufferCall_raw_of_cutpoints spec _ _ (valid compiler) (generated compiler) input initial pre

/-- Independent bounded-NUL semantics for BOTH complete frozen symbol windows.
The generic bridge supplies full RAM/ABI frames and actual current original
call/buffer authority at every continuing prefix and after return. Compatible
read-only aliases are admitted. Empty input never requires a data loan or
canonical data pointer. This is the represented sequential callable model;
native loading/hardware correspondence and corpus registration are separate. -/
theorem semantics (compiler : ByteScanWindows.Compiler) :
    Grading.ReadOnlySemanticClaim (BufferCall.readOnlyTask Grading.ByteScan.spec)
      (ByteScanWindows.bytes compiler) :=
  VCGen.bufferCall_semantics_of_cutpoints spec _ _ (valid compiler) (generated compiler)

/-- Conservative model-instruction budget, obtained as an output from the
production rank theorem. It is neither an optimal bound nor hardware cost. -/
theorem dynamic_bound (compiler : ByteScanWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteScanWindows.bytes compiler) input initial) (choices : Choices) :
    ∃ result, Sequential.run choices
        (((graph compiler).maxDepth + 1) * (input.value.values.length + 2)) initial = .ok result ∧
      BufferCall.Post spec input initial result.state ∧
      result.instructions ≤ ((graph compiler).maxDepth + 1) * (input.value.values.length + 2) := by
  have binding : CFG.At (ByteScanWindows.bytes compiler) (graph compiler) initial.rip
      (valid compiler).entry initial := by
    refine ⟨pre.code, ?_⟩
    simp [(valid compiler).entry_offset]
  have total := (annotations compiler input initial pre).sound (valid compiler)
    (valid compiler).entry_cutpoint binding (entry_invariant compiler input initial pre) choices
  cases compiler <;> exact total

end EDSL.Corpus.V1.ByteScanBodies
