/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.ByteComparison
import EDSL.X86.VCGen.Tactics
import EDSL.Corpus.V1.ByteComparisonWindows

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.ByteComparisonBodies
open X86 X86.Sequential X86.VCGen.ByteComparison Grading.ByteComparison

/-- Complete partitions, including unreachable padding. The only cutpoints
are entry and the first byte load. Static depth bounds a block, never n. -/
abbrev gccGraph : CFG.Graph := ⟨[
  ⟨0, .endbr64IbtDisabled, true, 8⟩,
  ⟨4, .test64 .rdx .rdx, false, 7⟩,
  ⟨7, .je 0x27, false, 6⟩,
  ⟨9, .xorSelf32 .rax, false, 5⟩,
  ⟨11, .jmp 0x0c, false, 0⟩,
  ⟨13, .nop .three, false, 5⟩,
  ⟨16, .addImm64 .rax 1, false, 4⟩,
  ⟨20, .cmp64 .rdx .rax, false, 3⟩,
  ⟨23, .je 0x17, false, 2⟩,
  ⟨25, .movzxMem8 .rcx (.indexed .rdi .rax 0) false, true, 8⟩,
  ⟨29, .movzxMem8 .r8 (.indexed .rsi .rax 0) true, false, 7⟩,
  ⟨34, .cmpReg8 .rcx .r8 true, false, 6⟩,
  ⟨37, .je 0xe9, false, 5⟩,
  ⟨39, .movzxReg8 .rax .rcx false, false, 2⟩,
  ⟨42, .subReg32 .rax .r8 true, false, 1⟩,
  ⟨45, .legacy .ret, false, 0⟩,
  ⟨46, .nop .two, false, 2⟩,
  ⟨48, .xorSelf32 .rax, false, 1⟩,
  ⟨50, .legacy .ret, false, 0⟩], 8⟩

abbrev clangGraph : CFG.Graph := ⟨[
  ⟨0, .test64 .rdx .rdx, true, 8⟩,
  ⟨3, .je 0x21, false, 7⟩,
  ⟨5, .xorSelf32 .rcx, false, 6⟩,
  ⟨7, .nop .nine, false, 0⟩,
  ⟨16, .movzxMem8 .rax (.indexed .rdi .rcx 0) false, true, 8⟩,
  ⟨20, .movzxMem8 .r8 (.indexed .rsi .rcx 0) true, false, 7⟩,
  ⟨25, .cmpReg8 .rax .r8 true, false, 6⟩,
  ⟨28, .legacy (.jnz 0x0b), false, 5⟩,
  ⟨30, .inc64 .rcx, false, 4⟩,
  ⟨33, .cmp64 .rdx .rcx, false, 3⟩,
  ⟨36, .legacy (.jnz 0xea), false, 2⟩,
  ⟨38, .xorSelf32 .rax, false, 1⟩,
  ⟨40, .legacy .ret, false, 0⟩,
  ⟨41, .subReg32 .rax .r8 true, false, 1⟩,
  ⟨44, .legacy .ret, false, 0⟩], 8⟩

theorem gcc_valid : CFG.Valid (ByteComparisonWindows.bytes .defaultGCC) gccGraph :=
  CFG.check_sound (by decide +kernel)
theorem clang_valid : CFG.Valid (ByteComparisonWindows.bytes .defaultClang) clangGraph :=
  CFG.check_sound (by decide +kernel)

abbrev gccEntry : gccGraph.Index := ⟨0, by decide⟩
abbrev gccLoop : gccGraph.Index := ⟨9, by decide⟩
abbrev clangEntry : clangGraph.Index := ⟨0, by decide⟩
abbrev clangLoop : clangGraph.Index := ⟨4, by decide⟩

def gccInv (input : BufferCall.Invocation spec) (initial : State)
    (node : gccGraph.Index) (state : State) : Prop :=
  CommonFrame initial state ∧ if node.val = 0 then True else
    EqualPrefix (view input.value) (state.registers .rax).toNat ∧
    (state.registers .rax).toNat < (view input.value).left.length
def clangInv (input : BufferCall.Invocation spec) (initial : State)
    (node : clangGraph.Index) (state : State) : Prop :=
  CommonFrame initial state ∧ if node.val = 0 then True else
    EqualPrefix (view input.value) (state.registers .rcx).toNat ∧
    (state.registers .rcx).toNat < (view input.value).left.length

def gccRank (input : BufferCall.Invocation spec) (node : gccGraph.Index) (state : State) : Nat :=
  if node.val = 0 then (view input.value).left.length + 1
  else (view input.value).left.length - (state.registers .rax).toNat
def clangRank (input : BufferCall.Invocation spec) (node : clangGraph.Index) (state : State) : Nat :=
  if node.val = 0 then (view input.value).left.length + 1
  else (view input.value).left.length - (state.registers .rcx).toNat

local macro "paired_frame" frame:ident : tactic => `(tactic| (
  simp only [commonFrame_iff, State.writeRegister, logicalFlags32_preserves,
    logicalFlags64_preserves, cmpFlags8_preserves, cmpFlags32_preserves, cmpFlags64_preserves,
    addFlags64_preserves, incFlags64_preserves, ($frame).memory, ($frame).flags,
    true_and, and_true]
  intro register notRax notRcx notR8
  simpa only [notRax, notRcx, notR8, ite_false] using
    ($frame).registers register notRax notRcx notR8))

local macro "paired_return" frame:ident correct:ident : tactic => `(tactic| (
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_⟩
  · simpa [BufferCall.Spec.scalarSpec] using $correct
  · intro register saved
    have different := saved_different register saved
    simpa only [State.writeRegister, different.1, different.2.1, different.2.2.1,
      different.2.2.2, ite_false] using
      ($frame).registers register different.2.1 different.2.2.1 different.2.2.2
  · simpa only [logicalFlags32_preserves, logicalFlags64_preserves, cmpFlags8_preserves,
      cmpFlags32_preserves, cmpFlags64_preserves, addFlags64_preserves,
      incFlags64_preserves] using ($frame).flags))

/-- GCC's sparse annotation uses RAX as the full-width cursor. MOVZX clears
both byte temporaries before CMP8; only an unequal pair reaches SUB32. -/
def gccAnnotations (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteComparisonWindows.bytes .defaultGCC) input initial) :
    VCGen.Cutpoints.Annotations (ByteComparisonWindows.bytes .defaultGCC) gccGraph initial.rip
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
    have rdi := frame.rdi.trans (left_argument pre)
    have rsi := frame.rsi.trans (right_argument pre)
    have rdx := frame.rdx.trans (count_argument pre)
    have stackAllowed : BufferCall.RawRead spec input initial
        ⟨.stack, initial.registers .rsp, 8⟩ := Or.inl ⟨rfl, rfl, rfl⟩
    have canonicalLoop : canonical (initial.rip + 25#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using gcc_valid.canonical_node binding.1 gccLoop
    have canonicalInc : canonical (initial.rip + 16#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using
        gcc_valid.canonical_node binding.1 (⟨6, by decide⟩ : gccGraph.Index)
    have canonicalEqual : canonical (initial.rip + 48#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using
        gcc_valid.canonical_node binding.1 (⟨17, by decide⟩ : gccGraph.Index)
    rcases cuts with same | same
    · subst cut
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node, gccGraph, gccEntry] using binding.2
      by_cases empty : (view input.value).left.length = 0
      · have correct : spec.result input.value 0 :=
          finish_bound pre (Grading.FirstMatch.Prefix.start _ _) empty.symm rfl
        change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (gccInv input initial) (gccRank input) (gccRank input gccEntry state) 9 gccEntry state
        vcgen_block gccGraph gccEntry simp [-BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rsp, rdx, pre.stack, pre.returnCanonical,
          stackAllowed, empty, logicalFlags64_zero, canonicalEqual]
        paired_return frame correct
      · have countNonzero : BitVec.ofNat 64 (view input.value).left.length ≠ 0#64 := by
          intro zero
          exact empty (by simpa only [count_nat pre, BitVec.toNat_zero] using congrArg BitVec.toNat zero)
        change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (gccInv input initial) (gccRank input) (gccRank input gccEntry state) 9 gccEntry state
        vcgen_block gccGraph gccEntry simp [-BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rdx, countNonzero, logicalFlags64_zero, canonicalLoop]
        dsimp only [gccInv, gccRank]
        refine ⟨⟨?_, Grading.FirstMatch.Prefix.start _ _, ?_⟩, by simp⟩
        · paired_frame frame
        · change 0 < (view input.value).left.length
          omega
    · subst cut
      change EqualPrefix (view input.value) (state.registers .rax).toNat ∧
        (state.registers .rax).toNat < (view input.value).left.length at cursor
      have pc : state.rip = initial.rip + 25#64 := by
        simpa [CFG.Graph.node, gccGraph, gccLoop] using binding.2
      obtain ⟨a, b, leftAt, rightAt, loadedA, loadedB, allowedA, allowedB⟩ := read_pair pre frame cursor.2
      simp only [memory, BitVec.ofNat_toNat, BitVec.setWidth_eq] at loadedA loadedB allowedA allowedB
      by_cases equalBytes : a = b
      · have advanced := advance pre cursor.2 cursor.1 leftAt rightAt equalBytes
        have nextNat := next_nat (count_small pre) cursor.2
        have nextLe : (state.registers .rax + 1).toNat ≤ (view input.value).left.length := by
          rw [nextNat]; omega
        by_cases last : (state.registers .rax + 1).toNat = (view input.value).left.length
        · have countEqual : BitVec.ofNat 64 (view input.value).left.length = state.registers .rax + 1 :=
            BitVec.eq_of_toNat_eq ((count_nat pre).trans last.symm)
          have correct : spec.result input.value 0 := finish_bound pre advanced last rfl
          change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (gccInv input initial) (gccRank input) (gccRank input gccLoop state) 9 gccLoop state
          vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rsp, rdi, rsi, rdx, loadedA, loadedB,
            allowedA, allowedB, pre.stack, pre.returnCanonical, stackAllowed, equalBytes,
            cmpFlags8_zero, cmpFlags64_zero, countEqual, canonicalInc, canonicalEqual]
          paired_return frame correct
        · have countDifferent : BitVec.ofNat 64 (view input.value).left.length ≠ state.registers .rax + 1 := by
            intro equal
            exact last ((congrArg BitVec.toNat equal).symm.trans (count_nat pre))
          have countZf : ∀ flags : Word,
              (cmpFlags64 flags (BitVec.ofNat 64 (view input.value).left.length)
                (state.registers .rax + 1#64)).getLsbD 6 = false := by
            intro flags
            rw [cmpFlags64_zero]
            exact beq_eq_false_iff_ne.mpr countDifferent
          change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (gccInv input initial) (gccRank input) (gccRank input gccLoop state) 9 gccLoop state
          vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rdi, rsi, rdx, loadedA, loadedB,
            allowedA, allowedB, equalBytes, cmpFlags8_zero, countZf, canonicalInc]
          dsimp only [gccInv, gccRank]
          refine ⟨⟨?_, advanced, ?_⟩, ?_⟩
          · paired_frame frame
          · change (state.registers .rax + 1).toNat < (view input.value).left.length
            omega
          · exact next_rank (count_small pre) cursor.2
      · have correct := finish_hit pre cursor.1 leftAt rightAt equalBytes (sub_return a b)
        change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (gccInv input initial) (gccRank input) (gccRank input gccLoop state) 9 gccLoop state
        vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rsp, rdi, rsi, loadedA, loadedB,
          allowedA, allowedB, pre.stack, pre.returnCanonical, stackAllowed, equalBytes, cmpFlags8_zero]
        paired_return frame correct

/-- Clang uses RCX as cursor and directly keeps the left MOVZX value in EAX.
The frame, paired reads, prefix step, rank and sign bridge are shared. -/
def clangAnnotations (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteComparisonWindows.bytes .defaultClang) input initial) :
    VCGen.Cutpoints.Annotations (ByteComparisonWindows.bytes .defaultClang) clangGraph initial.rip
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
    have rdi := frame.rdi.trans (left_argument pre)
    have rsi := frame.rsi.trans (right_argument pre)
    have rdx := frame.rdx.trans (count_argument pre)
    have stackAllowed : BufferCall.RawRead spec input initial
        ⟨.stack, initial.registers .rsp, 8⟩ := Or.inl ⟨rfl, rfl, rfl⟩
    have canonicalLoop : canonical (initial.rip + 16#64) = true := by
      simpa [CFG.Graph.node, clangGraph] using clang_valid.canonical_node binding.1 clangLoop
    have canonicalHit : canonical (initial.rip + 41#64) = true := by
      simpa [CFG.Graph.node, clangGraph] using
        clang_valid.canonical_node binding.1 (⟨13, by decide⟩ : clangGraph.Index)
    have canonicalEqual : canonical (initial.rip + 38#64) = true := by
      simpa [CFG.Graph.node, clangGraph] using
        clang_valid.canonical_node binding.1 (⟨11, by decide⟩ : clangGraph.Index)
    rcases cuts with same | same
    · subst cut
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node, clangGraph, clangEntry] using binding.2
      by_cases empty : (view input.value).left.length = 0
      · have correct : spec.result input.value 0 :=
          finish_bound pre (Grading.FirstMatch.Prefix.start _ _) empty.symm rfl
        change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (clangInv input initial) (clangRank input) (clangRank input clangEntry state) 9 clangEntry state
        vcgen_block clangGraph clangEntry simp [-BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rsp, rdx,
          pre.stack, pre.returnCanonical, stackAllowed, empty, logicalFlags64_zero, canonicalEqual]
        paired_return frame correct
      · have countNonzero : BitVec.ofNat 64 (view input.value).left.length ≠ 0#64 := by
          intro zero
          exact empty (by simpa only [count_nat pre, BitVec.toNat_zero] using congrArg BitVec.toNat zero)
        change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (clangInv input initial) (clangRank input) (clangRank input clangEntry state) 9 clangEntry state
        vcgen_block clangGraph clangEntry simp [-BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rdx,
          countNonzero, logicalFlags64_zero]
        dsimp only [clangInv, clangRank]
        refine ⟨⟨?_, Grading.FirstMatch.Prefix.start _ _, ?_⟩, by simp⟩
        · paired_frame frame
        · change 0 < (view input.value).left.length
          omega
    · subst cut
      change EqualPrefix (view input.value) (state.registers .rcx).toNat ∧
        (state.registers .rcx).toNat < (view input.value).left.length at cursor
      have pc : state.rip = initial.rip + 16#64 := by
        simpa [CFG.Graph.node, clangGraph, clangLoop] using binding.2
      obtain ⟨a, b, leftAt, rightAt, loadedA, loadedB, allowedA, allowedB⟩ := read_pair pre frame cursor.2
      simp only [memory, BitVec.ofNat_toNat, BitVec.setWidth_eq] at loadedA loadedB allowedA allowedB
      by_cases equalBytes : a = b
      · have advanced := advance pre cursor.2 cursor.1 leftAt rightAt equalBytes
        have nextNat := next_nat (count_small pre) cursor.2
        have nextLe : (state.registers .rcx + 1).toNat ≤ (view input.value).left.length := by
          rw [nextNat]; omega
        by_cases last : (state.registers .rcx + 1).toNat = (view input.value).left.length
        · have countEqual : BitVec.ofNat 64 (view input.value).left.length = state.registers .rcx + 1 :=
            BitVec.eq_of_toNat_eq ((count_nat pre).trans last.symm)
          have correct : spec.result input.value 0 := finish_bound pre advanced last rfl
          change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (clangInv input initial) (clangRank input) (clangRank input clangLoop state) 9 clangLoop state
          vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rsp, rdi, rsi, rdx,
            loadedA, loadedB, allowedA, allowedB, pre.stack, pre.returnCanonical, stackAllowed,
            equalBytes, cmpFlags8_zero, cmpFlags64_zero, countEqual]
          paired_return frame correct
        · have countDifferent : BitVec.ofNat 64 (view input.value).left.length ≠ state.registers .rcx + 1 := by
            intro equal
            exact last ((congrArg BitVec.toNat equal).symm.trans (count_nat pre))
          have countZf : ∀ flags : Word,
              (cmpFlags64 flags (BitVec.ofNat 64 (view input.value).left.length)
                (state.registers .rcx + 1#64)).getLsbD 6 = false := by
            intro flags
            rw [cmpFlags64_zero]
            exact beq_eq_false_iff_ne.mpr countDifferent
          change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (clangInv input initial) (clangRank input) (clangRank input clangLoop state) 9 clangLoop state
          vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rdi, rsi, rdx,
            loadedA, loadedB, allowedA, allowedB, equalBytes, cmpFlags8_zero, countZf, canonicalLoop]
          dsimp only [clangInv, clangRank]
          refine ⟨⟨?_, advanced, ?_⟩, ?_⟩
          · paired_frame frame
          · change (state.registers .rcx + 1).toNat < (view input.value).left.length
            omega
          · exact next_rank (count_small pre) cursor.2
      · have correct := finish_hit pre cursor.1 leftAt rightAt equalBytes (sub_return a b)
        change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (clangInv input initial) (clangRank input) (clangRank input clangLoop state) 9 clangLoop state
        vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rsp, rdi, rsi,
          loadedA, loadedB, allowedA, allowedB, pre.stack, pre.returnCanonical, stackAllowed,
          equalBytes, cmpFlags8_zero, canonicalHit]
        paired_return frame correct

def graph : ByteComparisonWindows.Compiler → CFG.Graph
  | .defaultGCC => gccGraph
  | .defaultClang => clangGraph

theorem valid (compiler : ByteComparisonWindows.Compiler) :
    CFG.Valid (ByteComparisonWindows.bytes compiler) (graph compiler) := by
  cases compiler
  · exact gcc_valid
  · exact clang_valid

def annotations (compiler : ByteComparisonWindows.Compiler) (input : BufferCall.Invocation spec)
    (initial : State) (pre : BufferCall.Pre spec (ByteComparisonWindows.bytes compiler) input initial) :
    VCGen.Cutpoints.Annotations (ByteComparisonWindows.bytes compiler) (graph compiler) initial.rip
      (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read) := by
  cases compiler
  · exact gccAnnotations input initial pre
  · exact clangAnnotations input initial pre

theorem entry_invariant (compiler : ByteComparisonWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteComparisonWindows.bytes compiler) input initial) :
    (annotations compiler input initial pre).Inv (valid compiler).entry initial := by
  cases compiler <;> exact ⟨CommonFrame.refl initial, True.intro⟩

theorem generated (compiler : ByteComparisonWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteComparisonWindows.bytes compiler) input initial) :
    ∃ annotation : VCGen.Cutpoints.Annotations (ByteComparisonWindows.bytes compiler) (graph compiler)
      initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read),
      annotation.Inv (valid compiler).entry initial :=
  ⟨annotations compiler input initial pre, entry_invariant compiler input initial pre⟩

theorem raw (compiler : ByteComparisonWindows.Compiler) :
    ∀ input initial, BufferCall.Pre spec (ByteComparisonWindows.bytes compiler) input initial →
      Sequential.AllExecutions initial (fun result => BufferCall.Post spec input initial result.state) ∧
      BufferCall.RawPolicy spec input initial :=
  VCGen.bufferCall_raw_of_cutpoints spec _ _ (valid compiler) (generated compiler)

/-- Every continuing prefix of an empty call needs only original STACK8
authority. Both bases and all scratch bits are arbitrary; no data address or
data-loan selector is inspected. The policy still quantifies over both AFs. -/
theorem empty_raw_policy (compiler : ByteComparisonWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteComparisonWindows.bytes compiler) input initial)
    (emptyLeft : (view input.value).left = []) (emptyRight : (view input.value).right = []) :
    Grading.ReadOnlyPolicy initial (fun before => before.memory = initial.memory)
      (fun _ read => PureCall.RawRead initial read) := by
  apply (raw compiler input initial pre).2.mono (fun _ frame => frame)
  intro _ read allowed
  rcases allowed with stack | data
  · exact stack
  · have noData : ¬BufferCall.DataRead
        [leftBuffer (view input.value), rightBuffer (view input.value)] read := by
      apply BufferCall.DataRead.no_empty
      intro buffer member
      have cases : buffer = leftBuffer (view input.value) ∨ buffer = rightBuffer (view input.value) := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
      rcases cases with rfl | rfl
      · exact emptyLeft
      · exact emptyRight
    exact False.elim (noData data)

/-- Universal fixed-contract semantics of both exact complete frozen bodies.
The production cutpoint bridge retains current resources at every prefix and
return, for every AF stream. Stable RAM, absent asynchronous interference and
the sequential callable target profile remain environmental assumptions. -/
theorem semantics (compiler : ByteComparisonWindows.Compiler) :
    Grading.BufferTask.SemanticClaim .lexicographicBytes (ByteComparisonWindows.bytes compiler) :=
  VCGen.bufferCall_semantics_of_cutpoints spec _ _ (valid compiler) (generated compiler)

/-- Conservative retired model-instruction bound, independent of physical
cost or optimality. The static nine-instruction block bound is not input fuel. -/
theorem dynamic_bound (compiler : ByteComparisonWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteComparisonWindows.bytes compiler) input initial)
    (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      BufferCall.Post spec input initial result.state ∧
      result.instructions ≤ 9 * ((view input.value).left.length + 2) := by
  have binding : CFG.At (ByteComparisonWindows.bytes compiler) (graph compiler) initial.rip
      (valid compiler).entry initial := by
    refine ⟨pre.code, ?_⟩
    simp [(valid compiler).entry_offset]
  obtain ⟨result, execution, post, bound⟩ := (annotations compiler input initial pre).execution
    (valid compiler) (valid compiler).entry_cutpoint binding (entry_invariant compiler input initial pre) choices
  refine ⟨result, execution, post, ?_⟩
  have depth : (graph compiler).maxDepth = 8 := by cases compiler <;> rfl
  have rank : (annotations compiler input initial pre).rank (valid compiler).entry initial =
      (view input.value).left.length + 1 := by cases compiler <;> rfl
  simpa only [depth, rank, Nat.add_assoc] using bound

end EDSL.Corpus.V1.ByteComparisonBodies
