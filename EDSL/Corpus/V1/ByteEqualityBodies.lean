/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.ByteEquality
import EDSL.X86.VCGen.Tactics
import EDSL.Corpus.V1.ByteEqualityWindows

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.ByteEqualityBodies
open X86 X86.Sequential X86.VCGen.ByteEquality Grading.ByteEquality

/-- Exact complete partitions; entry and one shared loop boundary are the
only cutpoints. Static depth bounds one generated block, never the input. -/
abbrev gccGraph : CFG.Graph := ⟨[
  ⟨0,.endbr64IbtDisabled,true,8⟩,⟨4,.test64 .rdx .rdx,false,7⟩,
  ⟨7,.je 0x1f,false,6⟩,⟨9,.xorSelf32 .rax,false,5⟩,⟨11,.jmp 0x0c,false,0⟩,
  ⟨13,.nop .three,false,5⟩,⟨16,.addImm64 .rax 1,false,4⟩,
  ⟨20,.cmp64 .rdx .rax,false,3⟩,⟨23,.je 0x0f,false,2⟩,
  ⟨25,.movzxMem8 .rcx (.indexed .rsi .rax 0) false,true,8⟩,
  ⟨29,.cmpMemReg8 (.indexed .rdi .rax 0) .rcx,false,7⟩,
  ⟨32,.je 0xee,false,6⟩,⟨34,.xorSelf32 .rax,false,1⟩,
  ⟨36,.legacy .ret,false,0⟩,⟨37,.nop .three,false,2⟩,
  ⟨40,.legacy (.mov32 .rax 1),false,1⟩,⟨45,.legacy .ret,false,0⟩],8⟩

abbrev clangProfile : CFG.Profile := ⟨128,32,by decide⟩
abbrev clangGraph : CFG.Graph := ⟨[
  ⟨0,.test64 .rdx .rdx,true,9⟩,⟨3,.je 0x39,false,8⟩,
  ⟨5,.movzxMem8 .rax (.base .rdi) false,false,7⟩,
  ⟨8,.cmpRegMem8 .rax (.base .rsi) false,false,6⟩,
  ⟨10,.legacy (.jnz 0x35),false,5⟩,⟨12,.legacy (.mov32 .rcx 1),false,4⟩,
  ⟨17,.nop .fifteen,false,0⟩,⟨32,.movReg64 .rax .rcx,true,9⟩,
  ⟨35,.cmp64 .rdx .rcx,false,8⟩,⟨38,.je 0x0f,false,7⟩,
  ⟨40,.movzxMem8 .r8 (.indexed .rdi .rax 0) true,false,6⟩,
  ⟨45,.lea64 .rcx (.baseDisp8 .rax 1),false,5⟩,
  ⟨49,.cmpRegMem8 .r8 (.indexed .rsi .rax 0) true,false,4⟩,
  ⟨53,.je 0xe9,false,3⟩,⟨55,.cmp64 .rax .rdx,false,2⟩,
  ⟨58,.setcc .aboveEqual .rax false,false,1⟩,⟨61,.legacy .ret,false,0⟩,
  ⟨62,.movImm8 .rax 1 false,false,1⟩,⟨64,.legacy .ret,false,0⟩,
  ⟨65,.xorSelf32 .rax,false,1⟩,⟨67,.legacy .ret,false,0⟩],9⟩

theorem gcc_valid : CFG.Valid (ByteEqualityWindows.bytes .defaultGCC) gccGraph :=
  CFG.check_sound (by decide +kernel)
theorem clang_valid : CFG.Valid (ByteEqualityWindows.bytes .defaultClang) clangGraph clangProfile :=
  CFG.checkWith_sound (by decide +kernel)

abbrev gccEntry : gccGraph.Index := ⟨0,by decide⟩
abbrev gccLoop : gccGraph.Index := ⟨9,by decide⟩
abbrev clangEntry : clangGraph.Index := ⟨0,by decide⟩
abbrev clangLoop : clangGraph.Index := ⟨7,by decide⟩

def gccInv (input : BufferCall.Invocation spec) (initial : State)
    (node : gccGraph.Index) (state : State) : Prop :=
  CommonFrame initial state ∧ if node.val = 0 then True else
    EqualPrefix (view input.value) (state.registers .rax).toNat ∧
    (state.registers .rax).toNat < (view input.value).left.length

def clangInv (input : BufferCall.Invocation spec) (initial : State)
    (node : clangGraph.Index) (state : State) : Prop :=
  CommonFrame initial state ∧ if node.val = 0 then True else
    EqualPrefix (view input.value) (state.registers .rcx).toNat ∧
    (state.registers .rcx).toNat ≤ (view input.value).left.length

def gccRank (input : BufferCall.Invocation spec) (node : gccGraph.Index) (state : State) : Nat :=
  if node.val = 0 then (view input.value).left.length + 1
  else (view input.value).left.length - (state.registers .rax).toNat

def clangRank (input : BufferCall.Invocation spec) (node : clangGraph.Index) (state : State) : Nat :=
  if node.val = 0 then (view input.value).left.length + 1
  else (view input.value).left.length - (state.registers .rcx).toNat
def gccAnnotations (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteEqualityWindows.bytes .defaultGCC) input initial) :
    VCGen.Cutpoints.Annotations (ByteEqualityWindows.bytes .defaultGCC) gccGraph initial.rip
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
    have canonicalEqual : canonical (initial.rip + 40#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using
        gcc_valid.canonical_node binding.1 (⟨15, by decide⟩ : gccGraph.Index)
    rcases cuts with same | same
    · subst cut
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node, gccGraph, gccEntry] using binding.2
      by_cases empty : (view input.value).left.length = 0
      · have correct : spec.result input.value 1 :=
          finish_bound pre (Grading.FirstMatch.Prefix.start _ _) empty.symm rfl
        change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (gccInv input initial) (gccRank input) (gccRank input gccEntry state) 9 gccEntry state
        vcgen_block gccGraph gccEntry simp [executeMov32, -BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rsp, rdx, pre.stack, pre.returnCanonical,
          stackAllowed, empty, logicalFlags64_zero, canonicalEqual]
        byte_equality_return frame correct
      · have countNonzero : BitVec.ofNat 64 (view input.value).left.length ≠ 0#64 := by
          intro zero
          exact empty (by simpa only [count_nat pre, BitVec.toNat_zero] using congrArg BitVec.toNat zero)
        change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (gccInv input initial) (gccRank input) (gccRank input gccEntry state) 9 gccEntry state
        vcgen_block gccGraph gccEntry simp [-BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rdx, countNonzero, logicalFlags64_zero, canonicalLoop]
        dsimp only [gccInv, gccRank]
        refine ⟨⟨?_, Grading.FirstMatch.Prefix.start _ _, ?_⟩, by simp⟩
        · byte_equality_frame frame
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
          have correct : spec.result input.value 1 := finish_bound pre advanced last rfl
          change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (gccInv input initial) (gccRank input) (gccRank input gccLoop state) 9 gccLoop state
          vcgen_block gccGraph gccLoop simp [executeMov32, -BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rsp, rdi, rsi, rdx, loadedA, loadedB,
            allowedA, allowedB, pre.stack, pre.returnCanonical, stackAllowed, equalBytes,
            cmpFlags8_zero, cmpFlags64_zero, countEqual, canonicalInc, canonicalEqual]
          byte_equality_return frame correct
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
          · byte_equality_frame frame
          · change (state.registers .rax + 1).toNat < (view input.value).left.length
            omega
          · exact next_rank (count_small pre) cursor.2
      · have correct := finish_hit (input := input) leftAt rightAt equalBytes (actual := 0) rfl
        change VCGen.Cutpoints.wp gccGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (gccInv input initial) (gccRank input) (gccRank input gccLoop state) 9 gccLoop state
        vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, BitVec.add_assoc, pc, memory, rsp, rdi, rsi, loadedA, loadedB,
          allowedA, allowedB, pre.stack, pre.returnCanonical, stackAllowed, equalBytes, cmpFlags8_zero]
        byte_equality_return frame correct


/-- Clang's loop cutpoint follows an equal prefix. RCX names the next unread
pair (possibly the complete extent); RAX is overwritten by the first loop
instruction. The initial pair and empty B001 path belong to the entry block. -/
def clangAnnotations (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteEqualityWindows.bytes .defaultClang) input initial) :
    VCGen.Cutpoints.Annotations (ByteEqualityWindows.bytes .defaultClang) clangGraph initial.rip
      (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read) where
  Inv := clangInv input initial
  rank := clangRank input
  blocks cut state isCut binding admitted := by
    have cuts : cut = clangEntry ∨ cut = clangLoop := by
      have allCuts : ∀ node : clangGraph.Index,
          clangGraph.cutpoint node = true → node = clangEntry ∨ node = clangLoop := by decide
      exact allCuts cut isCut
    obtain ⟨frame,cursor⟩ := admitted
    have memory := frame.memory
    have rsp := frame.rsp
    have rdi := frame.rdi.trans (left_argument pre)
    have rsi := frame.rsi.trans (right_argument pre)
    have rdx := frame.rdx.trans (count_argument pre)
    have stackAllowed : BufferCall.RawRead spec input initial
        ⟨.stack,initial.registers .rsp,8⟩ := Or.inl ⟨rfl,rfl,rfl⟩
    have canonicalLoop : canonical (initial.rip + 32#64) = true := by
      simpa [CFG.Graph.node,clangGraph] using clang_valid.canonical_node binding.1 clangLoop
    have canonicalEmpty : canonical (initial.rip + 62#64) = true := by
      simpa [CFG.Graph.node,clangGraph] using
        clang_valid.canonical_node binding.1 (⟨17,by decide⟩ : clangGraph.Index)
    have canonicalMiss : canonical (initial.rip + 65#64) = true := by
      simpa [CFG.Graph.node,clangGraph] using
        clang_valid.canonical_node binding.1 (⟨19,by decide⟩ : clangGraph.Index)
    have canonicalFinish : canonical (initial.rip + 55#64) = true := by
      simpa [CFG.Graph.node,clangGraph] using
        clang_valid.canonical_node binding.1 (⟨14,by decide⟩ : clangGraph.Index)
    rcases cuts with same | same
    · subst cut
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node,clangGraph,clangEntry] using binding.2
      by_cases empty : (view input.value).left.length = 0
      · have correct : spec.result input.value (replaceLow8 (state.registers .rax) 1) :=
          finish_bound pre (Grading.FirstMatch.Prefix.start _ _) empty.symm (return_replace _ _)
        change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (clangInv input initial) (clangRank input) (clangRank input clangEntry state) 10 clangEntry state
        vcgen_block clangGraph clangEntry simp [-BitVec.getLsbD_eq_getElem,
          BitVec.add_assoc,pc,memory,rsp,rdx,pre.stack,pre.returnCanonical,stackAllowed,
          empty,logicalFlags64_zero,canonicalEmpty]
        byte_equality_return frame correct
      · have positive : 0 < (view input.value).left.length := by omega
        have countNonzero : BitVec.ofNat 64 (view input.value).left.length ≠ 0#64 := by
          intro zero
          exact empty (by simpa only [count_nat pre,BitVec.toNat_zero] using congrArg BitVec.toNat zero)
        obtain ⟨a,b,leftAt,rightAt,loadedA,loadedB,allowedA,allowedB⟩ :=
          read_pair pre frame (index := 0) positive
        simp only [BitVec.add_zero,memory] at loadedA loadedB allowedA allowedB
        by_cases equalBytes : a = b
        · have advanced : EqualPrefix (view input.value) 1 := by
            simpa using advance (index := 0#64) pre positive
              (Grading.FirstMatch.Prefix.start _ _) leftAt rightAt equalBytes
          change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (clangInv input initial) (clangRank input) (clangRank input clangEntry state) 10 clangEntry state
          vcgen_block clangGraph clangEntry simp [executeMov32,-BitVec.getLsbD_eq_getElem,
            BitVec.add_assoc,pc,memory,rdi,rsi,rdx,countNonzero,logicalFlags64_zero,
            loadedA,loadedB,allowedA,allowedB,equalBytes,cmpFlags8_zero]
          dsimp only [clangInv,clangRank]
          refine ⟨⟨?_,advanced,?_⟩,?_⟩
          · byte_equality_frame frame
          · change 1 ≤ (view input.value).left.length
            omega
          · change (view input.value).left.length - 1 < (view input.value).left.length + 1
            omega
        · have correct := finish_hit (input := input) leftAt rightAt equalBytes (actual := 0) rfl
          change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (clangInv input initial) (clangRank input) (clangRank input clangEntry state) 10 clangEntry state
          vcgen_block clangGraph clangEntry simp [-BitVec.getLsbD_eq_getElem,
            BitVec.add_assoc,pc,memory,rsp,rdi,rsi,rdx,countNonzero,logicalFlags64_zero,
            loadedA,loadedB,allowedA,allowedB,pre.stack,pre.returnCanonical,stackAllowed,
            equalBytes,cmpFlags8_zero,canonicalMiss]
          byte_equality_return frame correct
    · subst cut
      change EqualPrefix (view input.value) (state.registers .rcx).toNat ∧
        (state.registers .rcx).toNat ≤ (view input.value).left.length at cursor
      have pc : state.rip = initial.rip + 32#64 := by
        simpa [CFG.Graph.node,clangGraph,clangLoop] using binding.2
      by_cases last : (state.registers .rcx).toNat = (view input.value).left.length
      · have countEqual : BitVec.ofNat 64 (view input.value).left.length = state.registers .rcx :=
          BitVec.eq_of_toNat_eq ((count_nat pre).trans last.symm)
        have correct : spec.result input.value (replaceLow8 (state.registers .rcx) 1) :=
          finish_bound pre cursor.1 last (return_replace _ _)
        change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
          (fun _ read => BufferCall.RawRead spec input initial read)
          (clangInv input initial) (clangRank input) (clangRank input clangLoop state) 10 clangLoop state
        vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem,
          BitVec.add_assoc,pc,memory,rsp,rdx,countEqual,cmpFlags64_zero,Condition.cmp_aboveEqual,
          pre.stack,pre.returnCanonical,stackAllowed,canonicalFinish]
        byte_equality_return frame correct
      · have inside : (state.registers .rcx).toNat < (view input.value).left.length := by omega
        have countDifferent : BitVec.ofNat 64 (view input.value).left.length ≠ state.registers .rcx := by
          intro equal
          exact last ((congrArg BitVec.toNat equal).symm.trans (count_nat pre))
        have countZf : ∀ flags : Word,
            (cmpFlags64 flags (BitVec.ofNat 64 (view input.value).left.length)
              (state.registers .rcx)).getLsbD 6 = false := by
          intro flags
          rw [cmpFlags64_zero]
          exact beq_eq_false_iff_ne.mpr countDifferent
        have countAeFalse : ∀ flags : Word,
            Condition.holds .aboveEqual (cmpFlags64 flags (state.registers .rcx)
              (BitVec.ofNat 64 (view input.value).left.length)) = false := by
          intro flags
          rw [Condition.cmp_aboveEqual,count_nat pre]
          exact decide_eq_false_iff_not.mpr (by omega)
        obtain ⟨a,b,leftAt,rightAt,loadedA,loadedB,allowedA,allowedB⟩ := read_pair pre frame inside
        simp only [memory,BitVec.ofNat_toNat,BitVec.setWidth_eq] at loadedA loadedB allowedA allowedB
        by_cases equalBytes : a = b
        · have advanced := advance pre inside cursor.1 leftAt rightAt equalBytes
          have nextNat := next_nat (count_small pre) inside
          change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (clangInv input initial) (clangRank input) (clangRank input clangLoop state) 10 clangLoop state
          vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem,
            BitVec.add_assoc,pc,memory,rdi,rsi,rdx,countZf,loadedA,loadedB,
            allowedA,allowedB,equalBytes,cmpFlags8_zero,canonicalLoop]
          dsimp only [clangInv,clangRank]
          refine ⟨⟨?_,advanced,?_⟩,?_⟩
          · byte_equality_frame frame
          · change (state.registers .rcx + 1).toNat ≤ (view input.value).left.length
            rw [nextNat]; omega
          · exact next_rank (count_small pre) inside
        · have correct : spec.result input.value (replaceLow8 (state.registers .rcx) 0) :=
            finish_hit leftAt rightAt equalBytes (return_replace _ _)
          change VCGen.Cutpoints.wp clangGraph initial.rip (BufferCall.Post spec input initial)
            (fun _ read => BufferCall.RawRead spec input initial read)
            (clangInv input initial) (clangRank input) (clangRank input clangLoop state) 10 clangLoop state
          vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem,
            BitVec.add_assoc,pc,memory,rsp,rdi,rsi,rdx,countZf,loadedA,loadedB,allowedA,allowedB,
            equalBytes,cmpFlags8_zero,countAeFalse,pre.stack,
            pre.returnCanonical,stackAllowed]
          byte_equality_return frame correct

def profile : ByteEqualityWindows.Compiler → CFG.Profile
  | .defaultGCC => CFG.defaultProfile
  | .defaultClang => clangProfile

def graph : ByteEqualityWindows.Compiler → CFG.Graph
  | .defaultGCC => gccGraph
  | .defaultClang => clangGraph

theorem valid (compiler : ByteEqualityWindows.Compiler) :
    CFG.Valid (ByteEqualityWindows.bytes compiler) (graph compiler) (profile compiler) := by
  cases compiler
  · exact gcc_valid
  · exact clang_valid

def annotations (compiler : ByteEqualityWindows.Compiler) (input : BufferCall.Invocation spec)
    (initial : State) (pre : BufferCall.Pre spec (ByteEqualityWindows.bytes compiler) input initial) :
    VCGen.Cutpoints.Annotations (ByteEqualityWindows.bytes compiler) (graph compiler) initial.rip
      (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read) := by
  cases compiler
  · exact gccAnnotations input initial pre
  · exact clangAnnotations input initial pre

theorem entry_invariant (compiler : ByteEqualityWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteEqualityWindows.bytes compiler) input initial) :
    (annotations compiler input initial pre).Inv (valid compiler).entry initial := by
  cases compiler <;> exact ⟨VCGen.ByteComparison.CommonFrame.refl initial,True.intro⟩

theorem generated (compiler : ByteEqualityWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteEqualityWindows.bytes compiler) input initial) :
    ∃ annotation : VCGen.Cutpoints.Annotations (ByteEqualityWindows.bytes compiler) (graph compiler)
      initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read),
      annotation.Inv (valid compiler).entry initial :=
  ⟨annotations compiler input initial pre,entry_invariant compiler input initial pre⟩

theorem raw (compiler : ByteEqualityWindows.Compiler) :
    ∀ input initial, BufferCall.Pre spec (ByteEqualityWindows.bytes compiler) input initial →
      Sequential.AllExecutions initial (fun result => BufferCall.Post spec input initial result.state) ∧
      BufferCall.RawPolicy spec input initial :=
  VCGen.bufferCall_raw_of_cutpoints spec _ _ (valid compiler) (generated compiler)

/-- All actual continuing prefixes of every admitted empty call need only
the original STACK8 authority, for arbitrary empty bases and all choices. -/
theorem empty_raw_policy (compiler : ByteEqualityWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteEqualityWindows.bytes compiler) input initial)
    (emptyLeft : (view input.value).left = []) (emptyRight : (view input.value).right = []) :
    Grading.ReadOnlyPolicy initial (fun before => before.memory = initial.memory)
      (fun _ read => PureCall.RawRead initial read) := by
  apply (raw compiler input initial pre).2.mono (fun _ frame => frame)
  intro _ read allowed
  rcases allowed with stack | data
  · exact stack
  · have noData : ¬BufferCall.DataRead
        [leftBuffer (view input.value),rightBuffer (view input.value)] read := by
      apply BufferCall.DataRead.no_empty
      intro buffer member
      have cases : buffer = leftBuffer (view input.value) ∨ buffer = rightBuffer (view input.value) := by
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using member
      rcases cases with rfl | rfl
      · exact emptyLeft
      · exact emptyRight
    exact False.elim (noData data)

/-- Universal fixed independent Boolean semantics of the exact frozen bodies,
including complete RAM/ABI/nonarithmetic frame and actual CURRENT original
authority at every prefix and return, for every choice stream. Stable ordinary
RAM, absent asynchronous interference and the represented callable target
profile (including exact long-NOP support) remain environmental assumptions. -/
theorem semantics (compiler : ByteEqualityWindows.Compiler) :
    Grading.ReadOnlySemanticClaim (BufferCall.readOnlyTask spec) (ByteEqualityWindows.bytes compiler) :=
  VCGen.bufferCall_semantics_of_cutpoints spec _ _ (valid compiler) (generated compiler)

/-- Conservative model-instruction bound. Static block depth is proof data,
not an input-length cap, dynamic interpreter fuel or physical cost claim. -/
theorem dynamic_bound (compiler : ByteEqualityWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteEqualityWindows.bytes compiler) input initial)
    (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      BufferCall.Post spec input initial result.state ∧
      result.instructions ≤ 10 * ((view input.value).left.length + 2) := by
  have binding : CFG.At (ByteEqualityWindows.bytes compiler) (graph compiler) initial.rip
      (valid compiler).entry initial := by
    refine ⟨pre.code,?_⟩
    simp [(valid compiler).entry_offset]
  obtain ⟨result,execution,post,bound⟩ := (annotations compiler input initial pre).execution
    (valid compiler) (valid compiler).entry_cutpoint binding
      (entry_invariant compiler input initial pre) choices
  refine ⟨result,execution,post,?_⟩
  have depth : (graph compiler).maxDepth + 1 ≤ 10 := by cases compiler <;> decide
  have rank : (annotations compiler input initial pre).rank (valid compiler).entry initial =
      (view input.value).left.length + 1 := by cases compiler <;> rfl
  rw [rank] at bound
  exact Nat.le_trans bound (Nat.mul_le_mul_right _ depth)

end EDSL.Corpus.V1.ByteEqualityBodies
