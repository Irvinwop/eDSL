/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.IndexSearchWindows
import EDSL.X86.VCGen.Tactics
import EDSL.X86.VCGen.IndexSearch

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.IndexSearchBodies
open X86 X86.Sequential
open X86.VCGen.IndexSearch
open Grading.IndexSearch

/-- Only the opcode and SIB scale vary with element width. -/
def operation : Width → IndexSearchWindows.Operation | .byte => .byte | .u32 => .u32

def bodyBytes (compiler : IndexSearchWindows.Compiler) (width : Width) : List Byte :=
  IndexSearchWindows.bytes compiler (operation width)

/-- Complete partitions include every padding byte and both return sites.
CFG.check, rather than these proposed layouts, authenticates decoding/edges. -/
abbrev gccGraph (width : Width) : CFG.Graph := ⟨[
  ⟨0, .endbr64IbtDisabled, true, 4⟩,
  ⟨4, .test64 .rsi .rsi, false, 3⟩,
  ⟨7, .je 0x17, false, 2⟩,
  ⟨9, .xorSelf32 .rax, false, 1⟩,
  ⟨11, .jmp 0x0c, false, 0⟩,
  ⟨13, .nop .three, false, 5⟩,
  ⟨16, .addImm64 .rax 1, false, 4⟩,
  ⟨20, .cmp64 .rsi .rax, false, 3⟩,
  ⟨23, .je 7, false, 2⟩,
  ⟨25, comparison width .rax, true, 6⟩,
  ⟨28, .legacy (.jnz 0xf2), false, 5⟩,
  ⟨30, .legacy .ret, false, 0⟩,
  ⟨31, .nop .one, false, 2⟩,
  ⟨32, .movSignImm32 .rax 0xffffffff, false, 1⟩,
  ⟨39, .legacy .ret, false, 0⟩], 6⟩

abbrev clangGraph (width : Width) : CFG.Graph := ⟨[
  ⟨0, .movSignImm32 .rax 0xffffffff, true, 4⟩,
  ⟨7, .test64 .rsi .rsi, false, 3⟩,
  ⟨10, .je 0x11, false, 2⟩,
  ⟨12, .xorSelf32 .rcx, false, 1⟩,
  ⟨14, .nop .two, false, 0⟩,
  ⟨16, comparison width .rcx, true, 5⟩,
  ⟨19, .je 9, false, 4⟩,
  ⟨21, .inc64 .rcx, false, 3⟩,
  ⟨24, .cmp64 .rsi .rcx, false, 2⟩,
  ⟨27, .legacy (.jnz 0xf3), false, 1⟩,
  ⟨29, .legacy .ret, false, 0⟩,
  ⟨30, .movReg64 .rax .rcx, false, 1⟩,
  ⟨33, .legacy .ret, false, 0⟩], 5⟩

theorem gcc_checked (width : Width) : CFG.check (bodyBytes .defaultGCC width) (gccGraph width) = true := by
  cases width <;> decide +kernel

theorem clang_checked (width : Width) : CFG.check (bodyBytes .defaultClang width) (clangGraph width) = true := by
  cases width <;> decide +kernel

theorem gcc_valid (width : Width) : CFG.Valid (bodyBytes .defaultGCC width) (gccGraph width) :=
  CFG.check_sound (gcc_checked width)

theorem clang_valid (width : Width) : CFG.Valid (bodyBytes .defaultClang width) (clangGraph width) :=
  CFG.check_sound (clang_checked width)

abbrev gccEntry (width : Width) : (gccGraph width).Index := ⟨0, by change 0 < 15; decide⟩
abbrev gccLoop (width : Width) : (gccGraph width).Index := ⟨9, by change 9 < 15; decide⟩
abbrev clangEntry (width : Width) : (clangGraph width).Index := ⟨0, by change 0 < 13; decide⟩
abbrev clangLoop (width : Width) : (clangGraph width).Index := ⟨5, by change 5 < 13; decide⟩

/-- The independent prefix excludes every earlier key. Only actual current
cursor/register observations occur in these sparse cutpoint assertions. -/
def gccInv (width : Width) (input : BufferCall.Invocation (spec width)) (initial : State)
    (node : (gccGraph width).Index) (state : State) : Prop :=
  CommonFrame initial state ∧ if node.val = 0 then True else
    Grading.FirstMatch.Prefix (values width input.value) (equals (key width input.value))
      (state.registers .rax).toNat ∧
    (state.registers .rax).toNat < (values width input.value).length

def clangInv (width : Width) (input : BufferCall.Invocation (spec width)) (initial : State)
    (node : (clangGraph width).Index) (state : State) : Prop :=
  CommonFrame initial state ∧ if node.val = 0 then True else
    Grading.FirstMatch.Prefix (values width input.value) (equals (key width input.value))
      (state.registers .rcx).toNat ∧
    (state.registers .rcx).toNat < (values width input.value).length ∧
    state.registers .rax = sizeMax

def gccRank (width : Width) (input : BufferCall.Invocation (spec width))
    (node : (gccGraph width).Index) (state : State) : Nat :=
  if node.val = 0 then (values width input.value).length + 1
  else (values width input.value).length - (state.registers .rax).toNat

def clangRank (width : Width) (input : BufferCall.Invocation (spec width))
    (node : (clangGraph width).Index) (state : State) : Nat :=
  if node.val = 0 then (values width input.value).length + 1
  else (values width input.value).length - (state.registers .rcx).toNat

local macro "search_frame" frame:ident : tactic => `(tactic| (
  simp only [commonFrame_iff, State.writeRegister, logicalFlags32_preserves,
    logicalFlags64_preserves, comparisonFlags_preserves, cmpFlags64_preserves,
    addFlags64_preserves, incFlags64_preserves, ($frame).memory, ($frame).flags,
    true_and, and_true]
  intro register notRax notRcx
  simpa only [notRax, notRcx, ite_false] using
    ($frame).registers register notRax notRcx))

local macro "search_return" frame:ident correct:ident : tactic => `(tactic| (
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_⟩
  · simpa [BufferCall.Spec.scalarSpec, sizeMax] using $correct
  · intro register saved
    have different := saved_different register saved
    simpa only [State.writeRegister, different.1, different.2.1, different.2.2, ite_false] using
      ($frame).registers register different.2.1 different.2.2
  · simpa only [logicalFlags32_preserves, logicalFlags64_preserves,
      comparisonFlags_preserves, cmpFlags64_preserves, addFlags64_preserves,
      incFlags64_preserves] using ($frame).flags))

local macro "search_comparison" effect:ident allowed:ident pc:ident layout:ident index:num : tactic => `(tactic| (
  refine wp_next $effect ?_
    ⟨$index:num, by first | (change $index:num < 15; decide) | (change $index:num < 13; decide)⟩ ?_ ?_
  · simpa only [List.mem_singleton, forall_eq] using $allowed
  · unfold CFG.Graph.node $layout
    simp [($pc), BitVec.add_assoc]
  unfold CFG.Graph.cutpoint CFG.Graph.node $layout
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Bool.false_eq_true, ↓reduceIte]))

/-- One width-parametric generated proof for the complete GCC layout. -/
def gccAnnotations (width : Width) (input : BufferCall.Invocation (spec width)) (initial : State)
    (pre : BufferCall.Pre (spec width) (bodyBytes .defaultGCC width) input initial) :
    VCGen.Cutpoints.Annotations (bodyBytes .defaultGCC width) (gccGraph width) initial.rip
      (BufferCall.Post (spec width) input initial)
      (fun _ read => BufferCall.RawRead (spec width) input initial read) where
  Inv := gccInv width input initial
  rank := gccRank width input
  blocks cut state isCut binding admitted := by
    have cuts : cut = gccEntry width ∨ cut = gccLoop width := by
      have allCuts : ∀ node : (gccGraph width).Index,
          (gccGraph width).cutpoint node = true → node = gccEntry width ∨ node = gccLoop width := by cases width <;> decide
      exact allCuts cut isCut
    obtain ⟨frame, cursor⟩ := admitted
    have memory := frame.memory
    have rsp := frame.rsp
    have rsi := frame.rsi.trans (count_argument pre)
    have stackAllowed : BufferCall.RawRead (spec width) input initial
        ⟨.stack, initial.registers .rsp, 8⟩ := Or.inl ⟨rfl, rfl, rfl⟩
    have canonicalLoop : canonical (initial.rip + 25#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using (gcc_valid width).canonical_node binding.1 (gccLoop width)
    have canonicalAdd : canonical (initial.rip + 16#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using
        (gcc_valid width).canonical_node binding.1 (⟨6, by change 6 < 15; decide⟩ : (gccGraph width).Index)
    have canonicalMax : canonical (initial.rip + 32#64) = true := by
      simpa [CFG.Graph.node, gccGraph] using
        (gcc_valid width).canonical_node binding.1 (⟨13, by change 13 < 15; decide⟩ : (gccGraph width).Index)
    rcases cuts with same | same
    · subst cut
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node, gccGraph, gccEntry] using binding.2
      by_cases empty : (values width input.value).length = 0
      · have correct := finish_bound (input := input) (Grading.FirstMatch.Prefix.start _ _) empty.symm
        change VCGen.Cutpoints.wp (gccGraph width) initial.rip (BufferCall.Post (spec width) input initial)
          (fun _ read => BufferCall.RawRead (spec width) input initial read)
          (gccInv width input initial) (gccRank width input) (gccRank width input (gccEntry width) state)
          5 (gccEntry width) state
        vcgen_block gccGraph gccEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp, rsi, pre.stack, pre.returnCanonical,
            stackAllowed, empty, logicalFlags64_zero, canonicalMax, BitVec.add_assoc]
        search_return frame correct
      · have countNonzero : BitVec.ofNat 64 (values width input.value).length ≠ 0#64 := by
          intro zero
          have natural := congrArg BitVec.toNat zero
          rw [count_nat pre] at natural
          exact empty natural
        change VCGen.Cutpoints.wp (gccGraph width) initial.rip (BufferCall.Post (spec width) input initial)
          (fun _ read => BufferCall.RawRead (spec width) input initial read)
          (gccInv width input initial) (gccRank width input) (gccRank width input (gccEntry width) state)
          5 (gccEntry width) state
        vcgen_block gccGraph gccEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsi, countNonzero,
            logicalFlags64_zero, canonicalLoop, BitVec.add_assoc]
        dsimp only [gccInv, gccRank]
        refine ⟨⟨?_, Grading.FirstMatch.Prefix.start _ _, ?_⟩, by simp⟩
        · search_frame frame
        · change 0 < (values width input.value).length
          omega
    · subst cut
      change Grading.FirstMatch.Prefix (values width input.value) (equals (key width input.value))
          (state.registers .rax).toNat ∧
        (state.registers .rax).toNat < (values width input.value).length at cursor
      have pc : state.rip = initial.rip + 25#64 := by
        simpa [CFG.Graph.node, gccGraph, gccLoop] using binding.2
      obtain ⟨value, present, dataAllowed, effect⟩ := read_comparison pre frame .rax cursor.2
      have nextNat := next_nat (count_small pre) cursor.2
      have nextLe : (state.registers .rax + 1).toNat ≤ (values width input.value).length := by
        rw [nextNat]; omega
      by_cases hit : value = key width input.value
      · have correct := finish_hit cursor.1 (by simpa only [hit] using present)
        change VCGen.Cutpoints.wp (gccGraph width) initial.rip (BufferCall.Post (spec width) input initial)
          (fun _ read => BufferCall.RawRead (spec width) input initial read)
          (gccInv width input initial) (gccRank width input) (gccRank width input (gccLoop width) state)
          7 (gccLoop width) state
        search_comparison effect dataAllowed pc gccGraph 10
        vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp,
            pre.stack, pre.returnCanonical, stackAllowed, hit, comparisonFlags_zero, BitVec.add_assoc]
        search_return frame correct
      · have advanced := advance pre cursor.2 cursor.1 present hit
        have valueZf : ∀ flags : Word,
            (comparisonFlags width flags value (key width input.value)).getLsbD 6 = false := by
          intro flags
          rw [comparisonFlags_zero]
          exact beq_eq_false_iff_ne.mpr hit
        by_cases last : (state.registers .rax + 1).toNat = (values width input.value).length
        · have equal : BitVec.ofNat 64 (values width input.value).length = state.registers .rax + 1 :=
            BitVec.eq_of_toNat_eq ((count_nat pre).trans last.symm)
          have correct := finish_bound advanced last
          change VCGen.Cutpoints.wp (gccGraph width) initial.rip (BufferCall.Post (spec width) input initial)
            (fun _ read => BufferCall.RawRead (spec width) input initial read)
            (gccInv width input initial) (gccRank width input) (gccRank width input (gccLoop width) state)
            7 (gccLoop width) state
          search_comparison effect dataAllowed pc gccGraph 10
          vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp, rsi,
              pre.stack, pre.returnCanonical, stackAllowed, valueZf, cmpFlags64_zero, equal,
              canonicalAdd, canonicalMax, BitVec.add_assoc]
          search_return frame correct
        · have different : BitVec.ofNat 64 (values width input.value).length ≠ state.registers .rax + 1 := by
            intro equal
            exact last ((congrArg BitVec.toNat equal).symm.trans (count_nat pre))
          have countZf : ∀ flags : Word,
              (cmpFlags64 flags (BitVec.ofNat 64 (values width input.value).length)
                (state.registers .rax + 1#64)).getLsbD 6 = false := by
            intro flags
            rw [cmpFlags64_zero]
            exact beq_eq_false_iff_ne.mpr different
          change VCGen.Cutpoints.wp (gccGraph width) initial.rip (BufferCall.Post (spec width) input initial)
            (fun _ read => BufferCall.RawRead (spec width) input initial read)
            (gccInv width input initial) (gccRank width input) (gccRank width input (gccLoop width) state)
            7 (gccLoop width) state
          search_comparison effect dataAllowed pc gccGraph 10
          vcgen_block gccGraph gccLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsi, valueZf, countZf,
              canonicalAdd, BitVec.add_assoc]
          dsimp only [gccInv, gccRank]
          refine ⟨⟨?_, advanced, ?_⟩, ?_⟩
          · search_frame frame
          · change (state.registers .rax + 1).toNat < (values width input.value).length
            omega
          · exact next_rank (count_small pre) cursor.2

/-- One width-parametric generated proof for the complete Clang layout. -/
def clangAnnotations (width : Width) (input : BufferCall.Invocation (spec width)) (initial : State)
    (pre : BufferCall.Pre (spec width) (bodyBytes .defaultClang width) input initial) :
    VCGen.Cutpoints.Annotations (bodyBytes .defaultClang width) (clangGraph width) initial.rip
      (BufferCall.Post (spec width) input initial)
      (fun _ read => BufferCall.RawRead (spec width) input initial read) where
  Inv := clangInv width input initial
  rank := clangRank width input
  blocks cut state isCut binding admitted := by
    have cuts : cut = clangEntry width ∨ cut = clangLoop width := by
      have allCuts : ∀ node : (clangGraph width).Index,
          (clangGraph width).cutpoint node = true → node = clangEntry width ∨ node = clangLoop width := by cases width <;> decide
      exact allCuts cut isCut
    obtain ⟨frame, cursor⟩ := admitted
    have memory := frame.memory
    have rsp := frame.rsp
    have rsi := frame.rsi.trans (count_argument pre)
    have stackAllowed : BufferCall.RawRead (spec width) input initial
        ⟨.stack, initial.registers .rsp, 8⟩ := Or.inl ⟨rfl, rfl, rfl⟩
    have canonicalLoop : canonical (initial.rip + 16#64) = true := by
      simpa [CFG.Graph.node, clangGraph] using (clang_valid width).canonical_node binding.1 (clangLoop width)
    have canonicalRet : canonical (initial.rip + 29#64) = true := by
      simpa [CFG.Graph.node, clangGraph] using
        (clang_valid width).canonical_node binding.1 (⟨10, by change 10 < 13; decide⟩ : (clangGraph width).Index)
    have canonicalHit : canonical (initial.rip + 30#64) = true := by
      simpa [CFG.Graph.node, clangGraph] using
        (clang_valid width).canonical_node binding.1 (⟨11, by change 11 < 13; decide⟩ : (clangGraph width).Index)
    rcases cuts with same | same
    · subst cut
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node, clangGraph, clangEntry] using binding.2
      by_cases empty : (values width input.value).length = 0
      · have correct := finish_bound (input := input) (Grading.FirstMatch.Prefix.start _ _) empty.symm
        change VCGen.Cutpoints.wp (clangGraph width) initial.rip (BufferCall.Post (spec width) input initial)
          (fun _ read => BufferCall.RawRead (spec width) input initial read)
          (clangInv width input initial) (clangRank width input) (clangRank width input (clangEntry width) state)
          5 (clangEntry width) state
        vcgen_block clangGraph clangEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp, rsi, pre.stack, pre.returnCanonical,
            stackAllowed, empty, logicalFlags64_zero, canonicalRet, BitVec.add_assoc]
        search_return frame correct
      · have countNonzero : BitVec.ofNat 64 (values width input.value).length ≠ 0#64 := by
          intro zero
          have natural := congrArg BitVec.toNat zero
          rw [count_nat pre] at natural
          exact empty natural
        change VCGen.Cutpoints.wp (clangGraph width) initial.rip (BufferCall.Post (spec width) input initial)
          (fun _ read => BufferCall.RawRead (spec width) input initial read)
          (clangInv width input initial) (clangRank width input) (clangRank width input (clangEntry width) state)
          5 (clangEntry width) state
        vcgen_block clangGraph clangEntry simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsi, countNonzero,
            logicalFlags64_zero, BitVec.add_assoc]
        dsimp only [clangInv, clangRank]
        refine ⟨⟨?_, Grading.FirstMatch.Prefix.start _ _, ?_, rfl⟩, by simp⟩
        · search_frame frame
        · change 0 < (values width input.value).length
          omega
    · subst cut
      change Grading.FirstMatch.Prefix (values width input.value) (equals (key width input.value))
          (state.registers .rcx).toNat ∧
        (state.registers .rcx).toNat < (values width input.value).length ∧
        state.registers .rax = sizeMax at cursor
      have pc : state.rip = initial.rip + 16#64 := by
        simpa [CFG.Graph.node, clangGraph, clangLoop] using binding.2
      obtain ⟨value, present, dataAllowed, effect⟩ := read_comparison pre frame .rcx cursor.2.1
      have nextNat := next_nat (count_small pre) cursor.2.1
      have nextLe : (state.registers .rcx + 1).toNat ≤ (values width input.value).length := by
        rw [nextNat]; omega
      by_cases hit : value = key width input.value
      · have correct := finish_hit cursor.1 (by simpa only [hit] using present)
        change VCGen.Cutpoints.wp (clangGraph width) initial.rip (BufferCall.Post (spec width) input initial)
          (fun _ read => BufferCall.RawRead (spec width) input initial read)
          (clangInv width input initial) (clangRank width input) (clangRank width input (clangLoop width) state)
          6 (clangLoop width) state
        search_comparison effect dataAllowed pc clangGraph 6
        vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp,
            pre.stack, pre.returnCanonical, stackAllowed, hit, comparisonFlags_zero,
            canonicalHit, BitVec.add_assoc]
        search_return frame correct
      · have advanced := advance pre cursor.2.1 cursor.1 present hit
        have valueZf : ∀ flags : Word,
            (comparisonFlags width flags value (key width input.value)).getLsbD 6 = false := by
          intro flags
          rw [comparisonFlags_zero]
          exact beq_eq_false_iff_ne.mpr hit
        by_cases last : (state.registers .rcx + 1).toNat = (values width input.value).length
        · have equal : BitVec.ofNat 64 (values width input.value).length = state.registers .rcx + 1 :=
            BitVec.eq_of_toNat_eq ((count_nat pre).trans last.symm)
          have correct : (spec width).result input.value (state.registers .rax) := by
            rw [cursor.2.2]
            exact finish_bound advanced last
          change VCGen.Cutpoints.wp (clangGraph width) initial.rip (BufferCall.Post (spec width) input initial)
            (fun _ read => BufferCall.RawRead (spec width) input initial read)
            (clangInv width input initial) (clangRank width input) (clangRank width input (clangLoop width) state)
            6 (clangLoop width) state
          search_comparison effect dataAllowed pc clangGraph 6
          vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsp, rsi,
              pre.stack, pre.returnCanonical, stackAllowed, valueZf, cmpFlags64_zero, equal,
              BitVec.add_assoc]
          search_return frame correct
        · have different : BitVec.ofNat 64 (values width input.value).length ≠ state.registers .rcx + 1 := by
            intro equal
            exact last ((congrArg BitVec.toNat equal).symm.trans (count_nat pre))
          have countZf : ∀ flags : Word,
              (cmpFlags64 flags (BitVec.ofNat 64 (values width input.value).length)
                (state.registers .rcx + 1#64)).getLsbD 6 = false := by
            intro flags
            rw [cmpFlags64_zero]
            exact beq_eq_false_iff_ne.mpr different
          change VCGen.Cutpoints.wp (clangGraph width) initial.rip (BufferCall.Post (spec width) input initial)
            (fun _ read => BufferCall.RawRead (spec width) input initial read)
            (clangInv width input initial) (clangRank width input) (clangRank width input (clangLoop width) state)
            6 (clangLoop width) state
          search_comparison effect dataAllowed pc clangGraph 6
          vcgen_block clangGraph clangLoop simp [-BitVec.getLsbD_eq_getElem, pc, memory, rsi, valueZf, countZf,
              canonicalLoop, BitVec.add_assoc]
          dsimp only [clangInv, clangRank]
          refine ⟨⟨?_, advanced, ?_, cursor.2.2⟩, ?_⟩
          · search_frame frame
          · change (state.registers .rcx + 1).toNat < (values width input.value).length
            omega
          · exact next_rank (count_small pre) cursor.2.1


/-- The public operation names select the trusted fixed task IDs. -/
def taskID : IndexSearchWindows.Operation → Grading.BufferTask.TaskID
  | .byte => .memchrIndex | .u32 => .linearSearchU32

def width : IndexSearchWindows.Operation → Width | .byte => .byte | .u32 => .u32

def graph (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation) : CFG.Graph :=
  match compiler with
  | .defaultGCC => gccGraph (width op)
  | .defaultClang => clangGraph (width op)

theorem valid (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation) :
    CFG.Valid (IndexSearchWindows.bytes compiler op) (graph compiler op) := by
  cases compiler <;> cases op
  · exact gcc_valid .byte
  · exact gcc_valid .u32
  · exact clang_valid .byte
  · exact clang_valid .u32

/-- Select the shared generated proof; this introduces no execution model or
per-element-width VCs. -/
def annotations (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation)
    (input : BufferCall.Invocation (spec (width op))) (initial : State)
    (pre : BufferCall.Pre (spec (width op)) (IndexSearchWindows.bytes compiler op) input initial) :
    VCGen.Cutpoints.Annotations (IndexSearchWindows.bytes compiler op) (graph compiler op) initial.rip
      (BufferCall.Post (spec (width op)) input initial)
      (fun _ read => BufferCall.RawRead (spec (width op)) input initial read) := by
  cases compiler <;> cases op
  · exact gccAnnotations .byte input initial pre
  · exact gccAnnotations .u32 input initial pre
  · exact clangAnnotations .byte input initial pre
  · exact clangAnnotations .u32 input initial pre

theorem entry_invariant (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation)
    (input : BufferCall.Invocation (spec (width op))) (initial : State)
    (pre : BufferCall.Pre (spec (width op)) (IndexSearchWindows.bytes compiler op) input initial) :
    (annotations compiler op input initial pre).Inv (valid compiler op).entry initial := by
  cases compiler <;> cases op <;> exact ⟨CommonFrame.refl initial, True.intro⟩

theorem generated (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation)
    (input : BufferCall.Invocation (spec (width op))) (initial : State)
    (pre : BufferCall.Pre (spec (width op)) (IndexSearchWindows.bytes compiler op) input initial) :
    ∃ evidence : VCGen.Cutpoints.Annotations (IndexSearchWindows.bytes compiler op)
        (graph compiler op) initial.rip (BufferCall.Post (spec (width op)) input initial)
        (fun _ read => BufferCall.RawRead (spec (width op)) input initial read),
      evidence.Inv (valid compiler op).entry initial :=
  ⟨annotations compiler op input initial pre, entry_invariant compiler op input initial pre⟩

/-- Universal raw correctness and every-prefix permitted reads for arbitrary
admitted finite snapshots, states, code relocations and AF streams. -/
theorem raw (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation)
    (input : BufferCall.Invocation (spec (width op))) (initial : State)
    (pre : BufferCall.Pre (spec (width op)) (IndexSearchWindows.bytes compiler op) input initial) :
    AllExecutions initial (fun result => BufferCall.Post (spec (width op)) input initial result.state) ∧
      BufferCall.RawPolicy (spec (width op)) input initial :=
  VCGen.bufferCall_raw_of_cutpoints (spec (width op)) _ _ (valid compiler op)
    (generated compiler op) input initial pre

/-- BOTH fixed independent tasks for BOTH exact complete frozen windows.
The production bridge retains complete RAM/permissions, ABI and nonarithmetic
flags, original caller/code resources and actual current authority at every
prefix and return. Empty inputs require no data loan or valid data pointer;
compatible read-only aliases and unaligned word buffers are admitted.

This is the registered sequential callable contract, with stable ordinary RAM,
no asynchronous interference and its stated target profile. Full-ELF adapters,
useful resource witnesses, corpus credit and physical hardware are separate. -/
theorem semantics (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation) :
    Grading.BufferTask.SemanticClaim (taskID op) (IndexSearchWindows.bytes compiler op) := by
  have proved := VCGen.bufferCall_semantics_of_cutpoints (spec (width op)) _ _
    (valid compiler op) (generated compiler op)
  cases op <;> exact proved

/-- A conservative output bound on retired model instructions, not an exact
count or a minimum/physical CPU-cost claim. It does not restrict admission. -/
theorem dynamic_bound (compiler : IndexSearchWindows.Compiler) (op : IndexSearchWindows.Operation)
    (input : BufferCall.Invocation (spec (width op))) (initial : State)
    (pre : BufferCall.Pre (spec (width op)) (IndexSearchWindows.bytes compiler op) input initial)
    (choices : Choices) :
    ∃ result, Sequential.run choices
        (((graph compiler op).maxDepth + 1) * ((values (width op) input.value).length + 2)) initial = .ok result ∧
      BufferCall.Post (spec (width op)) input initial result.state ∧
      result.instructions ≤ ((graph compiler op).maxDepth + 1) * ((values (width op) input.value).length + 2) := by
  have binding : CFG.At (IndexSearchWindows.bytes compiler op) (graph compiler op) initial.rip
      (valid compiler op).entry initial := by
    refine ⟨pre.code, ?_⟩
    simp [(valid compiler op).entry_offset]
  have total := (annotations compiler op input initial pre).sound (valid compiler op)
    (valid compiler op).entry_cutpoint binding (entry_invariant compiler op input initial pre) choices
  cases compiler <;> cases op <;> exact total

theorem gcc_byte_semantics : Grading.BufferTask.SemanticClaim .memchrIndex
    (IndexSearchWindows.bytes .defaultGCC .byte) := semantics .defaultGCC .byte

theorem gcc_u32_semantics : Grading.BufferTask.SemanticClaim .linearSearchU32
    (IndexSearchWindows.bytes .defaultGCC .u32) := semantics .defaultGCC .u32

theorem clang_byte_semantics : Grading.BufferTask.SemanticClaim .memchrIndex
    (IndexSearchWindows.bytes .defaultClang .byte) := semantics .defaultClang .byte

theorem clang_u32_semantics : Grading.BufferTask.SemanticClaim .linearSearchU32
    (IndexSearchWindows.bytes .defaultClang .u32) := semantics .defaultClang .u32


end EDSL.Corpus.V1.IndexSearchBodies
