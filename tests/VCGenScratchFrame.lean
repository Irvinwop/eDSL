/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.ScratchFrame
import EDSL.X86.VCGen.PureCall
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.VCGenScratchFrame
open X86 Sequential X86.VCGen PureCall

namespace HalveAdd

/-- Independent unsigned arithmetic, including full64 modular overflow. -/
def spec : Spec where
  Input := Word × Word
  arguments input index := if index.val = 0 then some (.word64 input.1)
    else if index.val = 1 then some (.word64 input.2) else none
  domain _ := True
  result input output := output.toNat = (input.1.toNat / 2 + input.2.toNat) % 2^64
  useful _ := True

/-- MOV RAX,RDI; SHR RAX,1; ADD RAX,RSI; RET. These literal bytes are
decoded and authenticated by production discovery/checking. -/
def bytes : List Byte := [0x48, 0x89, 0xf8, 0x48, 0xd1, 0xe8, 0x48, 0x01, 0xf0, 0xc3]
def graph : CFG.Graph := vcgen_graph bytes
theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide +kernel)
abbrev entry : graph.Index := ⟨0, by decide +kernel⟩
def scratch : List Register := [.rax]

def Evidence (input : Invocation spec) (initial : State) (result : Result) : Prop :=
  ScratchFrame (.rsp :: scratch) initial result.state ∧
  spec.result input.value (result.state.registers .rax) ∧
  result.state.rip = input.returnAddress ∧
  result.state.registers .rsp = initial.registers .rsp + 8

theorem generated (input : Invocation spec) (initial : State)
    (pre : Pre spec bytes input initial) :
    wp graph initial.rip (PureCallAllowed initial) 4 entry initial (Evidence input initial) := by
  have left : initial.registers .rdi = input.value.1 :=
    pre.arguments 0 (.word64 input.value.1) rfl
  have right : initial.registers .rsi = input.value.2 :=
    pre.arguments 1 (.word64 input.value.2) rfl
  have framed := ScratchFrame.refl scratch initial
  have terminal := framed.weaken (List.subset_cons_self Register.rsp scratch)
  vcgen_run graph entry simp [PureCallAllowed, RawRead, pre.stack, pre.returnCanonical,
    BitVec.add_assoc]
  refine ⟨?_, ?_, rfl, rfl⟩
  · vcgen_factor => vcgen_scratch_frame terminal
  · simp [spec, Result.prepend, left, right, BitVec.toNat_add,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem project (input : Invocation spec) (initial : State) (result : Result)
    (evidence : Evidence input initial result) : Post spec input initial result.state :=
  evidence.1.post_return (by decide +kernel) evidence.2.1 evidence.2.2.1 evidence.2.2.2

/-- Arbitrary dirty GPRs, full flags and all three original memory functions;
only the declared arguments/code/caller slot are constrained. Every AF stream
executes these actual decoded steps with the independent value and full frame. -/
theorem executes (input : Invocation spec) (initial : State)
    (pre : Pre spec bytes input initial) (choices : Choices) :
    ∃ result, Sequential.run choices 4 initial = .ok result ∧
      Evidence input initial result ∧ CheckedTrace (PureCallAllowed initial) choices initial result := by
  obtain ⟨result, actual, evidence, _, trace⟩ := run_sound valid pre.code
    (by change initial.rip = initial.rip + 0#64; simp) (generated input initial pre) choices
  exact ⟨result, actual, evidence, trace⟩

/-- The same generated proof includes every-prefix current-resource framing
through the existing scalar-call bridge; no new OS assumption is introduced. -/
theorem semantics : Grading.ReadOnlySemanticClaim (readOnlyTask spec) bytes :=
  pureCall_semantics_of_generated spec bytes graph valid entry (by decide +kernel) 4
    Evidence project generated

end HalveAdd

namespace Countdown

/-- A positive countdown returns its last positive count, independently of
initial RAX/RCX and flags. The invariant carries only the live positive count. -/
def spec : Spec where
  Input := Word
  arguments value index := if index.val = 0 then some (.word64 value) else none
  domain value := value ≠ 0
  result _ output := output.toNat = 1
  useful _ := True

/-- MOV RCX,RDI; header: MOV RAX,RCX; TEST RAX,RAX; LOOP header; RET. -/
def bytes : List Byte :=
  [0x48, 0x89, 0xf9, 0x48, 0x89, 0xc8, 0x48, 0x85, 0xc0, 0xe2, 0xf8, 0xc3]
def graph : CFG.Graph := vcgen_graph bytes
theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide +kernel)
abbrev entry : graph.Index := ⟨0, by decide +kernel⟩
abbrev header : graph.Index := ⟨1, by decide +kernel⟩
def scratch : List Register := [.rax, .rcx]

def Inv (initial : State) (node : graph.Index) (state : State) : Prop :=
  ScratchFrame scratch initial state ∧
  if node.val = 0 then state.registers .rdi ≠ 0 else state.registers .rcx ≠ 0

def rank (node : graph.Index) (state : State) : Nat :=
  if node.val = 0 then (state.registers .rdi).toNat + 1 else (state.registers .rcx).toNat

def annotations (input : Invocation spec) (initial : State) (pre : Pre spec bytes input initial) :
    Cutpoints.Annotations bytes graph initial.rip (Post spec input initial)
      (fun _ read => RawRead initial read) where
  Inv := Inv initial
  rank := rank
  blocks cut state isCut binding admitted := by
    have cuts : cut = entry ∨ cut = header := by
      have allCuts : ∀ node : graph.Index, graph.cutpoint node = true →
          node = entry ∨ node = header := by decide +kernel
      exact allCuts cut isCut
    obtain ⟨framed, positive⟩ := admitted
    have memory := framed.memory
    have rsp := framed.registers .rsp (by decide +kernel)
    rcases cuts with same | same
    · subst cut
      have pc : state.rip = initial.rip := by
        simpa [CFG.Graph.node, graph, entry] using binding.2
      change Cutpoints.wp graph initial.rip (Post spec input initial)
        (fun _ read => RawRead initial read) (Inv initial) rank (rank entry state) 6 entry state
      vcgen_block graph entry simp [pc, memory]
      change (ScratchFrame scratch initial _ ∧ state.registers .rdi ≠ 0) ∧
        (state.registers .rdi).toNat < (state.registers .rdi).toNat + 1
      refine ⟨⟨?_, positive⟩, Nat.lt_succ_self _⟩
      vcgen_factor => vcgen_scratch_frame framed
    · subst cut
      have pc : state.rip = initial.rip + 3#64 := by
        simpa [CFG.Graph.node, graph, header] using binding.2
      have canonicalHeader : canonical (initial.rip + 3#64) = true := by
        simpa [CFG.Graph.node, graph, header] using valid.canonical_node binding.1 header
      change state.registers .rcx ≠ 0 at positive
      have decreases : (state.registers .rcx - 1).toNat < (state.registers .rcx).toNat := by
        have nonzero : (state.registers .rcx).toNat ≠ 0 := by
          intro zero
          exact positive (BitVec.eq_of_toNat_eq zero)
        have oneLe : (1 : Word) ≤ state.registers .rcx := by
          change 1 ≤ (state.registers .rcx).toNat
          omega
        rw [BitVec.toNat_sub_of_le oneLe]
        change (state.registers .rcx).toNat - 1 < (state.registers .rcx).toNat
        omega
      by_cases last : state.registers .rcx - (1#64) = (0#64)
      · have one : state.registers .rcx = 1 := by
          simpa using BitVec.sub_eq_iff_eq_add.mp last
        change Cutpoints.wp graph initial.rip (Post spec input initial)
          (fun _ read => RawRead initial read) (Inv initial) rank (rank header state) 5 header state
        vcgen_block graph header simp [RawRead, pc, memory, rsp, pre.stack,
          pre.returnCanonical, one, BitVec.add_assoc]
        refine ScratchFrame.post_return (scratch := scratch) ?_ (by decide +kernel) ?_ rfl rfl
        · vcgen_factor => vcgen_scratch_frame
            (framed.weaken (List.subset_cons_self Register.rsp scratch))
        · simp [spec]
      · change Cutpoints.wp graph initial.rip (Post spec input initial)
          (fun _ read => RawRead initial read) (Inv initial) rank (rank header state) 5 header state
        vcgen_block graph header simp [pc, memory, last, canonicalHeader, BitVec.add_assoc]
        dsimp only [Inv, rank]
        refine ⟨⟨?_, last⟩, ?_⟩
        · vcgen_factor => vcgen_scratch_frame framed
        · simpa using decreases

theorem generated (input : Invocation spec) (initial : State) (pre : Pre spec bytes input initial) :
    ∃ annotations : Cutpoints.Annotations bytes graph initial.rip
      (Post spec input initial) (fun _ read => RawRead initial read),
      annotations.Inv valid.entry initial := by
  refine ⟨annotations input initial pre, ScratchFrame.refl _ _, ?_⟩
  have argument : initial.registers .rdi = input.value := pre.arguments 0 (.word64 input.value) rfl
  change initial.registers .rdi ≠ (0#64)
  intro zero
  apply pre.domain
  exact argument.symm.trans zero

theorem semantics : Grading.ReadOnlySemanticClaim (readOnlyTask spec) bytes :=
  pureCall_semantics_of_cutpoints spec bytes graph valid generated

/-- Unbounded positive inputs and arbitrary AF streams use the independently
decreasing natural rank. No successful future execution is an input premise. -/
theorem executes (input : Invocation spec) (initial : State)
    (pre : Pre spec bytes input initial) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧ Post spec input initial result.state :=
  (pureCall_raw_of_cutpoints spec bytes graph valid generated input initial pre).1 choices

end Countdown

namespace ProtectedWrite

/-- Owned synthetic negative: MOV RBX,RDI; RET. RBX is ABI callee-saved. -/
def bytes : List Byte := [0x48, 0x89, 0xfb, 0xc3]
def graph : CFG.Graph := vcgen_graph bytes
theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide +kernel)
abbrev entry : graph.Index := ⟨0, by decide +kernel⟩

theorem generated (initial : State) (target : Word)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) :
    wp graph initial.rip (PureCallAllowed initial) 2 entry initial
      (fun result => result.state.registers .rbx = initial.registers .rdi) := by
  vcgen_run graph entry simp [PureCallAllowed, RawRead, stack, canonicalTarget]
  rfl

/-- This actual decoded complete path cannot acquire the promised scalar
frame when the write changes RBX. This is a proved negation, beyond a tactic
failure or a finite observation. Arbitrary original RAM/permissions remain. -/
theorem rejected (initial : State) (target : Word)
    (code : CodeAt initial.memory initial.rip bytes)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true)
    (different : initial.registers .rdi ≠ initial.registers .rbx) (choices : Choices) :
    ¬ wp graph initial.rip (PureCallAllowed initial) 2 entry initial
      (fun result => ScratchFrame [.rsp, .rax] initial result.state) := by
  intro promised
  have pc : initial.rip = initial.rip + BitVec.ofNat 64 (graph.node entry).offset := by
    change initial.rip = initial.rip + 0#64
    simp
  obtain ⟨actual, execution, changed, _, _⟩ :=
    run_sound valid code pc (generated initial target stack canonicalTarget) choices
  obtain ⟨claimed, claimedExecution, framed, _, _⟩ := run_sound valid code pc promised choices
  have same : claimed = actual := Except.ok.inj (claimedExecution.symm.trans execution)
  subst claimed
  exact different (changed.symm.trans (framed.registers .rbx (by decide +kernel)))

end ProtectedWrite

#print axioms HalveAdd.executes
#print axioms HalveAdd.semantics
#print axioms Countdown.executes
#print axioms Countdown.semantics
#print axioms ProtectedWrite.rejected

end EDSL.Tests.VCGenScratchFrame

#audit_edsl
