/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known

set_option warningAsError true
-- Elaboration-only transparency for the definitionally equal Fin 8 indices.
set_option allowUnsafeReducibility true

/-! New exact-byte stride32 implementation, reusing the published loop
invariants through a shifted logical origin. No executable memory is patched;
the logical origin only reindexes generic loop state assertions. -/
namespace EDSL.StrideMov
open X86 Stride32

def bytes : List Byte := [0xb8, 0x00, 0x00, 0x00, 0x00, 0x48, 0x85, 0xf6, 0x74, 0x0b,
  0x03, 0x07, 0x48, 0xff, 0xce, 0x48, 0x83, 0xc7, 0x08, 0xeb, 0xf0, 0xc3]

def graph : Sequential.CFG.Graph := ⟨[
  ⟨0, .legacy (.mov32 .rax 0), true, 8⟩,
  ⟨5, .test64 .rsi .rsi, true, 7⟩,
  ⟨8, .je 11, false, 6⟩,
  ⟨10, .addMem32 .rax (.base .rdi), false, 5⟩,
  ⟨12, .dec64 .rsi, false, 4⟩,
  ⟨15, .addImm64 .rdi 8, false, 3⟩,
  ⟨19, .jmp 240, false, 2⟩,
  ⟨21, .legacy .ret, false, 1⟩], 8⟩

theorem valid : Sequential.CFG.Valid bytes graph := Sequential.CFG.check_sound (by decide)
attribute [local reducible] graph Stride32.graph
abbrev Index := graph.Index
instance : NeZero graph.nodes.length := ⟨by decide⟩

def origin (initial : State) : State := { initial with rip := initial.rip + 3 }
def clear (initial : State) : State := executeMov32 initial .rax 0

def initialized {initial : State} {values : List (BitVec 32)} {count : Nat} {target : Word}
    (pre : Pre bytes initial values count target) : Header (origin initial) values count (clear initial) where
  remaining := values
  count := count
  accumulator := 0
  consumed := 0
  length := pre.length
  countBound := pre.count_lt
  counter := pre.count
  pointer := by simp [clear, executeMov32, origin, State.writeRegister]
  value := by simp [clear, executeMov32, State.writeRegister]
  array := pre.array
  split := by omega
  correct := by simp
  frame := by
    have frame : Frame initial (clear initial) :=
      frame_edit initial .rax 0 _ initial.flags (by decide) (by decide) rfl
    exact ⟨frame.memory, frame.stack, frame.preserved, frame.flags⟩
  pc := by simp [clear, executeMov32, origin, BitVec.add_assoc]

theorem guard_exit {initial state : State} {values : List (BitVec 32)} {total : Nat}
    {target : Word} (pre : Pre bytes initial values total target)
    (header : Header (origin initial) values total state) (zero : header.count = 0) (af choice : Bool) :
    Sequential.execute (test state af) (.je 11) choice =
      .ok ⟨.next (exitState (origin initial).rip state af), []⟩ := by
  have canonicalExit : canonical ((origin initial).rip + 18) = true := by
    change canonical (initial.rip + 3 + 18) = true
    rw [BitVec.add_assoc]
    exact valid.canonical_node pre.code (⟨7, by decide⟩ : Index)
  have pc : (test state af).rip = initial.rip + 8 := by
    change state.rip + 3 = _
    rw [header.pc]
    change initial.rip + 3 + 2 + 3 = _
    rw [BitVec.add_assoc, BitVec.add_assoc]
    rfl
  have displacement : (8 : Word) + 2 + (11 : Byte).signExtend 64 = 21 := by decide
  have destination : (test state af).rip + 2 + (11 : Byte).signExtend 64 =
      (origin initial).rip + 18 := by
    rw [pc]
    change initial.rip + 8 + 2 + (11 : Byte).signExtend 64 = initial.rip + 3 + 18
    simp only [BitVec.add_assoc, displacement]
    rfl
  rw [Sequential.execute_je, tested_zero header af, zero]
  simp only [decide_true, executeShortBranch, ite_true, destination, canonicalExit, ok_bind, pure_ok]
  rfl

theorem back_edge {initial state : State} {values : List (BitVec 32)} {total : Nat}
    {target : Word} (pre : Pre bytes initial values total target)
    (header : Header (origin initial) values total state) (pair : Pair header) (af choice : Bool) :
    Sequential.execute (advance (decrement (load (body (origin initial).rip state af) pair.first)))
      (.jmp 240) choice = .ok ⟨.next (cycleState (origin initial).rip state af pair.first), []⟩ := by
  have canonicalHeader : canonical ((origin initial).rip + 2) = true := by
    change canonical (initial.rip + 3 + 2) = true
    rw [BitVec.add_assoc]
    exact valid.canonical_node pre.code (⟨1, by decide⟩ : Index)
  have pc : (advance (decrement (load (body (origin initial).rip state af) pair.first))).rip =
      initial.rip + 19 := by
    change initial.rip + 3 + 7 + 2 + 3 + 4 = _
    simp only [BitVec.add_assoc]
    rfl
  have displacement : (19 : Word) + 2 + (240 : Byte).signExtend 64 = 5 := by decide
  have destination : (advance (decrement (load (body (origin initial).rip state af) pair.first))).rip +
      2 + (240 : Byte).signExtend 64 = (origin initial).rip + 2 := by
    rw [pc]
    change initial.rip + 19 + 2 + (240 : Byte).signExtend 64 = initial.rip + 3 + 2
    simp only [BitVec.add_assoc, displacement]
    rfl
  rw [Sequential.execute_jmp]
  simp only [executeShortBranch, ite_true, destination, canonicalHeader, ok_bind, pure_ok]
  rfl

theorem zero_return {initial state : State} {values : List (BitVec 32)} {total : Nat}
    {target : Word} (pre : Pre bytes initial values total target)
    (header : Header (origin initial) values total state) (af choice : Bool) :
    Sequential.execute (exitState (origin initial).rip state af) (.legacy .ret) choice =
      .ok ⟨.returned (finish (exitState (origin initial).rip state af) target),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  have frame : Frame (origin initial) (exitState (origin initial).rip state af) :=
    header.frame.trans ((frame_test state af).trans (frame_atPC _ _))
  have stack : readWord (exitState (origin initial).rip state af).memory
      ((exitState (origin initial).rip state af).registers .rsp) = .ok target := by
    rw [frame.memory, frame.stack]
    exact pre.stack
  have returned : executeRet (exitState (origin initial).rip state af) =
      .ok (finish (exitState (origin initial).rip state af) target) := by
    unfold executeRet
    rw [stack]
    simp only [ok_bind, pre.canonicalTarget, ite_true, pure_ok]
    rfl
  simp only [Sequential.execute, X86.executeInstruction, returned, ok_bind, pure_ok,
    Sequential.Instruction.operandReads, frame.stack]
  rfl

theorem post_unshift {initial final : State} {values : List (BitVec 32)} {count : Nat} {target : Word}
    (post : Post (origin initial) values count target final) : Post initial values count target final :=
  ⟨post.value, post.memory, post.returnAddress, post.stackPointer, post.preserved, post.flags⟩

inductive Invariant (initial : State) (values : List (BitVec 32)) (total : Nat)
    (target : Word) : Index → State → Prop where
  | entry (pre : Pre bytes initial values total target) : Invariant initial values total target 0 initial
  | loop {state : State} (header : Header (origin initial) values total state) :
      Invariant initial values total target 1 state

inductive Phase (initial : State) (values : List (BitVec 32)) (total : Nat)
    (target : Word) : Index → Nat → Index → State → Prop where
  | entry (pre : Pre bytes initial values total target) : Phase initial values total target 0 (total + 1) 0 initial
  | loop {budget : Nat} {node : Index} {state : State}
      (nonentry : node ≠ 0)
      (inside : Stride32.Phase (origin initial) values total target 1 budget node state) :
      Phase initial values total target 1 budget node state

theorem shifted_offset (node : Index) (nonentry : node ≠ 0) :
    3 + (Stride32.graph.node node).offset = (graph.node node).offset := by
  have all : ∀ node : Index, node ≠ 0 →
      3 + (Stride32.graph.node node).offset = (graph.node node).offset := by decide
  exact all node nonentry

theorem Phase.memory {initial state : State} {values : List (BitVec 32)} {total : Nat}
    {target : Word} {source node : Index} {budget : Nat}
    (inside : Phase initial values total target source budget node state) : state.memory = initial.memory := by
  cases inside with
  | entry => rfl
  | loop _ inner => exact inner.memory

theorem Phase.pc {initial state : State} {values : List (BitVec 32)} {total : Nat}
    {target : Word} {source node : Index} {budget : Nat}
    (inside : Phase initial values total target source budget node state) :
    state.rip = initial.rip + BitVec.ofNat 64 (graph.node node).offset := by
  cases inside with
  | entry => simp [graph, Sequential.CFG.Graph.node]
  | loop nonentry inner =>
    rw [inner.pc]
    change initial.rip + BitVec.ofNat 64 3 + BitVec.ofNat 64 (Stride32.graph.node node).offset = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, shifted_offset node nonentry]

def annotations {initial : State} {values : List (BitVec 32)} {total : Nat} {target : Word}
    (pre : Pre bytes initial values total target) (Access : Sequential.Read → Prop)
    (permission : ∀ read ∈ operandReads initial total, Access read) :
    Sequential.CFG.Annotations bytes graph initial.rip (Post initial values total target)
      (Allowed initial Access) where
  Inv := Invariant initial values total target
  rank := Stride32.rank total
  Interior := Phase initial values total target
  binding source budget node state inside := ⟨by rw [inside.memory]; exact pre.code, inside.pc⟩
  start cut state isCut admitted := by
    cases admitted with
    | entry accepted => exact Phase.entry accepted
    | loop header =>
      simpa only [rank_header header] using
        (Phase.loop (node := 1) (by decide) (Stride32.Phase.header (target := target) header))
  localVC source budget node state inside af := by
    cases inside with
    | entry accepted =>
      let header := initialized accepted
      refine ⟨⟨.next (clear initial), []⟩, rfl, by simp, 1, by decide, .inl ⟨by decide, .loop header, ?_⟩⟩
      rw [rank_header header]
      exact Nat.lt_succ_self total
    | loop _ inner =>
      cases inner with
      | @header state header =>
        refine ⟨⟨.next (test state af), []⟩, ?_, by simp, 2, by decide,
          .inr ⟨by decide, .loop (by decide) (.tested header af)⟩⟩
        change Sequential.execute state (.test64 .rsi .rsi) af = _
        rw [Sequential.execute_test64, BitVec.and_self]
        rfl
      | @tested state header previous =>
        by_cases zero : header.count = 0
        · exact ⟨⟨.next (exitState (origin initial).rip state previous), []⟩, guard_exit pre header zero previous af,
            by simp, 7, by decide, .inr ⟨by decide, .loop (by decide) (.exiting header zero previous)⟩⟩
        · obtain ⟨pair⟩ := header.pair (by omega)
          exact ⟨⟨.next (body (origin initial).rip state previous), []⟩, guard_body header pair previous af,
            by simp, 3, by decide, .inr ⟨by decide, .loop (by decide) (.body header pair previous)⟩⟩
      | @body state header pair previous =>
        refine ⟨⟨.next (load (body (origin initial).rip state previous) pair.first),
          [⟨.data, state.registers .rdi, 4⟩]⟩, ?_, ?_, 4, by decide,
          .inr ⟨by decide, .loop (by decide) (.loaded header pair previous)⟩⟩
        · change Sequential.execute (body (origin initial).rip state previous) (.addMem32 .rax (.base .rdi)) af = _
          rw [Sequential.execute_addMem32]
          simp only [Sequential.Address.eval, header_operand header pair previous, ok_bind, pure_ok]
          rfl
        · intro read member
          have same : read = ⟨.data, state.registers .rdi, 4⟩ := List.mem_singleton.mp member
          subst read
          exact ⟨permission _ (by simpa only [operandReads, origin] using header_read_member header pair), header.frame.memory⟩
      | @loaded state header pair previous =>
        exact ⟨⟨.next (decrement (load (body (origin initial).rip state previous) pair.first)), []⟩,
          rfl, by simp, 5, by decide, .inr ⟨by decide, .loop (by decide) (.decremented header pair previous)⟩⟩
      | @decremented state header pair previous =>
        exact ⟨⟨.next (advance (decrement (load (body (origin initial).rip state previous) pair.first))), []⟩,
          rfl, by simp, 6, by decide, .inr ⟨by decide, .loop (by decide) (.advanced header pair previous)⟩⟩
      | @advanced state header pair previous =>
        let next := nextHeader header pair previous
        refine ⟨⟨.next (cycleState (origin initial).rip state previous pair.first), []⟩,
          back_edge pre header pair previous af, by simp, 1, by decide, .inl ⟨by decide, .loop next, ?_⟩⟩
        rw [rank_header next]
        have count := pair.count
        change pair.rest < header.count
        omega
      | @exiting state header zero previous =>
        refine ⟨⟨.returned (finish (exitState (origin initial).rip state previous) target),
          [⟨.stack, initial.registers .rsp, 8⟩]⟩, zero_return pre header previous af, ?_,
          post_unshift (zero_post header zero previous)⟩
        intro read member
        have same : read = ⟨.stack, initial.registers .rsp, 8⟩ := List.mem_singleton.mp member
        subst read
        exact ⟨permission _ (stack_read_member initial total), header.frame.memory⟩

/-- Exact machine correctness and current-resource authority for every AF stream. -/
theorem semantics : Grading.SemanticClaim Grading.strideTask bytes := by
  constructor
  · intro input initial pre
    let annotation := annotations pre (fun _ => True) (by intros; trivial)
    constructor
    · intro choices
      obtain ⟨result, execution, post, _⟩ := annotation.execution valid (.entry pre) choices
      exact ⟨result, execution, post⟩
    · exact (Grading.annotations_policy annotation valid (.entry pre)
        (fun _ => True) (by intros; trivial)).mono
          (by intros; trivial) (by intros; trivial)
  · intro resource initial pre
    have machinePre := pre.machine
    let annotation := annotations machinePre
      (OS.ArrayResources.ReadPermission resource.shared resource.call.worker)
      (fun read member => operandReads_permission pre.admitted pre.length pre.base pre.stack member)
    constructor
    · intro choices
      obtain ⟨result, execution, post, _⟩ := annotation.execution valid (.entry machinePre) choices
      exact ⟨result, execution, post, pre.admitted.unchangedMemory post.memory⟩
    · exact (Grading.annotations_policy annotation valid (.entry machinePre)
        (Grading.strideReadOnlyTask.current resource) (by
          intro source budget node before inside
          exact pre.admitted.unchangedMemory inside.memory)).mono
            (fun _ current => current) (fun _ _ allowed => allowed.1)

/-- Universal semantics plus independently inhabited machine/resource domains. -/
theorem claim : Grading.Claim .stride32 bytes :=
  ⟨semantics, Grading.domain_nonvacuous .stride32 bytes (by decide) (by decide)⟩

#print axioms valid
#print axioms semantics
#print axioms claim

end EDSL.StrideMov
