/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Stride32.Steps

namespace EDSL.Stride32
open X86

inductive Invariant (initial : State) (values : List (BitVec 32)) (total : Nat)
    (target : Word) : Index → State → Prop where
  | entry (pre : Pre bytes initial values total target) : Invariant initial values total target 0 initial
  | loop {state : State} (header : Header initial values total state) :
      Invariant initial values total target 1 state

/-- Interior annotations describe current local state after individual machine
operations. They contain no assumed future execution or result. -/
inductive Phase (initial : State) (values : List (BitVec 32)) (total : Nat)
    (target : Word) : Index → Nat → Index → State → Prop where
  | entry (pre : Pre bytes initial values total target) : Phase initial values total target 0 (total + 1) 0 initial
  | header {state : State} (header : Header initial values total state) :
      Phase initial values total target 1 header.count 1 state
  | tested {state : State} (header : Header initial values total state) (af : Bool) :
      Phase initial values total target 1 header.count 2 (test state af)
  | body {state : State} (header : Header initial values total state) (pair : Pair header) (af : Bool) :
      Phase initial values total target 1 header.count 3 (body initial.rip state af)
  | loaded {state : State} (header : Header initial values total state) (pair : Pair header) (af : Bool) :
      Phase initial values total target 1 header.count 4 (load (body initial.rip state af) pair.first)
  | decremented {state : State} (header : Header initial values total state) (pair : Pair header) (af : Bool) :
      Phase initial values total target 1 header.count 5 (decrement (load (body initial.rip state af) pair.first))
  | advanced {state : State} (header : Header initial values total state) (pair : Pair header) (af : Bool) :
      Phase initial values total target 1 header.count 6 (advance (decrement (load (body initial.rip state af) pair.first)))
  | exiting {state : State} (header : Header initial values total state) (zero : header.count = 0) (af : Bool) :
      Phase initial values total target 1 header.count 7 (exitState initial.rip state af)

def rank (total : Nat) (node : Index) (state : State) : Nat :=
  if node.val = 0 then total + 1 else (state.registers .rsi).toNat

theorem rank_header {initial state : State} {values : List (BitVec 32)} {total : Nat}
    (header : Header initial values total state) : rank total 1 state = header.count :=
  header.rank

theorem Phase.memory {initial state : State} {values : List (BitVec 32)} {total : Nat}
    {target : Word} {source node : Index} {budget : Nat}
    (inside : Phase initial values total target source budget node state) : state.memory = initial.memory := by
  cases inside with
  | entry => rfl
  | header header | tested header af | body header pair af | loaded header pair af
  | decremented header pair af | advanced header pair af | exiting header zero af => exact header.frame.memory

theorem Phase.pc {initial state : State} {values : List (BitVec 32)} {total : Nat}
    {target : Word} {source node : Index} {budget : Nat}
    (inside : Phase initial values total target source budget node state) :
    state.rip = initial.rip + BitVec.ofNat 64 (graph.node node).offset := by
  cases inside with
  | entry => simp [graph, Sequential.CFG.Graph.node]
  | header header => exact header.pc
  | tested header af =>
    simp only [test, header.pc, graph, Sequential.CFG.Graph.node, BitVec.add_assoc]
    rfl
  | body header pair af => rfl
  | loaded header pair af =>
    simp only [load, Stride32.body, atPC, edit, graph, Sequential.CFG.Graph.node, BitVec.add_assoc]
    rfl
  | decremented header pair af =>
    simp only [decrement, load, Stride32.body, atPC, edit, graph, Sequential.CFG.Graph.node, BitVec.add_assoc]
    rfl
  | advanced header pair af =>
    simp only [advance, decrement, load, Stride32.body, atPC, edit, graph, Sequential.CFG.Graph.node, BitVec.add_assoc]
    rfl
  | exiting header zero af => rfl

def Allowed (initial : State) (Access : Sequential.Read → Prop) (state : State)
    (read : Sequential.Read) : Prop := Access read ∧ state.memory = initial.memory

def annotations {initial : State} {values : List (BitVec 32)} {total : Nat} {target : Word}
    (pre : Pre bytes initial values total target) (Access : Sequential.Read → Prop)
    (permission : ∀ read ∈ operandReads initial total, Access read) :
    Sequential.CFG.Annotations bytes graph initial.rip (Post initial values total target) (Allowed initial Access) where
  Inv := Invariant initial values total target
  rank := rank total
  Interior := Phase initial values total target
  binding source budget node state inside := ⟨by rw [inside.memory]; exact pre.code, inside.pc⟩
  start cut state isCut admitted := by
    cases admitted with
    | entry accepted => exact Phase.entry accepted
    | loop header => simpa only [rank_header header] using Phase.header (target := target) header
  localVC source budget node state inside af := by
    cases inside with
    | entry accepted =>
      let header := initialized accepted af
      refine ⟨⟨.next (clear initial af), []⟩, rfl, by simp, 1, by decide, .inl ⟨by decide, .loop header, ?_⟩⟩
      rw [rank_header header]
      exact Nat.lt_succ_self total
    | @header state header =>
      refine ⟨⟨.next (test state af), []⟩, ?_, by simp, 2, by decide, .inr ⟨by decide, .tested header af⟩⟩
      change Sequential.execute state (.test64 .rsi .rsi) af = _
      rw [Sequential.execute_test64, BitVec.and_self]
      rfl
    | @tested state header previous =>
      by_cases zero : header.count = 0
      · exact ⟨⟨.next (exitState initial.rip state previous), []⟩, guard_exit pre header zero previous af,
          by simp, 7, by decide, .inr ⟨by decide, .exiting header zero previous⟩⟩
      · obtain ⟨pair⟩ := header.pair (by omega)
        exact ⟨⟨.next (body initial.rip state previous), []⟩, guard_body header pair previous af,
          by simp, 3, by decide, .inr ⟨by decide, .body header pair previous⟩⟩
    | @body state header pair previous =>
      refine ⟨⟨.next (load (body initial.rip state previous) pair.first),
        [⟨.data, state.registers .rdi, 4⟩]⟩, ?_, ?_, 4, by decide, .inr ⟨by decide, .loaded header pair previous⟩⟩
      · change Sequential.execute (body initial.rip state previous) (.addMem32 .rax (.base .rdi)) af = _
        rw [Sequential.execute_addMem32]
        simp only [Sequential.Address.eval, header_operand header pair previous, ok_bind, pure_ok]
        rfl
      · intro read member
        have same : read = ⟨.data, state.registers .rdi, 4⟩ := List.mem_singleton.mp member
        subst read
        exact ⟨permission _ (header_read_member header pair), header.frame.memory⟩
    | @loaded state header pair previous =>
      exact ⟨⟨.next (decrement (load (body initial.rip state previous) pair.first)), []⟩,
        rfl, by simp, 5, by decide, .inr ⟨by decide, .decremented header pair previous⟩⟩
    | @decremented state header pair previous =>
      exact ⟨⟨.next (advance (decrement (load (body initial.rip state previous) pair.first))), []⟩,
        rfl, by simp, 6, by decide, .inr ⟨by decide, .advanced header pair previous⟩⟩
    | @advanced state header pair previous =>
      let next := nextHeader header pair previous
      refine ⟨⟨.next (cycleState initial.rip state previous pair.first), []⟩,
        back_edge pre header pair previous af, by simp, 1, by decide, .inl ⟨by decide, .loop next, ?_⟩⟩
      rw [rank_header next]
      have count := pair.count
      change pair.rest < header.count
      omega
    | @exiting state header zero previous =>
      refine ⟨⟨.returned (finish (exitState initial.rip state previous) target),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩, zero_return pre header previous af, ?_,
        zero_post header zero previous⟩
      intro read member
      have same : read = ⟨.stack, initial.registers .rsp, 8⟩ := List.mem_singleton.mp member
      subst read
      exact ⟨permission _ (stack_read_member initial total), header.frame.memory⟩

end EDSL.Stride32
