/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArraySum64.GCC.Raw

set_option warningAsError true

namespace EDSL.ArraySum64.GCC
open X86 X86.Sequential

/-- Present stages between actual instructions. These annotations contain no
future execution, fuel-success premise or assumed machine postcondition. -/
inductive Prefix (initial : State) (values : List Word) : State → Prop where
  | entry : Prefix initial values initial
  | cleared (af : Bool) : Prefix initial values (clear initial .rax af)
  | header {remaining consumed state} (header : Header initial values remaining consumed state) :
      Prefix initial values state
  | tested {remaining consumed state} (header : Header initial values remaining consumed state) :
      Prefix initial values (test state)
  | body {value rest consumed state} (header : Header initial values (value :: rest) consumed state) :
      Prefix initial values (GCC.body initial.rip state)
  | added {value rest consumed state} (header : Header initial values (value :: rest) consumed state) :
      Prefix initial values (GCC.added initial.rip state value)
  | advanced {value rest consumed state} (header : Header initial values (value :: rest) consumed state) :
      Prefix initial values (GCC.advanced initial.rip state value)
  | exiting {consumed state} (header : Header initial values [] consumed state) :
      Prefix initial values (GCC.exiting initial.rip state)
  | moved {consumed state} (header : Header initial values [] consumed state) :
      Prefix initial values (GCC.moved initial.rip state)

theorem Prefix.memory {initial values state} (inside : Prefix initial values state) :
    state.memory = initial.memory := by
  cases inside with
  | entry => rfl
  | cleared af => rfl
  | header header => exact header.frame.memory
  | tested header => exact (header.frame.trans (frame_test _)).memory
  | body header => exact (header.frame.trans (frame_body ..)).memory
  | added header => exact (header.frame.trans (frame_added ..)).memory
  | advanced header => exact (header.frame.trans (frame_advanced ..)).memory
  | exiting header => exact (header.frame.trans (frame_exiting ..)).memory
  | moved header => exact (header.frame.trans (frame_moved ..)).memory

/-- The SIB address is an original element, despite using the current index. -/
theorem header_read_allowed {initial values value rest consumed state}
    (header : Header initial values (value :: rest) consumed state) :
    ReadAllowed initial values ⟨.data,initial.registers .rdi + BitVec.ofNat 64 (8 * consumed),8⟩ := by
  refine Or.inl ⟨rfl,rfl,consumed,?_,rfl⟩
  have split := header.split
  simp only [List.length_cons] at split
  omega

theorem stack_read_allowed (initial : State) (values : List Word) :
    ReadAllowed initial values ⟨.stack,initial.registers .rsp,8⟩ := Or.inr ⟨rfl,rfl,rfl⟩

/-- Both AF choices enable each decoded current instruction. Continuations
retain the present-state invariant and every operand read has the exact policy. -/
theorem Prefix.advance {initial values target state} (pre : Pre bytes initial values target)
    (inside : Prefix initial values state) :
    ∃ node, Sequential.decodeAt state = .ok (instruction node) ∧
      ∀ af, ∃ observation, Sequential.step af state = .ok observation ∧
        (∀ read ∈ observation.reads, ReadAllowed initial values read) ∧
        match observation.result with
        | .next after => Prefix initial values after
        | .returned _ => True
        | .atomic _ _ | .syscall _ => False := by
  cases inside with
  | entry =>
    have decoded := decode pre.code .clearIndex (by simp [offset])
    refine ⟨.clearIndex,decoded,?_⟩
    intro af
    exact ⟨⟨.next (clear initial .rax af),[]⟩,
      (step_eq_execute af decoded).trans (execute_clear initial .rax af),by simp,Prefix.cleared af⟩
  | cleared prior =>
    have code : CodeAt (clear initial .rax prior).memory initial.rip bytes := pre.code
    have decoded := decode code .clearValue rfl
    refine ⟨.clearValue,decoded,?_⟩
    intro af
    exact ⟨⟨.next (initialized initial prior af),[]⟩,
      (step_eq_execute af decoded).trans (execute_clear _ .rdx af),by simp,
      Prefix.header (initialized_header pre prior af)⟩
  | header header =>
    refine ⟨.header,decode (header.frame.code pre.code) .header header.pc,?_⟩
    intro af
    exact ⟨⟨.next (test _),[]⟩,test_step header pre af,by simp,Prefix.tested header⟩
  | @tested remaining consumed state header =>
    have frame := header.frame.trans (frame_test state)
    refine ⟨.guard,decode (frame.code pre.code) .guard (test_pc header),?_⟩
    intro af
    cases remaining with
    | nil => exact ⟨⟨.next (GCC.exiting initial.rip state),[]⟩,exit_step header pre af,
        by simp,Prefix.exiting header⟩
    | cons value rest => exact ⟨⟨.next (GCC.body initial.rip state),[]⟩,body_step header pre af,
        by simp,Prefix.body header⟩
  | @body value rest consumed state header =>
    have frame := header.frame.trans (frame_body initial.rip state)
    refine ⟨.add,decode (frame.code pre.code) .add rfl,?_⟩
    intro af
    refine ⟨⟨.next (GCC.added initial.rip state value),
      [⟨.data,initial.registers .rdi + BitVec.ofNat 64 (8 * consumed),8⟩]⟩,
      add_step header pre af,?_,Prefix.added header⟩
    intro read member
    have same := List.mem_singleton.mp member
    subst read
    exact header_read_allowed header
  | @added value rest consumed state header =>
    have frame := header.frame.trans (frame_added initial.rip state value)
    refine ⟨.increment,decode (frame.code pre.code) .increment (added_pc ..),?_⟩
    intro af
    exact ⟨⟨.next (GCC.advanced initial.rip state value),[]⟩,increment_step header pre af,
      by simp,Prefix.advanced header⟩
  | @advanced value rest consumed state header =>
    have frame := header.frame.trans (frame_advanced initial.rip state value)
    refine ⟨.back,decode (frame.code pre.code) .back (advanced_pc ..),?_⟩
    intro af
    exact ⟨⟨.next (cycle initial.rip state value),[]⟩,back_step header pre af,
      by simp,Prefix.header (next_header header)⟩
  | @exiting consumed state header =>
    have frame := header.frame.trans (frame_exiting initial.rip state)
    refine ⟨.move,decode (frame.code pre.code) .move rfl,?_⟩
    intro af
    exact ⟨⟨.next (GCC.moved initial.rip state),[]⟩,move_step header pre af,
      by simp,Prefix.moved header⟩
  | @moved consumed state header =>
    have frame := header.frame.trans (frame_moved initial.rip state)
    refine ⟨.ret,decode (frame.code pre.code) .ret (moved_pc ..),?_⟩
    intro af
    refine ⟨⟨.returned (finish (GCC.moved initial.rip state) target),[⟨.stack,initial.registers .rsp,8⟩]⟩,
      ret_step header pre af,?_,True.intro⟩
    intro read member
    have same := List.mem_singleton.mp member
    subst read
    exact stack_read_allowed initial values

theorem Prefix.reachable {initial values target state} (pre : Pre bytes initial values target)
    (reachable : Sequential.Reachable initial state) : Prefix initial values state := by
  obtain ⟨choices,count,reads,block⟩ := reachable
  have closed : ∀ {choices before after count reads},
      Sequential.Block choices before after count reads → Prefix initial values before →
        Prefix initial values after := by
    intro choices before after count reads block
    induction block with
    | nil => intro inside; exact inside
    | @next choices before middle after count reads rest actual tail induction =>
      intro inside
      obtain ⟨_,_,enabled⟩ := inside.advance pre
      obtain ⟨observation,chosen,_,progress⟩ := enabled (choices 0)
      have same := Except.ok.inj (chosen.symm.trans actual)
      cases same
      exact induction progress
    | @atomic choices before middle after count reads rest event actual tail induction =>
      intro inside
      obtain ⟨_,_,enabled⟩ := inside.advance pre
      obtain ⟨observation,chosen,_,progress⟩ := enabled (choices 0)
      have same := Except.ok.inj (chosen.symm.trans actual)
      cases same
      exact False.elim progress
  exact closed block Prefix.entry

/-- Every actually reachable prefix has current code, both AF choices enabled,
successful allowed DATA8/STACK8 reads, and unchanged complete permission RAM. -/
theorem raw_policy {initial values target} (pre : Pre bytes initial values target) : RawPolicy initial values := by
  intro before reachable
  have inside := Prefix.reachable pre reachable
  obtain ⟨node,decoded,enabled⟩ := inside.advance pre
  refine ⟨inside.memory,⟨instruction node,decoded,readOnly node⟩,?_⟩
  intro af
  obtain ⟨observation,actual,permission,_⟩ := enabled af
  have effect : execute before (instruction node) af = .ok observation := by
    rw [← step_eq_execute af decoded]
    exact actual
  refine ⟨observation,actual,?_,?_⟩
  · intro read member
    exact ⟨permission read member,observed_reads_succeed actual read member⟩
  · obtain ⟨after,next | ⟨returned,_⟩⟩ := CFG.execute_result (readOnly node) effect
    · rw [next]
      exact CFG.execute_next_memory (readOnly node) effect next
    · rw [returned]
      exact CFG.execute_returned_memory (readOnly node) effect returned

end EDSL.ArraySum64.GCC
