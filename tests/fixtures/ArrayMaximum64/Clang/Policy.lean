/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArrayMaximum64.Clang.Steps

set_option warningAsError true

namespace EDSL.ArrayMaximum64.Clang
open X86 X86.Sequential

/-- Ghost descriptions of current instruction pre-states only. In particular,
no constructor assumes successful future execution or an eventual postcondition. -/
inductive Phase (initial : State) (values : List Word) : State → Prop where
  | entry : Phase initial values initial
  | tested (af : Bool) : Phase initial values (test initial af)
  | positive (af : Bool) (nonempty : values ≠ []) : Phase initial values (positiveState initial af)
  | indexed (testAF indexAF : Bool) (nonempty : values ≠ []) :
      Phase initial values (indexState initial testAF indexAF)
  | header (remaining : List Word) (consumed : Nat) (state : State)
      (invariant : Header initial values remaining consumed state) : Phase initial values state
  | loaded (state : State) (rest : List Word) (consumed : Nat) (value : Word)
      (invariant : Header initial values (value :: rest) consumed state) :
      Phase initial values (load state value)
  | compared (state : State) (rest : List Word) (consumed : Nat) (value : Word)
      (invariant : Header initial values (value :: rest) consumed state) :
      Phase initial values (Clang.compared state value)
  | selected (state : State) (rest : List Word) (consumed : Nat) (value : Word)
      (invariant : Header initial values (value :: rest) consumed state) :
      Phase initial values (Clang.selected state value)
  | advanced (state : State) (rest : List Word) (consumed : Nat) (value : Word)
      (invariant : Header initial values (value :: rest) consumed state) :
      Phase initial values (Clang.advanced state value)
  | testedIndex (state : State) (rest : List Word) (consumed : Nat) (value : Word)
      (invariant : Header initial values (value :: rest) consumed state) :
      Phase initial values (Clang.testedIndex state value)
  | empty (af : Bool) (empty : values = []) : Phase initial values (emptyState initial af)
  | emptyReturn (testAF resultAF : Bool) (empty : values = []) :
      Phase initial values (Clang.emptyReturn initial testAF resultAF)

theorem Phase.frame {initial before : State} {values : List Word}
    (inside : Phase initial values before) : Frame initial before := by
  cases inside with
  | entry => exact .refl initial
  | tested af => exact frame_test initial af
  | positive af _ => exact frame_positive initial af
  | indexed testAF indexAF _ => exact frame_index initial testAF indexAF
  | header _ _ _ header => exact header.frame
  | loaded _ _ _ _ header => exact header.frame.trans (frame_load ..)
  | compared _ _ _ _ header => exact header.frame.trans (frame_compared ..)
  | selected _ _ _ _ header => exact header.frame.trans (frame_selected ..)
  | advanced _ _ _ _ header => exact header.frame.trans (frame_advanced ..)
  | testedIndex _ _ _ _ header => exact header.frame.trans (frame_testedIndex ..)
  | empty af _ => exact frame_empty initial af
  | emptyReturn testAF resultAF _ => exact frame_emptyReturn initial testAF resultAF

theorem Phase.binding {initial before : State} {values : List Word}
    (inside : Phase initial values before) :
    ∃ node : Index, before.rip = initial.rip + BitVec.ofNat 64 (graph.node node).offset := by
  cases inside with
  | entry => exact ⟨0,by simp [graph,CFG.Graph.node]⟩
  | tested af => exact ⟨1,rfl⟩
  | positive af _ => exact ⟨2,rfl⟩
  | indexed testAF indexAF _ =>
    refine ⟨3,?_⟩
    change initial.rip + 5 + 2 = initial.rip + 7
    rw [BitVec.add_assoc]
    rfl
  | header remaining consumed state header =>
    cases remaining with
    | nil => exact ⟨10,header.pc⟩
    | cons value rest => exact ⟨4,header.pc⟩
  | loaded state rest consumed value header =>
    refine ⟨5,?_⟩
    simp only [load,edit,header.pc,loopOffset,List.isEmpty_cons,BitVec.add_assoc]
    rfl
  | compared state rest consumed value header =>
    refine ⟨6,?_⟩
    simp only [Clang.compared,compareValue,load,edit,header.pc,loopOffset,List.isEmpty_cons,
      BitVec.add_assoc]
    rfl
  | selected state rest consumed value header =>
    refine ⟨7,?_⟩
    simp only [Clang.selected,select,Clang.compared,compareValue,load,edit,header.pc,loopOffset,
      List.isEmpty_cons,BitVec.add_assoc]
    rfl
  | advanced state rest consumed value header =>
    refine ⟨8,?_⟩
    simp only [Clang.advanced,increment,Clang.selected,select,Clang.compared,compareValue,load,edit,
      header.pc,loopOffset,List.isEmpty_cons,BitVec.add_assoc]
    rfl
  | testedIndex state rest consumed value header =>
    refine ⟨9,?_⟩
    simp only [Clang.testedIndex,compareIndex,Clang.advanced,increment,Clang.selected,select,
      Clang.compared,compareValue,load,edit,header.pc,loopOffset,List.isEmpty_cons,BitVec.add_assoc]
    rfl
  | empty af _ => exact ⟨11,rfl⟩
  | emptyReturn testAF resultAF _ =>
    refine ⟨12,?_⟩
    change initial.rip + 29 + 2 = initial.rip + 31
    rw [BitVec.add_assoc]
    rfl

/-- Both AF choices enable the actual decoded step. Only the current original
array element or the original caller slot can occur as an operand read. -/
theorem Phase.enabled {initial before : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (inside : Phase initial values before) (af : Bool) :
    ∃ observation, Sequential.step af before = .ok observation ∧
      (∀ read ∈ observation.reads, ReadAllowed initial values read) ∧
      match observation.result with
      | .next after => Phase initial values after ∧ after.memory = before.memory
      | .returned after => after.memory = before.memory
      | .atomic _ _ | .syscall _ => False := by
  cases inside with
  | entry => exact ⟨_,step_test pre af,by simp,.tested af,rfl⟩
  | tested previous =>
    by_cases empty : values = []
    · exact ⟨_,step_empty pre empty previous af,by simp,.empty previous empty,rfl⟩
    · exact ⟨_,step_positive pre empty previous af,by simp,.positive previous empty,rfl⟩
  | positive previous nonempty =>
    exact ⟨_,step_clearIndex pre previous af,by simp,.indexed previous af nonempty,rfl⟩
  | indexed testAF indexAF nonempty =>
    exact ⟨_,step_clearResult pre testAF indexAF af,by simp,
      .header values 0 _ (initialized pre nonempty testAF indexAF af),
      (frame_clear (indexState initial testAF indexAF) .rax af (by decide) (by decide)).memory⟩
  | header remaining consumed state header =>
    cases remaining with
    | nil =>
      refine ⟨_,step_return pre header af,?_,rfl⟩
      intro read member
      have same := List.mem_singleton.mp member
      subst read
      exact .inr ⟨rfl,rfl,rfl⟩
    | cons value rest =>
      refine ⟨_,step_load pre header af,?_,.loaded _ rest consumed value header,rfl⟩
      intro read member
      have same := List.mem_singleton.mp member
      subst read
      have bound : consumed < values.length := by
        have length := header.length
        simp only [List.length_cons] at length
        omega
      exact .inl ⟨rfl,rfl,consumed,bound,rfl⟩
  | loaded state rest consumed value header =>
    exact ⟨_,step_compareValue pre header af,by simp,.compared state rest consumed value header,rfl⟩
  | compared state rest consumed value header =>
    exact ⟨_,step_select pre header af,by simp,.selected state rest consumed value header,rfl⟩
  | selected state rest consumed value header =>
    exact ⟨_,step_increment pre header af,by simp,.advanced state rest consumed value header,
      (frame_increment (Clang.selected state value)).memory⟩
  | advanced state rest consumed value header =>
    exact ⟨_,step_compareIndex pre header af,by simp,.testedIndex state rest consumed value header,rfl⟩
  | testedIndex state rest consumed value header =>
    exact ⟨_,step_cycle pre header af,by simp,
      .header rest (consumed + 1) _ (nextHeader header),rfl⟩
  | empty previous empty =>
    exact ⟨_,step_clearEmpty pre previous af,by simp,.emptyReturn previous af empty,rfl⟩
  | emptyReturn testAF resultAF _ =>
    refine ⟨_,step_returnEmpty pre testAF resultAF af,?_,rfl⟩
    intro read member
    have same := List.mem_singleton.mp member
    subst read
    exact .inr ⟨rfl,rfl,rfl⟩

theorem Phase.continues {initial before after : State} {values : List Word} {target : Word}
    {af : Bool} {outcome : StepResult} {reads : List Read}
    (pre : Pre bytes initial values target) (inside : Phase initial values before)
    (actual : Sequential.step af before = .ok ⟨outcome,reads⟩)
    (next : nextState outcome = some after) : Phase initial values after := by
  obtain ⟨expected,chosen,_,continuing⟩ := inside.enabled pre af
  have same := Except.ok.inj (chosen.symm.trans actual)
  cases same
  cases outcome with
  | next state => cases next; exact continuing.1
  | atomic event state => exact False.elim continuing
  | returned state | syscall request => cases next

theorem Phase.block {initial before final : State} {values : List Word} {target : Word}
    {choices : Choices} {count : Nat} {reads : List Read}
    (pre : Pre bytes initial values target) (inside : Phase initial values before)
    (block : Sequential.Block choices before final count reads) : Phase initial values final := by
  induction block with
  | nil => exact inside
  | next step tail induction | atomic step tail induction =>
    exact induction (inside.continues pre step rfl)

theorem phase_reachable {initial before : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (reachable : Sequential.Reachable initial before) :
    Phase initial values before := by
  obtain ⟨_,_,_,block⟩ := reachable
  exact Phase.block pre .entry block

/-- Prefix-sensitive policy for actual decoded read-only instructions, complete
unchanged memory and permission maps, and successful allowed DATA8/STACK8. -/
theorem raw_policy {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) : RawPolicy initial values := by
  intro before reachable
  have inside := phase_reachable pre reachable
  obtain ⟨node,pc⟩ := inside.binding
  have decoded := valid.decoded pre.code node before inside.frame.memory pc
  refine ⟨inside.frame.memory,⟨_,decoded,(valid.nodes node).2.2.1⟩,?_⟩
  intro af
  obtain ⟨observation,actual,allowed,continuing⟩ := inside.enabled pre af
  refine ⟨observation,actual,?_,?_⟩
  · intro read member
    exact ⟨allowed read member,observed_reads_succeed actual read member⟩
  · cases result : observation.result with
    | next after =>
      simp only [result] at continuing ⊢
      exact continuing.2
    | returned after => simpa only [result] using continuing
    | atomic event after | syscall request =>
      simp only [result] at continuing

end EDSL.ArrayMaximum64.Clang
