/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArraySum64.Clang.Steps

set_option warningAsError true

namespace EDSL.ArraySum64.Clang
open X86 X86.Sequential

/-- Current instruction pre-states. None assumes future successful execution
or an eventual postcondition. The fused ADD has exactly one successor phase. -/
inductive Phase (initial : State) (values : List Word) : State → Prop where
  | entry : Phase initial values initial
  | tested (af : Bool) : Phase initial values (test initial af)
  | positive (af : Bool) (nonempty : values ≠ []) : Phase initial values (positiveState initial af)
  | indexed (testAF indexAF : Bool) (nonempty : values ≠ []) :
      Phase initial values (indexState initial testAF indexAF)
  | header (remaining : List Word) (consumed : Nat) (state : State)
      (invariant : Header initial values remaining consumed state) : Phase initial values state
  | added (state : State) (rest : List Word) (consumed : Nat) (value : Word)
      (invariant : Header initial values (value :: rest) consumed state) :
      Phase initial values (add state value)
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
  | added _ _ _ _ header => exact header.frame.trans (frame_add ..)
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
    | nil => exact ⟨8,header.pc⟩
    | cons value rest => exact ⟨4,header.pc⟩
  | added state rest consumed value header =>
    refine ⟨5,?_⟩
    simp only [add,edit,header.pc,loopOffset,List.isEmpty_cons,BitVec.add_assoc]
    rfl
  | advanced state rest consumed value header =>
    refine ⟨6,?_⟩
    simp only [Clang.advanced,increment,add,edit,header.pc,loopOffset,List.isEmpty_cons,BitVec.add_assoc]
    rfl
  | testedIndex state rest consumed value header =>
    refine ⟨7,?_⟩
    simp only [Clang.testedIndex,compareIndex,Clang.advanced,increment,add,edit,
      header.pc,loopOffset,List.isEmpty_cons,BitVec.add_assoc]
    rfl
  | empty af _ => exact ⟨9,rfl⟩
  | emptyReturn testAF resultAF _ =>
    refine ⟨10,?_⟩
    change initial.rip + 22 + 2 = initial.rip + 24
    rw [BitVec.add_assoc]
    rfl

/-- Both AF choices enable the actual decoded instruction. Its only possible
operand is the current original DATA8 element or the original caller STACK8. -/
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
      refine ⟨_,step_add pre header af,?_,.added _ rest consumed value header,
        (frame_add before value).memory⟩
      intro read member
      have same := List.mem_singleton.mp member
      subst read
      have bound : consumed < values.length := by
        have length := header.length
        simp only [List.length_cons] at length
        omega
      exact .inl ⟨rfl,rfl,consumed,bound,rfl⟩
  | added state rest consumed value header =>
    exact ⟨_,step_increment pre header af,by simp,.advanced state rest consumed value header,
      (frame_increment (add state value)).memory⟩
  | advanced state rest consumed value header =>
    exact ⟨_,step_compareIndex pre header af,by simp,.testedIndex state rest consumed value header,rfl⟩
  | testedIndex state rest consumed value header =>
    exact ⟨_,step_cycle pre header af,by simp,
      .header rest (consumed + 1) _ (nextHeader header),(frame_atPC (Clang.testedIndex state value) _).memory⟩
  | empty previous empty =>
    exact ⟨_,step_clearEmpty pre previous af,by simp,.emptyReturn previous af empty,
      (frame_clear (emptyState initial previous) .rax af (by decide) (by decide)).memory⟩
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

/-- Every actually reachable prefix decodes read-only code, preserves complete
RAM/permissions, and performs only successful allowed DATA8 or STACK8 reads. -/
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

end EDSL.ArraySum64.Clang
