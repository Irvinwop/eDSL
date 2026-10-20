/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallResources
import EDSL.X86.CallReturn.Machine
import EDSL.X86.VCGen.Core
import EDSL.X86.VCGen.Cutpoints

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.Sequential

/-- Independent width characterization: the unchanged high slice is concatenated
with the new byte. This also rules out sign extension and low32 zero extension. -/
theorem replaceLow8_eq_append (old : Word) (value : Byte) :
    replaceLow8 old value = old.extractLsb' 8 56 ++ value := by
  have mask : (0xffffffffffffff00 : Word) =
      ~~~((BitVec.allOnes 8).setWidth 64) := by decide +kernel
  unfold replaceLow8
  rw [mask]
  apply BitVec.eq_of_getLsbD_eq
  intro index inside
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_append]
  by_cases low : index < 8
  · simp [inside, low]
  · have high : index - 8 < 56 := by omega
    have adjust : 8 + (index - 8) = index := by omega
    simp [inside, low, high, adjust,
      BitVec.getLsbD_of_ge value index (by omega)]

theorem replaceLow8_widths (old : Word) (value : Byte) :
    (replaceLow8 old value).setWidth 8 = value ∧
    (replaceLow8 old value).extractLsb' 8 56 = old.extractLsb' 8 56 := by
  rw [replaceLow8_eq_append]
  exact ⟨BitVec.setWidth_append_eq_right, BitVec.extractLsb'_append_eq_left⟩

/-- Every destination bit, including out-of-width queries. -/
theorem replaceLow8_bits (old : Word) (value : Byte) (index : Nat) :
    (replaceLow8 old value).getLsbD index =
      if index < 8 then value.getLsbD index else old.getLsbD index := by
  rw [replaceLow8_eq_append, BitVec.getLsbD_append]
  split
  · rfl
  · rename_i high
    simp only [BitVec.getLsbD_extractLsb']
    by_cases inside : index < 64
    · simp [show index - 8 < 56 by omega, show 8 + (index - 8) = index by omega]
    · simp [show ¬ index - 8 < 56 by omega, BitVec.getLsbD_of_ge old index (by omega)]

/-- Complete local effect. Memory equality includes read, execute and write
maps. No restriction on destination (including RSP) or incoming flags occurs. -/
structure Low8Context (before after : State) (destination : Register)
    (value : Byte) (length : Nat) : Prop where
  word : after.registers destination = (before.registers destination).extractLsb' 8 56 ++ value
  low8 : (after.registers destination).setWidth 8 = value
  upper56 : (after.registers destination).extractLsb' 8 56 =
    (before.registers destination).extractLsb' 8 56
  bits : ∀ index, (after.registers destination).getLsbD index =
    if index < 8 then value.getLsbD index else (before.registers destination).getLsbD index
  other : ∀ register, register ≠ destination → after.registers register = before.registers register
  memory : after.memory = before.memory
  flags : after.flags = before.flags
  rip : after.rip = before.rip + BitVec.ofNat 64 length

private theorem low8Context (before : State) (destination : Register) (value : Byte)
    (length : Nat) :
    Low8Context before { before.writeRegister destination
      (replaceLow8 (before.registers destination) value) with
      rip := before.rip + BitVec.ofNat 64 length } destination value length := by
  constructor
  · simpa [State.writeRegister] using replaceLow8_eq_append (before.registers destination) value
  · simpa [State.writeRegister] using (replaceLow8_widths (before.registers destination) value).1
  · simpa [State.writeRegister] using (replaceLow8_widths (before.registers destination) value).2
  · intro index
    simpa [State.writeRegister] using replaceLow8_bits (before.registers destination) value index
  · intro register other
    simp [State.writeRegister, other]
  · rfl
  · rfl
  · rfl

theorem execute_setcc (before : State) (condition : Condition) (destination : Register)
    (prefixed af : Bool) :
    execute before (.setcc condition destination prefixed) af =
      .ok ⟨.next { before.writeRegister destination
        (replaceLow8 (before.registers destination) (if condition.holds before.flags then 1 else 0))
        with rip := before.rip + BitVec.ofNat 64 (if prefixed then 4 else 3) }, []⟩ := rfl

theorem execute_movImm8 (before : State) (destination : Register) (value : Byte)
    (prefixed af : Bool) :
    execute before (.movImm8 destination value prefixed) af =
      .ok ⟨.next { before.writeRegister destination (replaceLow8 (before.registers destination) value)
        with rip := before.rip + BitVec.ofNat 64 (if prefixed then 3 else 2) }, []⟩ := rfl

/-- One common result for both AF choices; the condition uses PRESTATE flags. -/
theorem execute_setcc_context (before : State) (condition : Condition)
    (destination : Register) (prefixed : Bool) :
    ∃ after, (∀ af, execute before (.setcc condition destination prefixed) af =
      .ok ⟨.next after, []⟩) ∧
      Low8Context before after destination (if condition.holds before.flags then 1 else 0)
        (if prefixed then 4 else 3) :=
  ⟨_, fun _ => rfl, low8Context ..⟩

theorem execute_movImm8_context (before : State) (destination : Register) (value : Byte)
    (prefixed : Bool) :
    ∃ after, (∀ af, execute before (.movImm8 destination value prefixed) af =
      .ok ⟨.next after, []⟩) ∧ Low8Context before after destination value (if prefixed then 3 else 2) :=
  ⟨_, fun _ => rfl, low8Context ..⟩

theorem execute_setcc_choice_independent (before : State) (condition : Condition)
    (destination : Register) (prefixed left right : Bool) :
    execute before (.setcc condition destination prefixed) left =
      execute before (.setcc condition destination prefixed) right := rfl

theorem execute_movImm8_choice_independent (before : State) (destination : Register)
    (value : Byte) (prefixed left right : Bool) :
    execute before (.movImm8 destination value prefixed) left =
      execute before (.movImm8 destination value prefixed) right := rfl

/-- Exact Boolean range and truth direction, independent of dirty upper bits. -/
theorem execute_setcc_result {before after : State} {condition : Condition}
    {destination : Register} {prefixed af : Bool} {reads : List Read}
    (actual : execute before (.setcc condition destination prefixed) af = .ok ⟨.next after, reads⟩) :
    reads = [] ∧ (after.registers destination).setWidth 8 =
      (if condition.holds before.flags then 1 else 0) ∧
    ((after.registers destination).setWidth 8 = 1 ↔ condition.holds before.flags = true) ∧
    ((after.registers destination).setWidth 8 = 0 ∨ (after.registers destination).setWidth 8 = 1) := by
  obtain ⟨final, executed, context⟩ := execute_setcc_context before condition destination prefixed
  rw [executed af] at actual
  cases actual
  refine ⟨rfl, context.low8, ?_, ?_⟩ <;> rw [context.low8] <;>
    cases condition.holds before.flags <;> simp

end EDSL.X86.Sequential

namespace EDSL.OS.CallResources
open X86 X86.Sequential

/-- Same complete current world and original caller resources. A destination
RSP creates no permission to read from its new value; RET still needs its own
current-slot and policy obligations. No ABI preservation is inferred. -/
theorem current_setcc_step {call : Call} {shared : Shared} {before : State}
    {condition : Condition} {destination : Register} {prefixed : Bool}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.setcc condition destination prefixed)) :
    ∃ after, (∀ af, step af before = .ok ⟨.next after, []⟩) ∧ Current call shared after ∧
      Low8Context before after destination (if condition.holds before.flags then 1 else 0)
        (if prefixed then 4 else 3) := by
  obtain ⟨after, executed, context⟩ := execute_setcc_context before condition destination prefixed
  exact ⟨after, fun af => (step_eq_execute af decoded).trans (executed af),
    current.sameMemory context.memory, context⟩

theorem current_movImm8_step {call : Call} {shared : Shared} {before : State}
    {destination : Register} {value : Byte} {prefixed : Bool}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.movImm8 destination value prefixed)) :
    ∃ after, (∀ af, step af before = .ok ⟨.next after, []⟩) ∧ Current call shared after ∧
      Low8Context before after destination value (if prefixed then 3 else 2) := by
  obtain ⟨after, executed, context⟩ := execute_movImm8_context before destination value prefixed
  exact ⟨after, fun af => (step_eq_execute af decoded).trans (executed af),
    current.sameMemory context.memory, context⟩

end EDSL.OS.CallResources

namespace EDSL.X86.CallReturn

theorem execute_setcc (before : State) (condition : Sequential.Condition)
    (destination : Register) (prefixed af : Bool) :
    execute before (liftSequential (.setcc condition destination prefixed)) af =
      Sequential.execute before (.setcc condition destination prefixed) af := execute_liftSequential ..

theorem execute_movImm8 (before : State) (destination : Register) (value : Byte)
    (prefixed af : Bool) :
    execute before (liftSequential (.movImm8 destination value prefixed)) af =
      Sequential.execute before (.movImm8 destination value prefixed) af := execute_liftSequential ..

end EDSL.X86.CallReturn

namespace EDSL.X86.VCGen
open Sequential

/-- The ordinary production WP needs only the actual fallthrough continuation. -/
theorem wp_setcc_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (before : State) (Post : Contract) (condition : Condition) (destination : Register)
    (prefixed : Bool) (instruction : (graph.node node).instruction = .setcc condition destination prefixed) :
    let after := { before.writeRegister destination
      (replaceLow8 (before.registers destination) (if condition.holds before.flags then 1 else 0)) with
      rip := before.rip + BitVec.ofNat 64 (if prefixed then 4 else 3) }
    wp graph base AllowedRead (fuel + 1) node before Post ↔
      ∃ next : graph.Index,
        after.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        wp graph base AllowedRead fuel next after (fun result => Post (result.prepend 1 [])) := by
  apply wp_pure_next_iff
  intro af
  rw [instruction, Sequential.execute_setcc]

theorem wp_movImm8_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (before : State) (Post : Contract) (destination : Register) (value : Byte)
    (prefixed : Bool) (instruction : (graph.node node).instruction = .movImm8 destination value prefixed) :
    let after := { before.writeRegister destination (replaceLow8 (before.registers destination) value) with
      rip := before.rip + BitVec.ofNat 64 (if prefixed then 3 else 2) }
    wp graph base AllowedRead (fuel + 1) node before Post ↔
      ∃ next : graph.Index,
        after.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        wp graph base AllowedRead fuel next after (fun result => Post (result.prepend 1 [])) := by
  apply wp_pure_next_iff
  intro af
  rw [instruction, Sequential.execute_movImm8]

end EDSL.X86.VCGen

namespace EDSL.X86.VCGen.Cutpoints
open Sequential

theorem wp_setcc_iff (graph : CFG.Graph) (base : Word) (Post : State → Prop)
    (AllowedRead : State → Read → Prop) (Inv : graph.Index → State → Prop)
    (rank : graph.Index → State → Nat) (budget fuel : Nat) (node : graph.Index)
    (before : State) (condition : Condition) (destination : Register) (prefixed : Bool)
    (instruction : (graph.node node).instruction = .setcc condition destination prefixed) :
    let after := { before.writeRegister destination
      (replaceLow8 (before.registers destination) (if condition.holds before.flags then 1 else 0)) with
      rip := before.rip + BitVec.ofNat 64 (if prefixed then 4 else 3) }
    wp graph base Post AllowedRead Inv rank budget (fuel + 1) node before ↔
      ∃ next : graph.Index,
        after.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        if graph.cutpoint next then Inv next after ∧ rank next after < budget
        else wp graph base Post AllowedRead Inv rank budget fuel next after := by
  apply wp_pure_next_iff
  intro af
  rw [instruction, Sequential.execute_setcc]

theorem wp_movImm8_iff (graph : CFG.Graph) (base : Word) (Post : State → Prop)
    (AllowedRead : State → Read → Prop) (Inv : graph.Index → State → Prop)
    (rank : graph.Index → State → Nat) (budget fuel : Nat) (node : graph.Index)
    (before : State) (destination : Register) (value : Byte) (prefixed : Bool)
    (instruction : (graph.node node).instruction = .movImm8 destination value prefixed) :
    let after := { before.writeRegister destination (replaceLow8 (before.registers destination) value) with
      rip := before.rip + BitVec.ofNat 64 (if prefixed then 3 else 2) }
    wp graph base Post AllowedRead Inv rank budget (fuel + 1) node before ↔
      ∃ next : graph.Index,
        after.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        if graph.cutpoint next then Inv next after ∧ rank next after < budget
        else wp graph base Post AllowedRead Inv rank budget fuel next after := by
  apply wp_pure_next_iff
  intro af
  rw [instruction, Sequential.execute_movImm8]

end EDSL.X86.VCGen.Cutpoints
