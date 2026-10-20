/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Pair32.Annotations
import EDSL.X86.Sequential.CutpointsAccounting

namespace EDSL.Pair32
open X86

theorem inputReads_succ (base : Word) (count : Nat) :
    inputReads base (count + 1) =
      ⟨.data, base, 4⟩ :: inputReads (base + 4) count := by
  simp only [inputReads, List.range_succ_eq_map, List.map_cons, Nat.mul_zero, List.map_map]
  congr 1
  · congr 1
    exact BitVec.add_zero base
  · apply List.map_congr_left
    intro index member
    simp only [Function.comp_apply, Nat.mul_succ, BitVec.ofNat_add]
    congr 1
    change base + (BitVec.ofNat 64 (4 * index) + 4) = (base + 4) + BitVec.ofNat 64 (4 * index)
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (4 * index)) 4]

/-- Exact remaining retired instructions at each checked node, using the
current full-width counters. The entry count uses the independent list lengths. -/
def remainingCost (lengthA lengthB : Nat) (node : Index) (state : State) : Nat :=
  let a := (state.registers .rsi).toNat
  let b := (state.registers .rcx).toNat
  match node.val with
  | 0 => 6 * (lengthA + lengthB) + 6
  | 1 => 6 * (a + b) + 5
  | 2 => 6 * (a + b) + 4
  | 3 => 6 * (a + b) + 3
  | 4 => 6 * (a + b) + 2
  | 5 => 6 * (a + b) + 7
  | 6 => 6 * (a + b) + 6
  | 7 => 6 * b + 3
  | 8 => 6 * b + 2
  | 9 => 6 * b + 1
  | 10 => 6 * b
  | 11 => 6 * b + 5
  | 12 => 6 * b + 4
  | _ => 1

/-- Ordered remaining A operands, then B operands, then the full return slot.
ADD has consumed the current operand before DEC and the pointer advance. -/
def remainingReads (node : Index) (state : State) : List Sequential.Read :=
  let a := (state.registers .rsi).toNat
  let b := (state.registers .rcx).toNat
  let pa := state.registers .rdi
  let pb := state.registers .rdx
  let stack : List Sequential.Read := [⟨.stack, state.registers .rsp, 8⟩]
  match node.val with
  | 4 => (inputReads (pa + 4) (a - 1) ++ inputReads pb b) ++ stack
  | 5 => (inputReads (pa + 4) a ++ inputReads pb b) ++ stack
  | 7 | 8 | 9 | 12 => inputReads pb b ++ stack
  | 10 => inputReads (pb + 4) (b - 1) ++ stack
  | 11 => inputReads (pb + 4) b ++ stack
  | 13 => stack
  | _ => (inputReads pa a ++ inputReads pb b) ++ stack

private theorem Phase.actual {initial state : State} {valuesA valuesB : List (BitVec 32)}
    {target : Word} (pre : Pre bytes initial valuesA valuesB target)
    {source node : Index} {amount : Nat}
    (inside : Phase initial valuesA valuesB target source amount node state) (af : Bool) :
    Sequential.step af state =
      Sequential.execute state (graph.node node).instruction af := by
  have code : CodeAt state.memory initial.rip bytes := by rw [inside.memory]; exact pre.code
  exact valid.step_eq_execute code node state rfl inside.pc af

private theorem decrement_counter {initial state : State} {valuesA valuesB : List (BitVec 32)}
    {loop : Loop} (header : Header initial valuesA valuesB loop state)
    (element : Element header) (af : Bool) :
    ((decrement loop (load (body loop initial.rip state af) element.first)).registers loop.counter).toNat =
      element.rest := by
  simp only [decrement, load, body, atPC, test, edit, State.writeRegister,
    Loop.counter_ne_rax, ite_true, ite_false]
  rw [header.counter, element.count, BitVec.ofNat_add]
  change ((BitVec.ofNat 64 element.rest + (1 : Word)) - 1).toNat = element.rest
  rw [BitVec.add_sub_cancel]
  have bound : element.rest < 2^64 := by
    have bound := header.countBound
    rw [element.count] at bound
    omega
  exact Nat.mod_eq_of_lt bound

@[simp] private theorem test_registers (loop : Loop) (state : State) (af : Bool) (register : Register) :
    (test loop state af).registers register = state.registers register := rfl
@[simp] private theorem body_registers (loop : Loop) (base : Word) (state : State) (af : Bool)
    (register : Register) :
    (body loop base state af).registers register = state.registers register := rfl
@[simp] private theorem load_registers (state : State) (value : BitVec 32) (register : Register)
    (different : register ≠ .rax) :
    (load state value).registers register = state.registers register := by
  simp only [load, edit, State.writeRegister, different, ite_false]
@[simp] private theorem decrement_rdi (loop : Loop) (state : State) :
    (decrement loop state).registers .rdi = state.registers .rdi := by cases loop <;> rfl
@[simp] private theorem decrement_rdx (loop : Loop) (state : State) :
    (decrement loop state).registers .rdx = state.registers .rdx := by cases loop <;> rfl
@[simp] private theorem decrement_rsp (loop : Loop) (state : State) :
    (decrement loop state).registers .rsp = state.registers .rsp := by cases loop <;> rfl
@[simp] private theorem decrement_first_rcx (state : State) :
    (decrement .first state).registers .rcx = state.registers .rcx := rfl
@[simp] private theorem advance_rsi (loop : Loop) (state : State) :
    (advance loop state).registers .rsi = state.registers .rsi := by cases loop <;> rfl
@[simp] private theorem advance_rcx (loop : Loop) (state : State) :
    (advance loop state).registers .rcx = state.registers .rcx := by cases loop <;> rfl
@[simp] private theorem cycle_registers (loop : Loop) (base : Word) (state : State) (af : Bool)
    (value : BitVec 32) (register : Register) :
    (cycleState loop base state af value).registers register =
      (advance loop (decrement loop (load (body loop base state af) value))).registers register := rfl
@[simp] private theorem exit_registers (loop : Loop) (base : Word) (state : State) (af : Bool)
    (register : Register) :
    (exitState loop base state af).registers register = state.registers register := rfl

/-- Exact local accounting for actual byte-bound steps. The certificate supplies
constructive totality separately; these obligations assume no future run. -/
def accounting {initial : State} {valuesA valuesB : List (BitVec 32)} {target : Word}
    (pre : Pre bytes initial valuesA valuesB target) (Access : Sequential.Read → Prop)
    (permission : ∀ read ∈ operandReads initial valuesA valuesB, Access read) :
    Sequential.Cutpoints.Accounting ((annotations pre Access permission).certificate valid) where
  cost := remainingCost valuesA.length valuesB.length
  reads := remainingReads
  localStep source amount node state inside af observation actual := by
    change Phase initial valuesA valuesB target source amount node state at inside
    rw [inside.actual pre af] at actual
    cases inside with
    | entry accepted =>
      change Sequential.execute initial (.xorSelf32 .rax) af = .ok observation at actual
      have effect : Sequential.execute initial (.xorSelf32 .rax) af =
          .ok ⟨.next (clear initial af), []⟩ := rfl
      rw [effect] at actual
      cases actual
      refine ⟨headerIndex .first, ⟨_, _, .header (initialized accepted af)⟩, ?_, ?_⟩
      · change 6 * (valuesA.length + valuesB.length) + 6 =
          1 + (6 * ((initial.registers .rsi).toNat + (initial.registers .rcx).toNat) + 5)
        rw [pre.countA, pre.countB, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt pre.countA_lt, Nat.mod_eq_of_lt pre.countB_lt]
        omega
      · rfl
    | @header loop state header =>
      rw [header_instruction, Sequential.execute_test64, BitVec.and_self] at actual
      change Except.ok ⟨.next (test loop state af), []⟩ = .ok observation at actual
      cases actual
      refine ⟨testedIndex loop, ⟨_, _, .tested header af⟩, ?_, ?_⟩
      · cases loop <;>
          simp only [remainingCost, headerIndex, testedIndex, test_registers] <;> omega
      · cases loop <;> rfl
    | @tested loop state header previous =>
      rw [tested_instruction] at actual
      by_cases zero : header.count = 0
      · rw [guard_exit pre header zero previous af] at actual
        cases actual
        cases loop with
        | first =>
          let next := switchHeader pre header zero previous
          refine ⟨headerIndex .second, ⟨_, _, .header next⟩, ?_, ?_⟩
          · change 6 * ((state.registers .rsi).toNat + (state.registers .rcx).toNat) + 4 =
              1 + (6 * (state.registers .rcx).toNat + 3)
            have count := header.rank
            change (state.registers .rsi).toNat = header.count at count
            rw [count, zero]
            omega
          · change (inputReads (state.registers .rdi) (state.registers .rsi).toNat ++
                inputReads (state.registers .rdx) (state.registers .rcx).toNat) ++
                [⟨.stack, state.registers .rsp, 8⟩] =
              [] ++ (inputReads (state.registers .rdx) (state.registers .rcx).toNat ++
                [⟨.stack, state.registers .rsp, 8⟩])
            have count := header.rank
            change (state.registers .rsi).toNat = header.count at count
            simp only [count, zero, inputReads, List.range_zero, List.map_nil, List.nil_append]
        | second =>
          refine ⟨⟨13, by decide⟩, ⟨_, _, .returning header zero previous⟩, ?_, ?_⟩
          · change 6 * (state.registers .rcx).toNat + 2 = 1 + 1
            have count := header.rank
            change (state.registers .rcx).toNat = header.count at count
            rw [count, zero]
          · change inputReads (state.registers .rdx) (state.registers .rcx).toNat ++
                [⟨.stack, state.registers .rsp, 8⟩] =
              [] ++ [⟨.stack, state.registers .rsp, 8⟩]
            have count := header.rank
            change (state.registers .rcx).toNat = header.count at count
            simp only [count, zero, inputReads, List.range_zero, List.map_nil, List.nil_append]
      · obtain ⟨element⟩ := header.element (by omega)
        rw [guard_body header element previous af] at actual
        cases actual
        refine ⟨bodyIndex loop, ⟨_, _, .body header element previous⟩, ?_, ?_⟩
        · cases loop <;>
            simp only [remainingCost, testedIndex, bodyIndex, test_registers, body_registers] <;> omega
        · cases loop <;> rfl
    | @body loop state header element previous =>
      rw [body_instruction, Sequential.execute_addMem32] at actual
      simp only [Sequential.Address.eval, header_operand header element previous, ok_bind, pure_ok] at actual
      change Except.ok ⟨.next (load (body loop initial.rip state previous) element.first),
        [⟨.data, state.registers loop.pointer, 4⟩]⟩ = .ok observation at actual
      cases actual
      refine ⟨loadedIndex loop, ⟨_, _, .loaded header element previous⟩, ?_, ?_⟩
      · cases loop <;>
          simp only [remainingCost, bodyIndex, loadedIndex, load_registers, ne_eq, reduceCtorEq,
            not_false_eq_true] <;> omega
      · have count := header.rank
        cases loop <;>
          simp only [Loop.counter] at count <;>
          simp only [remainingReads, bodyIndex, loadedIndex, Loop.pointer, body_registers,
            load_registers, ne_eq, reduceCtorEq, not_false_eq_true, count, element.count,
            Nat.add_sub_cancel, inputReads_succ, List.cons_append, List.nil_append]
    | @loaded loop state header element previous =>
      rw [loaded_instruction] at actual
      change Except.ok ⟨.next (decrement loop (load (body loop initial.rip state previous) element.first)), []⟩ =
        .ok observation at actual
      cases actual
      refine ⟨decrementedIndex loop, ⟨_, _, .decremented header element previous⟩, ?_, ?_⟩
      · have count := header.rank
        have decreased := decrement_counter header element previous
        have successor := element.count
        cases loop <;>
          simp only [Loop.counter] at count decreased <;>
          simp only [remainingCost, loadedIndex, decrementedIndex,
            load_registers, body_registers, decrement_first_rcx, ne_eq, reduceCtorEq,
            not_false_eq_true, count, decreased] <;> omega
      · have count := header.rank
        have decreased := decrement_counter header element previous
        cases loop <;>
          simp only [Loop.counter] at count decreased <;>
          simp only [remainingReads, loadedIndex, decrementedIndex,
            load_registers, body_registers, decrement_rdi, decrement_rdx, decrement_rsp,
            decrement_first_rcx, ne_eq, reduceCtorEq,
            not_false_eq_true, count, decreased, element.count, Nat.add_sub_cancel,
            List.nil_append]
    | @decremented loop state header element previous =>
      rw [decremented_instruction] at actual
      change Except.ok ⟨.next (advance loop (decrement loop (load (body loop initial.rip state previous) element.first))), []⟩ =
        .ok observation at actual
      cases actual
      refine ⟨advancedIndex loop, ⟨_, _, .advanced header element previous⟩, ?_, ?_⟩
      · cases loop <;>
          simp only [remainingCost, decrementedIndex, advancedIndex, advance_rsi, advance_rcx] <;> omega
      · cases loop <;> rfl
    | @advanced loop state header element previous =>
      rw [advanced_instruction, back_edge pre header element previous af] at actual
      cases actual
      let next := nextHeader header element previous
      refine ⟨headerIndex loop, ⟨_, _, .header next⟩, ?_, ?_⟩
      · cases loop <;>
          simp only [remainingCost, advancedIndex, headerIndex, cycle_registers] <;> omega
      · cases loop <;> rfl
    | @returning state header zero previous =>
      change Sequential.execute (exitState .second initial.rip state previous) (.legacy .ret) af =
        .ok observation at actual
      rw [zero_return pre header previous af] at actual
      cases actual
      exact ⟨rfl, by
        change [(⟨.stack, (exitState .second initial.rip state previous).registers .rsp, 8⟩ : Sequential.Read)] = _
        rw [exit_registers, header.frame.stack]⟩

@[simp] theorem accounting_initial_cost {initial : State} {valuesA valuesB : List (BitVec 32)}
    {target : Word} (pre : Pre bytes initial valuesA valuesB target) (Access : Sequential.Read → Prop)
    (permission : ∀ read ∈ operandReads initial valuesA valuesB, Access read) :
    (accounting pre Access permission).cost 0 initial = 6 * (valuesA.length + valuesB.length) + 6 := rfl

@[simp] theorem accounting_initial_reads {initial : State} {valuesA valuesB : List (BitVec 32)}
    {target : Word} (pre : Pre bytes initial valuesA valuesB target) (Access : Sequential.Read → Prop)
    (permission : ∀ read ∈ operandReads initial valuesA valuesB, Access read) :
    (accounting pre Access permission).reads 0 initial = operandReads initial valuesA valuesB := by
  change (inputReads (initial.registers .rdi) (initial.registers .rsi).toNat ++
      inputReads (initial.registers .rdx) (initial.registers .rcx).toNat) ++ _ = _
  rw [pre.countA, pre.countB, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt pre.countA_lt, Nat.mod_eq_of_lt pre.countB_lt]
  rfl

end EDSL.Pair32
