/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Stride32.Annotations
import EDSL.X86.Sequential.CutpointsAccounting

namespace EDSL.Stride32
open X86

theorem inputReads_succ (base : Word) (count : Nat) :
    inputReads base (count + 1) =
      ⟨.data, base, 4⟩ :: inputReads (base + 8) count := by
  simp only [inputReads, List.range_succ_eq_map, List.map_cons, Nat.mul_zero, List.map_map]
  congr 1
  · congr 1
    exact BitVec.add_zero base
  · apply List.map_congr_left
    intro index member
    simp only [Function.comp_apply, Nat.mul_succ, BitVec.ofNat_add]
    congr 1
    change base + (BitVec.ofNat 64 (8 * index) + 8) = (base + 8) + BitVec.ofNat 64 (8 * index)
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * index)) 8]

/-- Exact remaining retired-instruction count at each checked instruction.
The counter is read from the current full-width RSI. -/
def remainingCost (total : Nat) (node : Index) (state : State) : Nat :=
  let count := (state.registers .rsi).toNat
  match node.val with
  | 0 => 6 * total + 4
  | 1 => 6 * count + 3
  | 2 => 6 * count + 2
  | 3 => 6 * count + 1
  | 4 => 6 * count
  | 5 => 6 * count + 5
  | 6 => 6 * count + 4
  | _ => 1

/-- The remaining ordered operand reads, expressed using current machine
registers. After ADD, the current element has already been read; after DEC,
the current pointer still needs its eight-byte advance. -/
def remainingReads (node : Index) (state : State) : List Sequential.Read :=
  let count := (state.registers .rsi).toNat
  let base := state.registers .rdi
  let stack : List Sequential.Read := [⟨.stack, state.registers .rsp, 8⟩]
  match node.val with
  | 4 => inputReads (base + 8) (count - 1) ++ stack
  | 5 => inputReads (base + 8) count ++ stack
  | 7 => stack
  | _ => inputReads base count ++ stack

private theorem Phase.actual {initial state : State} {values : List (BitVec 32)}
    {total : Nat} {target : Word} (pre : Pre bytes initial values total target)
    {source node : Index} {budget : Nat}
    (inside : Phase initial values total target source budget node state) (af : Bool) :
    Sequential.step af state =
      Sequential.execute state (graph.node node).instruction af := by
  have code : CodeAt state.memory initial.rip bytes := by rw [inside.memory]; exact pre.code
  exact valid.step_eq_execute code node state rfl inside.pc af

private theorem decrement_counter {initial state : State} {values : List (BitVec 32)}
    {total : Nat} (header : Header initial values total state) (pair : Pair header)
    (af : Bool) :
    ((decrement (load (body initial.rip state af) pair.first)).registers .rsi).toNat = pair.rest := by
  simp only [decrement, load, body, atPC, test, edit, State.writeRegister,
    reduceCtorEq, ite_true, ite_false]
  rw [header.counter, pair.count, BitVec.ofNat_add]
  change ((BitVec.ofNat 64 pair.rest + (1 : Word)) - 1).toNat = pair.rest
  rw [BitVec.add_sub_cancel]
  have bound : pair.rest < 2^64 := by have bound := header.countBound; rw [pair.count] at bound; omega
  exact Nat.mod_eq_of_lt bound

@[simp] private theorem clear_rsi (state : State) (af : Bool) :
    (clear state af).registers .rsi = state.registers .rsi := rfl
@[simp] private theorem clear_rdi (state : State) (af : Bool) :
    (clear state af).registers .rdi = state.registers .rdi := rfl
@[simp] private theorem clear_rsp (state : State) (af : Bool) :
    (clear state af).registers .rsp = state.registers .rsp := rfl
@[simp] private theorem test_registers (state : State) (af : Bool) (register : Register) :
    (test state af).registers register = state.registers register := rfl
@[simp] private theorem body_registers (base : Word) (state : State) (af : Bool) (register : Register) :
    (body base state af).registers register = state.registers register := rfl
@[simp] private theorem load_rsi (state : State) (value : BitVec 32) :
    (load state value).registers .rsi = state.registers .rsi := rfl
@[simp] private theorem load_rdi (state : State) (value : BitVec 32) :
    (load state value).registers .rdi = state.registers .rdi := rfl
@[simp] private theorem load_rsp (state : State) (value : BitVec 32) :
    (load state value).registers .rsp = state.registers .rsp := rfl
@[simp] private theorem decrement_rdi (state : State) :
    (decrement state).registers .rdi = state.registers .rdi := rfl
@[simp] private theorem decrement_rsp (state : State) :
    (decrement state).registers .rsp = state.registers .rsp := rfl
@[simp] private theorem advance_rsi (state : State) :
    (advance state).registers .rsi = state.registers .rsi := rfl
@[simp] private theorem advance_rdi (state : State) :
    (advance state).registers .rdi = state.registers .rdi + 8 := rfl
@[simp] private theorem advance_rsp (state : State) :
    (advance state).registers .rsp = state.registers .rsp := rfl
@[simp] private theorem cycle_registers (base : Word) (state : State) (af : Bool)
    (value : BitVec 32) (register : Register) :
    (cycleState base state af value).registers register =
      (advance (decrement (load (body base state af) value))).registers register := rfl
@[simp] private theorem exit_registers (base : Word) (state : State) (af : Bool) (register : Register) :
    (exitState base state af).registers register = state.registers register := rfl

/-- Local exact accounting for the actual byte-bound certificate. No successful
future evaluator run is assumed in these obligations. -/
def accounting {initial : State} {values : List (BitVec 32)} {total : Nat} {target : Word}
    (pre : Pre bytes initial values total target) (Access : Sequential.Read → Prop)
    (permission : ∀ read ∈ operandReads initial total, Access read) :
    Sequential.Cutpoints.Accounting ((annotations pre Access permission).certificate valid) where
  cost := remainingCost total
  reads := remainingReads
  localStep source budget node state inside af observation actual := by
    change Phase initial values total target source budget node state at inside
    rw [inside.actual pre af] at actual
    cases inside with
    | entry accepted =>
      change Sequential.execute initial (.xorSelf32 .rax) af = .ok observation at actual
      have effect : Sequential.execute initial (.xorSelf32 .rax) af =
          .ok ⟨.next (clear initial af), []⟩ := rfl
      rw [effect] at actual
      cases actual
      refine ⟨1, ⟨1, total, .header (initialized accepted af)⟩, ?_, ?_⟩
      · change 6 * total + 4 = 1 + (6 * ((clear initial af).registers .rsi).toNat + 3)
        have counter : (initial.registers .rsi).toNat = total := by
          rw [pre.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pre.count_lt]
        simp only [clear_rsi, counter]
        omega
      · change inputReads (initial.registers .rdi) (initial.registers .rsi).toNat ++
          [⟨.stack, initial.registers .rsp, 8⟩] = _
        rfl
    | @header state header =>
      change Sequential.execute state (.test64 .rsi .rsi) af = .ok observation at actual
      rw [Sequential.execute_test64, BitVec.and_self] at actual
      change Except.ok ⟨.next (test state af), []⟩ = .ok observation at actual
      cases actual
      refine ⟨2, ⟨1, header.count, .tested header af⟩, ?_, ?_⟩
      · change 6 * (state.registers .rsi).toNat + 3 =
          1 + (6 * ((test state af).registers .rsi).toNat + 2)
        rw [test_registers]
        omega
      · rfl
    | @tested state header previous =>
      change Sequential.execute (test state previous) (.je 11) af = .ok observation at actual
      by_cases zero : header.count = 0
      · rw [guard_exit pre header zero previous af] at actual
        cases actual
        refine ⟨7, ⟨1, header.count, .exiting header zero previous⟩, ?_, ?_⟩
        · change 6 * ((test state previous).registers .rsi).toNat + 2 = 1 + 1
          simp only [test_registers, header.rank, zero]
        · change inputReads ((test state previous).registers .rdi)
            ((test state previous).registers .rsi).toNat ++
            [⟨.stack, (test state previous).registers .rsp, 8⟩] =
              [] ++ [⟨.stack, (exitState initial.rip state previous).registers .rsp, 8⟩]
          simp only [test_registers, exit_registers, header.rank, zero, inputReads,
            List.range_zero, List.map_nil, List.nil_append]
      · obtain ⟨pair⟩ := header.pair (by omega)
        rw [guard_body header pair previous af] at actual
        cases actual
        refine ⟨3, ⟨1, header.count, .body header pair previous⟩, ?_, ?_⟩
        · change 6 * ((test state previous).registers .rsi).toNat + 2 =
            1 + (6 * ((body initial.rip state previous).registers .rsi).toNat + 1)
          simp only [test_registers, body_registers]
          omega
        · rfl
    | @body state header pair previous =>
      change Sequential.execute (body initial.rip state previous)
        (.addMem32 .rax (.base .rdi)) af = .ok observation at actual
      rw [Sequential.execute_addMem32] at actual
      simp only [Sequential.Address.eval, header_operand header pair previous, ok_bind, pure_ok] at actual
      change Except.ok ⟨.next (load (body initial.rip state previous) pair.first),
        [⟨.data, state.registers .rdi, 4⟩]⟩ = .ok observation at actual
      cases actual
      refine ⟨4, ⟨1, header.count, .loaded header pair previous⟩, ?_, ?_⟩
      · change 6 * ((body initial.rip state previous).registers .rsi).toNat + 1 =
          1 + 6 * ((load (body initial.rip state previous) pair.first).registers .rsi).toNat
        simp only [load_rsi]
        omega
      · change inputReads ((body initial.rip state previous).registers .rdi)
          ((body initial.rip state previous).registers .rsi).toNat ++
          [⟨.stack, (body initial.rip state previous).registers .rsp, 8⟩] =
            [⟨.data, state.registers .rdi, 4⟩] ++
              (inputReads ((load (body initial.rip state previous) pair.first).registers .rdi + 8)
                (((load (body initial.rip state previous) pair.first).registers .rsi).toNat - 1) ++
                  [⟨.stack, (load (body initial.rip state previous) pair.first).registers .rsp, 8⟩])
        simp only [body_registers, load_rsi, load_rdi, load_rsp, header.rank,
          pair.count, Nat.add_sub_cancel, inputReads_succ, List.cons_append,
          List.nil_append]
    | @loaded state header pair previous =>
      change Sequential.execute (load (body initial.rip state previous) pair.first)
        (.dec64 .rsi) af = .ok observation at actual
      change Except.ok ⟨.next (decrement (load (body initial.rip state previous) pair.first)), []⟩ =
        .ok observation at actual
      cases actual
      refine ⟨5, ⟨1, header.count, .decremented header pair previous⟩, ?_, ?_⟩
      · change 6 * ((load (body initial.rip state previous) pair.first).registers .rsi).toNat =
          1 + (6 * ((decrement (load (body initial.rip state previous) pair.first)).registers .rsi).toNat + 5)
        simp only [load_rsi, body_registers, header.rank, decrement_counter header pair previous]
        have count := pair.count
        omega
      · change inputReads ((load (body initial.rip state previous) pair.first).registers .rdi + 8)
          (((load (body initial.rip state previous) pair.first).registers .rsi).toNat - 1) ++
          [⟨.stack, (load (body initial.rip state previous) pair.first).registers .rsp, 8⟩] =
            [] ++ (inputReads ((decrement (load (body initial.rip state previous) pair.first)).registers .rdi + 8)
              ((decrement (load (body initial.rip state previous) pair.first)).registers .rsi).toNat ++
                [⟨.stack, (decrement (load (body initial.rip state previous) pair.first)).registers .rsp, 8⟩])
        simp only [load_rsi, load_rdi, load_rsp, body_registers, decrement_rdi, decrement_rsp,
          header.rank, decrement_counter header pair previous, pair.count, Nat.add_sub_cancel,
          List.nil_append]
    | @decremented state header pair previous =>
      change Sequential.execute (decrement (load (body initial.rip state previous) pair.first))
        (.addImm64 .rdi 8) af = .ok observation at actual
      change Except.ok ⟨.next (advance (decrement (load (body initial.rip state previous) pair.first))), []⟩ =
        .ok observation at actual
      cases actual
      refine ⟨6, ⟨1, header.count, .advanced header pair previous⟩, ?_, ?_⟩
      · change 6 * ((decrement (load (body initial.rip state previous) pair.first)).registers .rsi).toNat + 5 =
          1 + (6 * ((advance (decrement (load (body initial.rip state previous) pair.first))).registers .rsi).toNat + 4)
        rw [advance_rsi]
        omega
      · rfl
    | @advanced state header pair previous =>
      change Sequential.execute (advance (decrement (load (body initial.rip state previous) pair.first)))
        (.jmp 240) af = .ok observation at actual
      rw [back_edge pre header pair previous af] at actual
      cases actual
      let next := nextHeader header pair previous
      refine ⟨1, ⟨1, pair.rest, .header next⟩, ?_, ?_⟩
      · change 6 * ((advance (decrement (load (body initial.rip state previous) pair.first))).registers .rsi).toNat + 4 =
          1 + (6 * ((cycleState initial.rip state previous pair.first).registers .rsi).toNat + 3)
        rw [cycle_registers]
        omega
      · rfl
    | @exiting state header zero previous =>
      change Sequential.execute (exitState initial.rip state previous) (.legacy .ret) af =
        .ok observation at actual
      rw [zero_return pre header previous af] at actual
      cases actual
      exact ⟨rfl, by change [(⟨.stack, (exitState initial.rip state previous).registers .rsp, 8⟩ : Sequential.Read)] = _
                     rw [exit_registers, header.frame.stack]⟩

@[simp] theorem accounting_initial_cost {initial : State} {values : List (BitVec 32)}
    {total : Nat} {target : Word} (pre : Pre bytes initial values total target)
    (Access : Sequential.Read → Prop) (permission : ∀ read ∈ operandReads initial total, Access read) :
    (accounting pre Access permission).cost 0 initial = 6 * total + 4 := rfl

@[simp] theorem accounting_initial_reads {initial : State} {values : List (BitVec 32)}
    {total : Nat} {target : Word} (pre : Pre bytes initial values total target)
    (Access : Sequential.Read → Prop) (permission : ∀ read ∈ operandReads initial total, Access read) :
    (accounting pre Access permission).reads 0 initial = operandReads initial total := by
  change inputReads (initial.registers .rdi) (initial.registers .rsi).toNat ++ _ = _
  rw [pre.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pre.count_lt]
  rfl

end EDSL.Stride32
