/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Execution

namespace EDSL.Examples.Compiler.Increment
open X86

/-- Exact optimized output observed from Clang 18 and GCC 13 for uint32 increment. -/
def bytes : List Byte := [0x8d, 0x47, 0x01, 0xc3]

/-- Independent mathematical contract: unsigned 32-bit modular increment. -/
def specification (input : BitVec 32) : BitVec 32 := input + 1

theorem lea_matches_specification (input : Word) :
    (((input + 1).setWidth 32).setWidth 64) =
      (specification (input.setWidth 32)).setWidth 64 := by
  unfold specification
  bv_decide

def finalState (initial : State) (returnAddress : Word) : State :=
  { initial with
    registers := fun register =>
      if register = .rsp then initial.registers .rsp + 8
      else if register = .rax then
        (specification ((initial.registers .rdi).setWidth 32)).setWidth 64
      else initial.registers register
    rip := returnAddress }

/-- All admitted register values, flags, memory states and return targets.
The theorem includes code-fetch binding, stack read, state framing and exact cost. -/
theorem actual_bytes_correct (initial : State) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip bytes)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    run 2 initial = .ok ⟨finalState initial returnAddress, 2⟩ := by
  have b0 := code.2 0 0x8d (by decide)
  have b1 := code.2 1 0x47 (by decide)
  have b2 := code.2 2 0x01 (by decide)
  have b3 := code.2 3 0xc3 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0
  simp only [BitVec.ofNat_eq_ofNat] at b1 b2 b3
  simp [run, step, decodeAt, b0, b1, b2, b3, executeLea, executeRet,
    State.writeRegister, stack, returnValid, finalState,
    Bind.bind, Pure.pure, Except.bind, Except.pure]
  funext register
  cases register <;> simp
  exact lea_matches_specification (initial.registers .rdi)

/-- A concrete mapped code/stack witness; the entry conditions are satisfiable. -/
def witnessMemory : Memory where
  read address :=
    match address.toNat with
    | 4096 => some 0x8d
    | 4097 => some 0x47
    | 4098 => some 0x01
    | 4099 => some 0xc3
    | 32768 => some 0x00
    | 32769 => some 0x20
    | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some 0x00
    | _ => none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4100)

def witnessEntry (input : Word) : State where
  registers register := if register = .rdi then input
    else if register = .rsp then 32768 else 0
  rip := 4096
  flags := 0x202
  memory := witnessMemory

theorem witness_code : CodeAt witnessMemory 4096 bytes := by
  refine ⟨by decide, ?_⟩
  intro offset byte atOffset
  match offset with
  | 0 | 1 | 2 | 3 =>
    simp [bytes] at atOffset
    subst byte
    rfl
  | n + 4 => simp [bytes] at atOffset

theorem witness_stack : readWord witnessMemory 32768 = .ok 8192 := by rfl

theorem every_input_has_an_execution (input : Word) :
    run 2 (witnessEntry input) = .ok ⟨finalState (witnessEntry input) 8192, 2⟩ := by
  apply actual_bytes_correct
  · exact witness_code
  · exact witness_stack
  · decide

theorem terminates_and_all_results_match (initial : State) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip bytes)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes initial (finalState initial returnAddress) 2 ∧
    ¬ Diverges initial ∧
    ∀ final count, Executes initial final count →
      final = finalState initial returnAddress ∧ count = 2 := by
  have execution := run_sound (actual_bytes_correct initial returnAddress code stack returnValid)
  exact ⟨execution, execution.no_divergence, fun _ _ other => other.deterministic execution⟩

/-- Any implementation in the supported machine model needs two instructions
on a zero-input, zero-RAX entry to satisfy the increment contract. The certified
fixture attains this bound; this is not an all-x86 or cycle optimality claim. -/
theorem zero_input_lower_bound {initial final : State} {count : Nat}
    (execution : Executes initial final count)
    (initialRax : initial.registers .rax = 0)
    (inputZero : (initial.registers .rdi).setWidth 32 = 0)
    (correct : final.registers .rax =
      (specification ((initial.registers .rdi).setWidth 32)).setWidth 64) :
    2 ≤ count := by
  apply execution.changing_rax_costs_two
  rw [initialRax, correct, inputZero]
  decide

end EDSL.Examples.Compiler.Increment
