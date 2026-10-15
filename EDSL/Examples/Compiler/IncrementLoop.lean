/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.ControlFlow

namespace EDSL.Examples.Compiler.IncrementLoop
open X86

def bytes : List Byte := [0x89, 0xf8, 0xe3, 5, 0x8d, 0x40, 1, 0xe2, 0xfb, 0xc3]

/-- Independent modular arithmetic contract. RCX is the iteration input. -/
def specification (value : BitVec 32) (count : Nat) : BitVec 32 := value + BitVec.ofNat 32 count

def cost (count : Nat) : Nat := 2 * count + 3

/-- Loop invariant state: remaining iterations decrease in natural arithmetic;
the accumulator remains a zero-extended 32-bit value. -/
def invariantState (initial : State) (accumulator : BitVec 32) (remaining : Nat) : State :=
  { initial with
    registers := fun register => if register = .rax then accumulator.setWidth 64
      else if register = .rcx then BitVec.ofNat 64 remaining else initial.registers register
    rip := initial.rip + (if remaining = 0 then 9 else 4) }

def finalState (initial : State) (returnAddress : Word) : State :=
  { initial with
    registers := fun register => if register = .rax then
      (specification ((initial.registers .rdi).setWidth 32) (initial.registers .rcx).toNat).setWidth 64
      else if register = .rcx then 0
      else if register = .rsp then initial.registers .rsp + 8 else initial.registers register
    rip := returnAddress }

def finish (initial : State) (accumulator : BitVec 32) (returnAddress : Word) : State :=
  { initial with
    registers := fun register => if register = .rax then accumulator.setWidth 64
      else if register = .rcx then 0
      else if register = .rsp then initial.registers .rsp + 8 else initial.registers register
    rip := returnAddress }

theorem increment_accumulator (value : BitVec 32) :
    ((value.setWidth 64 + 1).setWidth 32) = value + 1 := by
  rw [BitVec.setWidth_add _ _ (by decide)]
  simp

theorem body_step (initial : State) (accumulator : BitVec 32) (remaining : Nat)
    (code : CodeAt initial.memory initial.rip bytes) :
    step (invariantState initial accumulator (remaining + 1)) =
      .ok (.next (executeLeaRax (invariantState initial accumulator (remaining + 1)) 1)) := by
  have b4 := code.2 4 0x8d (by decide)
  have b5 := code.2 5 0x40 (by decide)
  have b6 := code.2 6 1 (by decide)
  simp [step, decodeAt, invariantState, b4, b5, b6, BitVec.add_assoc]

theorem backedge (initial : State) (accumulator : BitVec 32) (remaining : Nat)
    (bound : remaining + 1 < 2^64) (code : CodeAt initial.memory initial.rip bytes) :
    step (executeLeaRax (invariantState initial accumulator (remaining + 1)) 1) =
      .ok (.next (invariantState initial (accumulator + 1) remaining)) := by
  have b4 := code.2 4 0x8d (by decide)
  have b7 := code.2 7 0xe2 (by decide)
  have b8 := code.2 8 0xfb (by decide)
  have canonicalHead := fetch_canonical b4
  have countZero : BitVec.ofNat 64 remaining = 0 ↔ remaining = 0 := by
    constructor
    · intro zero
      have same := congrArg BitVec.toNat zero
      simpa [Nat.mod_eq_of_lt (show remaining < 2^64 by omega)] using same
    · intro zero; subst remaining; rfl
  simp only [BitVec.ofNat_eq_ofNat] at b4 b7 b8 canonicalHead
  simp [step, decodeAt, invariantState, executeLeaRax, executeLoop, State.writeRegister,
    executeShortBranch, BitVec.add_assoc, b7, b8, BitVec.ofNat_add,
    canonicalHead, BitVec.add_sub_cancel]
  all_goals
    split <;> simp_all
    all_goals
      funext register
      cases register <;> first
        | rfl
        | exact congrArg (BitVec.setWidth 64) (increment_accumulator accumulator)

theorem return_step (initial : State) (accumulator : BitVec 32) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip bytes)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    step (invariantState initial accumulator 0) =
      .ok (.returned (finish initial accumulator returnAddress)) := by
  have b9 := code.2 9 0xc3 (by decide)
  simp [step, decodeAt, invariantState, b9, executeRet, stack, returnValid,
    finish, State.writeRegister]
  funext register
  cases register <;> rfl

/-- Induction on the natural remaining counter proves a loop invariant and
termination for every admitted 64-bit count, without execution unrolling. -/
theorem loop_executes (initial : State) (accumulator : BitVec 32) (remaining : Nat)
    (bound : remaining < 2^64) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip bytes)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes (invariantState initial accumulator remaining)
      (finish initial (specification accumulator remaining) returnAddress) (2 * remaining + 1) := by
  induction remaining generalizing accumulator with
  | zero =>
    simpa [specification] using Executes.ret (return_step initial accumulator returnAddress code stack returnValid)
  | succ remaining induction =>
    have tail := induction (accumulator + 1) (by omega)
    have path := Executes.next (body_step initial accumulator remaining code)
      (Executes.next (backedge initial accumulator remaining bound code) tail)
    have value : specification (accumulator + 1) remaining = specification accumulator (remaining + 1) := by
      simp only [specification, BitVec.ofNat_add]
      rw [BitVec.add_assoc, BitVec.add_comm 1 (BitVec.ofNat 32 remaining)]
      rfl
    rw [value] at path
    have costEq : 2 * remaining + 1 + 1 + 1 = 2 * (remaining + 1) + 1 := by omega
    rw [costEq] at path
    exact path

theorem entry_steps (initial : State) (code : CodeAt initial.memory initial.rip bytes) :
    Steps initial (invariantState initial ((initial.registers .rdi).setWidth 32)
      (initial.registers .rcx).toNat) 2 := by
  have b0 := code.2 0 0x89 (by decide)
  have b1 := code.2 1 0xf8 (by decide)
  have b2 := code.2 2 0xe3 (by decide)
  have b3 := code.2 3 5 (by decide)
  have b9 := code.2 9 0xc3 (by decide)
  have canonicalExit := fetch_canonical b9
  have first : step initial = .ok (.next (executeMovEaxEdi initial)) := by
    simp only [BitVec.add_zero] at b0
    simp [step, decodeAt, b0, b1]
  have second : step (executeMovEaxEdi initial) = .ok (.next
      (invariantState initial ((initial.registers .rdi).setWidth 32) (initial.registers .rcx).toNat)) := by
    simp [step, decodeAt, executeMovEaxEdi, executeJrcxz, executeShortBranch,
      State.writeRegister, BitVec.add_assoc, b2, b3, canonicalExit, invariantState]
    split <;> simp_all
    all_goals
      first
        | constructor
          · funext register; cases register <;> rfl
          · intro impossible
            apply ‹initial.registers .rcx ≠ 0›
            exact BitVec.eq_of_toNat_eq impossible
        | funext register; cases register <;> simp_all
  exact Steps.next first (Steps.next second .refl)

theorem actual_bytes_correct (initial : State) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip bytes)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes initial (finalState initial returnAddress) (cost (initial.registers .rcx).toNat) := by
  have loopRun := loop_executes initial ((initial.registers .rdi).setWidth 32)
    (initial.registers .rcx).toNat (initial.registers .rcx).isLt returnAddress code stack returnValid
  have run := loopRun.prepend (entry_steps initial code)
  have costEq : 2 + (2 * (initial.registers .rcx).toNat + 1) = cost (initial.registers .rcx).toNat := by
    unfold cost
    omega
  rw [costEq] at run
  exact run

theorem terminates_and_all_results_match (initial : State) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip bytes)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes initial (finalState initial returnAddress) (cost (initial.registers .rcx).toNat) ∧
    ¬ Diverges initial ∧ ∀ final count, Executes initial final count →
      final = finalState initial returnAddress ∧ count = cost (initial.registers .rcx).toNat := by
  have run := actual_bytes_correct initial returnAddress code stack returnValid
  exact ⟨run, run.no_divergence, fun _ _ other => other.deterministic run⟩

end EDSL.Examples.Compiler.IncrementLoop
