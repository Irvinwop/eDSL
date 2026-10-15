/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Compiler.Increment
import EDSL.Examples.Compiler.IncrementLoop
import EDSL.Examples.Compiler.MemoryOps

namespace EDSL.Certificate
open X86 Examples.Compiler

inductive Profile where
  | increment | incrementLoop | load32 | store32
  deriving DecidableEq, Repr

def Profile.name : Profile → String
  | .increment => "increment"
  | .incrementLoop => "increment-loop"
  | .load32 => "load32"
  | .store32 => "store32"

def Profile.parse : String → Option Profile
  | "increment" => some .increment
  | "increment-loop" => some .incrementLoop
  | "load32" => some .load32
  | "store32" => some .store32
  | _ => none

def Profile.bytes : Profile → List Byte
  | .increment => Increment.bytes
  | .incrementLoop => IncrementLoop.bytes
  | .load32 => MemoryOps.loadBytes
  | .store32 => MemoryOps.storeBytes

def accepts (profile : Profile) (candidate : List Byte) : Bool :=
  decide (candidate = profile.bytes)

/-- First deliberately narrow contract profile. Other encodings are unsupported,
not automatically incorrect. Soundness below is about machine execution. -/
def acceptsIncrement (candidate : List Byte) : Bool :=
  accepts .increment candidate

theorem increment_sound (candidate : List Byte)
    (accepted : acceptsIncrement candidate = true)
    (initial : State) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip candidate)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes initial (Increment.finalState initial returnAddress) 2 ∧
    ¬ Diverges initial ∧
    ∀ final count, Executes initial final count →
      final = Increment.finalState initial returnAddress ∧ count = 2 := by
  have equal : candidate = Increment.bytes := of_decide_eq_true accepted
  subst candidate
  exact Increment.terminates_and_all_results_match initial returnAddress code stack returnValid

theorem load32_sound (candidate : List Byte) (accepted : accepts .load32 candidate = true)
    (initial : State) (value : BitVec 32) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip candidate)
    (data : loadDWord initial.memory (initial.registers .rdi) = .ok value)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes initial (MemoryOps.loadFinal initial value returnAddress) 2 ∧
    ¬ Diverges initial ∧
    ∀ final count, Executes initial final count →
      final = MemoryOps.loadFinal initial value returnAddress ∧ count = 2 := by
  have equal : candidate = MemoryOps.loadBytes := of_decide_eq_true accepted
  subst candidate
  exact MemoryOps.load_correct initial value returnAddress code data stack returnValid

theorem incrementLoop_sound (candidate : List Byte) (accepted : accepts .incrementLoop candidate = true)
    (initial : State) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip candidate)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes initial (IncrementLoop.finalState initial returnAddress)
      (IncrementLoop.cost (initial.registers .rcx).toNat) ∧
    ¬ Diverges initial ∧ ∀ final count, Executes initial final count →
      final = IncrementLoop.finalState initial returnAddress ∧
      count = IncrementLoop.cost (initial.registers .rcx).toNat := by
  have equal : candidate = IncrementLoop.bytes := of_decide_eq_true accepted
  subst candidate
  exact IncrementLoop.terminates_and_all_results_match initial returnAddress code stack returnValid

theorem store32_sound (candidate : List Byte) (accepted : accepts .store32 candidate = true)
    (initial : State) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip candidate)
    (allowed : canStoreDWord initial.memory (initial.registers .rdi) = true)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip candidate.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes initial (MemoryOps.storeFinal initial returnAddress) 2 ∧
    ¬ Diverges initial ∧
    ∀ final count, Executes initial final count →
      final = MemoryOps.storeFinal initial returnAddress ∧ count = 2 := by
  have equal : candidate = MemoryOps.storeBytes := of_decide_eq_true accepted
  subst candidate
  exact MemoryOps.store_correct initial returnAddress code allowed codeDisjoint stackDisjoint stack returnValid

end EDSL.Certificate
