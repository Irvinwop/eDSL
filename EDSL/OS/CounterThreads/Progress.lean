/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Dispatch

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

theorem AdvanceEffect.remaining {state : State} {identifier : Nat} {worker : Worker} {result : Advance}
    (effect : AdvanceEffect state identifier worker result) (valid : PrivateValid worker) :
    result.worker.remaining + 1 = worker.remaining := by
  cases effect with
  | entry phase =>
    by_cases zero : worker.context.registers .rcx = 0
    all_goals
      simp only [BitVec.ofNat_eq_ofNat] at zero
      simp [Worker.remaining, evolved, nextPhase, phase, entryContext, zero]
      <;> omega
  | preparing phase =>
    simp [Worker.remaining, evolved, nextPhase, phase, immediateContext]
  | adding phase _ =>
    have p := valid
    simp only [PrivateValid, phase] at p
    have positive := BitVec.toNat_pos_of_ne_zero p.2.2.2.2.1
    simp [Worker.remaining, evolved, nextPhase, phase, addedContext]
    omega
  | backedge phase =>
    have p := valid
    simp only [PrivateValid, phase] at p
    have progress := decrement_count (worker.context.registers .rcx) p.2.2.2.2
    simp only [BitVec.ofNat_eq_ofNat] at progress
    by_cases zero : worker.context.registers .rcx - 1 = 0
    · have nextZero : (worker.context.registers .rcx - 1).toNat = 0 := congrArg BitVec.toNat zero
      simp only [BitVec.ofNat_eq_ofNat] at zero nextZero
      simp only [Worker.remaining, evolved, nextPhase, phase, loopContext, ↓reduceIte]
      simp only [BitVec.ofNat_eq_ofNat]
      simp only [zero, ↓reduceIte]
      omega
    · simp only [BitVec.ofNat_eq_ofNat] at zero
      simp only [Worker.remaining, evolved, nextPhase, phase, loopContext, ↓reduceIte]
      simp only [BitVec.ofNat_eq_ofNat]
      simp only [zero, ↓reduceIte]
      omega
  | finishing phase => simp [Worker.remaining, evolved, nextPhase, phase]
  | returning phase => simp [Worker.remaining, evolved, nextPhase, phase]

theorem AdvanceEffect.performed {state : State} {identifier : Nat} {worker : Worker} {result : Advance}
    (effect : AdvanceEffect state identifier worker result) (valid : PrivateValid worker) :
    result.worker.performed = worker.performed + (if result.event.isSome then 1 else 0) := by
  cases effect with
  | entry phase =>
    by_cases zero : worker.context.registers .rcx = 0
    all_goals
      simp only [BitVec.ofNat_eq_ofNat] at zero
      simp [Worker.performed, evolved, nextPhase, phase, entryContext, zero]
  | preparing phase => simp [Worker.performed, evolved, nextPhase, phase, immediateContext]
  | adding phase _ =>
    have p := valid
    simp only [PrivateValid, phase] at p
    have positive := BitVec.toNat_pos_of_ne_zero p.2.2.2.2.1
    have bound := p.2.1
    simp [Worker.performed, evolved, nextPhase, phase, addedContext]
    omega
  | backedge phase =>
    have p := valid
    simp only [PrivateValid, phase] at p
    have progress := decrement_count (worker.context.registers .rcx) p.2.2.2.2
    simp only [BitVec.ofNat_eq_ofNat] at progress
    by_cases zero : worker.context.registers .rcx - 1 = 0
    · have nextZero : (worker.context.registers .rcx - 1).toNat = 0 := congrArg BitVec.toNat zero
      simp only [BitVec.ofNat_eq_ofNat] at zero nextZero
      simp only [Worker.performed, evolved, nextPhase, phase, loopContext, ↓reduceIte]
      simp only [BitVec.ofNat_eq_ofNat]
      simp only [zero, ↓reduceIte, Option.isSome_none, reduceCtorEq, Bool.false_eq_true,
        Nat.add_zero, Nat.sub_zero, BitVec.toNat_zero]
      omega
    · simp only [BitVec.ofNat_eq_ofNat] at zero
      simp only [Worker.performed, evolved, nextPhase, phase, loopContext, ↓reduceIte]
      simp only [BitVec.ofNat_eq_ofNat]
      simp only [zero, ↓reduceIte, Option.isSome_none, reduceCtorEq, Bool.false_eq_true,
        Nat.add_zero, Nat.sub_zero]
      omega
  | finishing phase => simp [Worker.performed, evolved, nextPhase, phase, immediateContext]
  | returning phase => simp [Worker.performed, evolved, nextPhase, phase, returnedContext]

theorem dispatch_remaining (state : State) (identifier query : Nat) (worker : Worker)
    (result : State × Option AtomicEvent) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : dispatch state identifier = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.remaining + (if identifier = query then 1 else 0) = worker.remaining := by
  obtain ⟨selected, advanced, selectedAt, advancedOk, same⟩ := dispatch_ok _ _ _ success
  have selectedValid := (valid.2 _ _ selectedAt).2
  have effect := advance_effect state identifier selected advanced valid.1 selectedValid advancedOk
  rw [same]
  by_cases own : query = identifier
  · subst query
    have equal := Option.some.inj (selectedAt.symm.trans live)
    subst selected
    exact ⟨advanced.worker, by simp [replace], by simpa using effect.remaining selectedValid.privateContext⟩
  · exact ⟨worker, by simpa [replace, own] using live, by simp [Ne.symm own]⟩

end EDSL.OS.CounterThreads
