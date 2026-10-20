/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Dispatch

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

inductive UserStep (before after : X86.State) : Option AtomicEvent → Prop where
  | next (success : X86.step before = .ok (.next after)) : UserStep before after none
  | atomic {event} (success : X86.step before = .ok (.atomic event after)) : UserStep before after (some event)
  | returned (success : X86.step before = .ok (.returned after)) : UserStep before after none

/-- The complete projected machine state, including registers and flags,
comes from one actual decoded step against the current shared cells. -/
theorem AdvanceEffect.machine {state : State} {identifier : Nat} {worker : Worker} {result : Advance}
    (effect : AdvanceEffect state identifier worker result) (valid : WorkerValid state.shared identifier worker) :
    UserStep (worker.context.snapshot state.shared.shared.resources.space)
      (result.worker.context.snapshot result.shared.shared.resources.space) result.event := by
  cases effect with
  | entry phase => exact .next (entry_step _ _ _ valid phase)
  | preparing phase => exact .next (immediate_step _ _ _ 1 valid (by simp [expected, phase]))
  | adding phase success => exact .atomic (adding_step _ _ _ _ valid phase success)
  | backedge phase => exact .next (loop_step _ _ _ valid phase)
  | finishing phase => exact .next (immediate_step _ _ _ 0 valid (by simp [expected, phase]))
  | returning phase => exact .returned (return_step _ _ _ valid phase)

theorem AdvanceEffect.memory {state : State} {identifier : Nat} {worker : Worker} {result : Advance}
    (effect : AdvanceEffect state identifier worker result) (valid : WorkerValid state.shared identifier worker) :
    match result.event with
    | none => result.shared.shared.resources = state.shared.shared.resources
    | some event => event.address = worker.entry.registers .rdi ∧ event.after = event.before + 1 ∧
        loadDWord (toMemory state.shared.shared.resources.space) event.address = .ok event.before ∧
        loadDWord (toMemory result.shared.shared.resources.space) event.address = .ok event.after := by
  cases effect with
  | entry _ | preparing _ | backedge _ | finishing _ | returning _ => rfl
  | adding _ success =>
    obtain ⟨handle, authorized, transition⟩ := Atomics.fetchAdd_sound _ _ _ _ _ success
    obtain ⟨other, checked, address⟩ := valid.authorized
    have same := Except.ok.inj (authorized.symm.trans checked)
    subst other
    exact ⟨rfl, rfl, by simpa only [address] using transition.2.2.1,
      by simpa only [address] using transition.readback⟩

theorem dispatch_machine (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) :
    ∃ worker current, state.workers identifier = some worker ∧ result.1.workers identifier = some current ∧
      UserStep (worker.context.snapshot state.shared.shared.resources.space)
        (current.context.snapshot result.1.shared.shared.resources.space) result.2 := by
  obtain ⟨worker, advanced, found, selected, same⟩ := dispatch_ok _ _ _ success
  have effect := advance_effect state identifier worker advanced valid.1 (valid.2 _ _ found).2 selected
  rw [same]
  exact ⟨worker, advanced.worker, found, by simp [replace], effect.machine (valid.2 _ _ found).2⟩

end EDSL.OS.CounterThreads
