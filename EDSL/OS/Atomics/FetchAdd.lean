/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics.Trace
import EDSL.Examples.Compiler.FetchAdd

namespace EDSL.OS.Atomics
open X86 AddressSpace

/-- A checked handle-authorized fetch-add. The read and replacement below are
one pure operation on one current snapshot, with no admitted intermediate
environment step. Native conformance requires the locked-instruction bridge. -/
def fetchAdd (state : State) (actor identifier : Nat) (delta : BitVec 32) :
    Except Fault (State × BitVec 32) := do
  let handle ← authorize state actor identifier
  let old ← (loadDWord (toMemory state.shared.resources.space) handle.address).mapError Fault.machine
  exchange state actor identifier (old + delta)

theorem fetchAdd_ok (state : State) (actor identifier : Nat) (delta : BitVec 32)
    (result : State × BitVec 32) (success : fetchAdd state actor identifier delta = .ok result) :
    ∃ handle, authorize state actor identifier = .ok handle ∧
      loadDWord (toMemory state.shared.resources.space) handle.address = .ok result.2 ∧
      exchange state actor identifier (result.2 + delta) = .ok result := by
  cases authority : authorize state actor identifier with
  | error fault => simp [fetchAdd, authority] at success
  | ok handle =>
    cases read : loadDWord (toMemory state.shared.resources.space) handle.address with
    | error fault => simp [fetchAdd, authority, read, Except.mapError] at success
    | ok old =>
      have exchanged : exchange state actor identifier (old + delta) = .ok result := by
        simpa [fetchAdd, authority, read, Except.mapError] using success
      obtain ⟨other, checked, transition⟩ := exchange_sound _ _ _ _ _ exchanged
      have same := Except.ok.inj (checked.symm.trans authority)
      subst other
      have equal : result.2 = old := Except.ok.inj (transition.2.2.1.symm.trans read)
      exact ⟨handle, rfl, by rw [equal]; exact read, by rw [equal]; exact exchanged⟩

theorem fetchAdd_sound (state : State) (actor identifier : Nat) (delta : BitVec 32)
    (result : State × BitVec 32) (success : fetchAdd state actor identifier delta = .ok result) :
    ∃ handle, authorize state actor identifier = .ok handle ∧
      ExchangeTransition (toMemory state.shared.resources.space) ⟨handle.address, result.2, result.2 + delta⟩
        (toMemory result.1.shared.resources.space) := by
  obtain ⟨_, _, _, exchanged⟩ := fetchAdd_ok _ _ _ _ _ success
  exact exchange_sound _ _ _ _ _ exchanged

theorem fetchAdd_wellFormed (state : State) (actor identifier : Nat) (delta : BitVec 32)
    (result : State × BitVec 32) (valid : WellFormed state)
    (success : fetchAdd state actor identifier delta = .ok result) : WellFormed result.1 := by
  obtain ⟨_, _, _, exchanged⟩ := fetchAdd_ok _ _ _ _ _ success
  exact exchange_wellFormed _ _ _ _ _ valid exchanged

theorem fetchAdd_history (state : State) (actor identifier : Nat) (delta : BitVec 32)
    (result : State × BitVec 32) (success : fetchAdd state actor identifier delta = .ok result) :
    History state result.1 := by
  obtain ⟨_, _, _, exchanged⟩ := fetchAdd_ok _ _ _ _ _ success
  exact .next (.exchange exchanged) .refl

theorem fetchAdd_enabled (state : State) (actor identifier : Nat) (handle : Handle)
    (delta : BitVec 32) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok handle) :
    ∃ result, fetchAdd state actor identifier delta = .ok result := by
  have live := (authorize_ok _ _ _ _ authorized).1
  obtain ⟨_, _, _, _, _, _, _, writable⟩ := valid.handles _ _ live
  obtain ⟨old, read⟩ := load_exists_of_canStore _ _ writable
  obtain ⟨result, exchanged⟩ := exchange_enabled state actor identifier handle (old + delta) valid authorized
  exact ⟨result, by simp [fetchAdd, authorized, read, exchanged, Except.mapError]⟩

def afterFetchAdd (initial : X86.State) (space : Space) (old : BitVec 32) : X86.State :=
  { initial.writeRegister .rax (old.setWidth 64) with
    memory := toMemory space
    rip := initial.rip + 4
    flags := addFlags32 initial.flags old ((initial.registers .rax).setWidth 32) }

theorem fetchAdd_step (state : State) (actor identifier : Nat) (delta : BitVec 32)
    (result : State × BitVec 32) (handle : Handle) (initial : X86.State)
    (success : fetchAdd state actor identifier delta = .ok result)
    (authorized : authorize state actor identifier = .ok handle)
    (memory : initial.memory = toMemory state.shared.resources.space)
    (operand : initial.registers .rdi = handle.address)
    (replacement : (initial.registers .rax).setWidth 32 = delta)
    (decoded : decodeAt initial = .ok .fetchAddEaxRdi) :
    X86.step initial = .ok (.atomic ⟨handle.address, result.2, result.2 + delta⟩
      (afterFetchAdd initial result.1.shared.resources.space result.2)) := by
  obtain ⟨selected, checked, transition⟩ := fetchAdd_sound _ _ _ _ _ success
  have same := Except.ok.inj (checked.symm.trans authorized)
  subst selected
  have added := X86.fetchAddDWord_success _ handle.address result.2 delta
    transition.1 transition.2.1 transition.2.2.1
  simp [X86.step, decoded, executeFetchAdd, operand, replacement, memory, added,
    afterFetchAdd, transition.2.2.2]

/-- Exact compiler bytes refine the checked resource operation. The explicit
memory equality binds the complete routine's final machine memory to OS cells. -/
theorem fetchAdd32_updates_space (state : State) (actor identifier : Nat)
    (result : State × BitVec 32) (handle : Handle) (initial : X86.State) (returnAddress : Word)
    (success : fetchAdd state actor identifier ((initial.registers .rsi).setWidth 32) = .ok result)
    (authorized : authorize state actor identifier = .ok handle)
    (operand : initial.registers .rdi = handle.address)
    (code : CodeAt (toMemory state.shared.resources.space) initial.rip Examples.Compiler.FetchAdd.bytes)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip Examples.Compiler.FetchAdd.bytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord (toMemory state.shared.resources.space) (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    let entry := { initial with memory := toMemory state.shared.resources.space }
    let final := Examples.Compiler.FetchAdd.finalState entry result.2 returnAddress
    AtomicExecutes entry final 3 [Examples.Compiler.FetchAdd.event entry result.2] ∧
    final.memory = toMemory result.1.shared.resources.space ∧
    Executes entry final 3 ∧ ¬ Diverges entry ∧
    ∀ other count, Executes entry other count → other = final ∧ count = 3 := by
  obtain ⟨selected, checked, transition⟩ := fetchAdd_sound _ _ _ _ _ success
  have same := Except.ok.inj (checked.symm.trans authorized)
  subst selected
  have supported : atomicAddressable (initial.registers .rdi) = true := by simpa [operand] using transition.1
  have allowed : canStoreDWord (toMemory state.shared.resources.space) (initial.registers .rdi) = true := by
    simpa [operand] using transition.2.1
  have read : loadDWord (toMemory state.shared.resources.space) (initial.registers .rdi) = .ok result.2 := by
    simpa [operand] using transition.2.2.1
  have proof := Examples.Compiler.FetchAdd.correct { initial with memory := toMemory state.shared.resources.space }
    result.2 returnAddress code supported allowed read codeDisjoint stackDisjoint stack returnValid
  exact ⟨proof.1, by simpa [Examples.Compiler.FetchAdd.finalState, operand] using transition.2.2.2.symm, proof.2⟩

structure Addition where
  actor : Nat
  identifier : Nat
  delta : BitVec 32
  old : BitVec 32

/-- A finite sequence of successful, same-cell fetch-add operations. No outside
memory updates or administrative resource actions are implicit in this trace. -/
inductive AddTrace (address : Word) : State → State → List Addition → Prop where
  | nil {state} : AddTrace address state state []
  | next {before middle after actor identifier delta old handle events}
      (authorized : authorize before actor identifier = .ok handle)
      (target : handle.address = address)
      (success : fetchAdd before actor identifier delta = .ok (middle, old))
      (tail : AddTrace address middle after events) :
      AddTrace address before after (⟨actor, identifier, delta, old⟩ :: events)

def totalDelta (events : List Addition) : BitVec 32 :=
  events.foldr (fun event total => event.delta + total) 0

/-- The final word is the independently observed initial value plus every
actual delta, modulo 2^32. Intermediate old results come from current memory,
not from handle issuance. This is a safety result for supplied finite traces. -/
theorem AddTrace.counter {address : Word} {before after : State} {events : List Addition}
    (trace : AddTrace address before after events) (initial : BitVec 32)
    (observed : loadDWord (toMemory before.shared.resources.space) address = .ok initial) :
    loadDWord (toMemory after.shared.resources.space) address = .ok (initial + totalDelta events) := by
  induction trace generalizing initial with
  | nil => simpa [totalDelta] using observed
  | @next before middle after actor identifier delta old handle events authorized target success tail induction =>
    obtain ⟨selected, checked, transition⟩ := fetchAdd_sound _ _ _ _ _ success
    have same := Except.ok.inj (checked.symm.trans authorized)
    subst selected
    have read : loadDWord (toMemory before.shared.resources.space) address = .ok old := by
      simpa only [target] using transition.2.2.1
    have equal : old = initial := Except.ok.inj (read.symm.trans observed)
    have nextRead : loadDWord (toMemory middle.shared.resources.space) address = .ok (old + delta) := by
      simpa only [target] using transition.readback
    have final := induction (old + delta) nextRead
    simpa [totalDelta, equal, BitVec.add_assoc] using final

theorem history_append {before middle after : State}
    (first : History before middle) (last : History middle after) : History before after := by
  induction first with
  | refl => exact last
  | next step _ induction => exact .next step (induction last)

theorem AddTrace.history {address : Word} {before after : State} {events : List Addition}
    (trace : AddTrace address before after events) : History before after := by
  induction trace with
  | nil => exact .refl
  | next _ _ success _ induction => exact history_append (fetchAdd_history _ _ _ _ _ success) induction

end EDSL.OS.Atomics
