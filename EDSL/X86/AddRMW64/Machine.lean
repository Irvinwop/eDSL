/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.AddRMW64.Decode

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.AddRMW64

/-- One fixed-code gate and one existing indivisible current-RAM primitive.
An error contains neither a replacement state nor an event. -/
def execute (state : State) (instruction : Instruction) : Except Error Observation := do
  let address := state.registers instruction.base
  let delta := instruction.delta state
  if !dataOnly64 state.memory address then throw (.writeDenied address)
  let result ← fetchAddQWord state.memory address delta
  return ⟨result.2, afterRmw state instruction result.1 result.2, instruction.accesses state⟩

def step (state : State) : Except Error Observation := do
  execute state (← decodeAt state)

theorem step_eq_execute {state : State} {instruction : Instruction}
    (decoded : decodeAt state = .ok instruction) : step state = execute state instruction := by
  simp only [step, decoded, ok_bind]

/-- Full arbitrary-state instruction effect. Code is certified separately by
step_sound; there is no assumed successful decode, desired old value, OS
authority, or physical execution hidden in this primitive contract. -/
structure Effect (initial : State) (instruction : Instruction)
    (event : FetchAddEvent64) (final : State) : Prop where
  primitive : fetchAddQWord initial.memory (initial.registers instruction.base)
    (instruction.delta initial) = .ok (final.memory, event)
  dataOnly : dataOnly64 initial.memory (initial.registers instruction.base) = true
  registers : final.registers = instruction.registersAfter initial event
  rip : final.rip = initial.rip + BitVec.ofNat 64 instruction.length
  flags : final.flags = instruction.flagsAfter initial.flags event.event.before (instruction.delta initial)

theorem execute_sound {initial : State} {instruction : Instruction} {observation : Observation}
    (success : execute initial instruction = .ok observation) :
    Effect initial instruction observation.event observation.state ∧
      observation.accesses = instruction.accesses initial := by
  by_cases data : dataOnly64 initial.memory (initial.registers instruction.base) = true
  · cases rmw : fetchAddQWord initial.memory (initial.registers instruction.base)
        (instruction.delta initial) with
    | error fault => simp [execute, data, rmw] at success
    | ok result =>
      simp [execute, data, rmw] at success
      subst observation
      exact ⟨⟨rmw, data, rfl, rfl, rfl⟩, rfl⟩
  · simp [execute, data] at success

/-- Enabledness needs only the current data gate, address support and all
eight bytes' read/write preflight. The old value is read by the primitive. -/
theorem execute_enabled (state : State) (instruction : Instruction)
    (data : dataOnly64 state.memory (state.registers instruction.base) = true)
    (supported : atomicAddressable64 (state.registers instruction.base) = true)
    (allowed : canStoreQWord state.memory (state.registers instruction.base) = true) :
    ∃ observation, execute state instruction = .ok observation := by
  obtain ⟨result, success⟩ := fetchAddQWord_enabled state.memory
    (state.registers instruction.base) (instruction.delta state) supported allowed
  exact ⟨⟨result.2, afterRmw state instruction result.1 result.2, instruction.accesses state⟩,
    by simp [execute, data, success]⟩

theorem execute_enabled_iff (state : State) (instruction : Instruction) :
    (∃ observation, execute state instruction = .ok observation) ↔
    dataOnly64 state.memory (state.registers instruction.base) = true ∧
    atomicAddressable64 (state.registers instruction.base) = true ∧
    canStoreQWord state.memory (state.registers instruction.base) = true := by
  constructor
  · rintro ⟨observation, success⟩
    have effect := (execute_sound success).1
    have sound := fetchAddQWord_sound _ _ _ _ effect.primitive
    have supported := sound.1.1
    have allowed := sound.1.2.1
    rw [sound.2.2.1] at supported allowed
    exact ⟨effect.dataOnly, supported, allowed⟩
  · rintro ⟨data, supported, allowed⟩
    exact execute_enabled state instruction data supported allowed

theorem execute_accesses_succeed {state : State} {instruction : Instruction} {observation : Observation}
    (success : execute state instruction = .ok observation) :
    ∀ access ∈ observation.accesses, AccessSucceeds state access := by
  obtain ⟨effect, accesses⟩ := execute_sound success
  rw [accesses]
  intro access member
  simp only [Instruction.accesses, List.mem_singleton] at member
  subst access
  have sound := fetchAddQWord_sound _ _ _ _ effect.primitive
  have supported := sound.1.1
  have allowed := sound.1.2.1
  have read := sound.1.2.2.1
  rw [sound.2.2.1] at supported allowed read
  exact ⟨effect.dataOnly, supported, allowed, _, read⟩

theorem step_sound {initial : State} {observation : Observation}
    (success : step initial = .ok observation) :
    ∃ instruction, decodeAt initial = .ok instruction ∧
      CodeAt initial.memory initial.rip instruction.bytes ∧
      Effect initial instruction observation.event observation.state ∧
      observation.accesses = [.rmw8 (initial.registers instruction.base)] ∧
      ∀ access ∈ observation.accesses, AccessSucceeds initial access := by
  cases decoded : decodeAt initial with
  | error fault => simp [step, decoded] at success
  | ok instruction =>
    rw [step_eq_execute decoded] at success
    have sound := execute_sound success
    exact ⟨instruction, rfl, decodeAt_code decoded, sound.1, sound.2,
      execute_accesses_succeed success⟩

theorem step_enabled {state : State} {instruction : Instruction}
    (decoded : decodeAt state = .ok instruction)
    (data : dataOnly64 state.memory (state.registers instruction.base) = true)
    (supported : atomicAddressable64 (state.registers instruction.base) = true)
    (allowed : canStoreQWord state.memory (state.registers instruction.base) = true) :
    ∃ observation, step state = .ok observation := by
  rw [step_eq_execute decoded]
  exact execute_enabled state instruction data supported allowed

theorem step_enabled_of_code {state : State} (instruction : Instruction)
    (code : CodeAt state.memory state.rip instruction.bytes)
    (data : dataOnly64 state.memory (state.registers instruction.base) = true)
    (supported : atomicAddressable64 (state.registers instruction.base) = true)
    (allowed : canStoreQWord state.memory (state.registers instruction.base) = true) :
    ∃ observation, step state = .ok observation :=
  step_enabled (decodeAt_of_code instruction code) data supported allowed

theorem step_enabled_iff (state : State) :
    (∃ observation, step state = .ok observation) ↔
      ∃ instruction : Instruction, CodeAt state.memory state.rip instruction.bytes ∧
        dataOnly64 state.memory (state.registers instruction.base) = true ∧
        atomicAddressable64 (state.registers instruction.base) = true ∧
        canStoreQWord state.memory (state.registers instruction.base) = true := by
  constructor
  · rintro ⟨observation, success⟩
    obtain ⟨instruction, decoded, code, _⟩ := step_sound success
    have gates := (execute_enabled_iff state instruction).mp
      ⟨observation, by rwa [step_eq_execute decoded] at success⟩
    exact ⟨instruction, code, gates⟩
  · rintro ⟨instruction, code, data, supported, allowed⟩
    exact step_enabled_of_code instruction code data supported allowed

theorem step_event_accesses {state : State} {observation : Observation}
    (success : step state = .ok observation) :
    observation.accesses = [.rmw8 observation.event.event.address] := by
  obtain ⟨instruction, _, _, effect, accesses, _⟩ := step_sound success
  have address := (fetchAddQWord_sound _ _ _ _ effect.primitive).2.2.1
  rw [accesses, address]

/-- Fixed-code exclusion precedes even unsupported-address validation. -/
theorem execute_not_data (state : State) (instruction : Instruction)
    (denied : dataOnly64 state.memory (state.registers instruction.base) = false) :
    execute state instruction = .error (.writeDenied (state.registers instruction.base)) := by
  simp [execute, denied]

theorem execute_error_iff (state : State) (instruction : Instruction) (fault : Error) :
    execute state instruction = .error fault ↔
      (dataOnly64 state.memory (state.registers instruction.base) = false ∧
        fault = .writeDenied (state.registers instruction.base)) ∨
      (dataOnly64 state.memory (state.registers instruction.base) = true ∧
        fetchAddQWord state.memory (state.registers instruction.base)
          (instruction.delta state) = .error fault) := by
  by_cases data : dataOnly64 state.memory (state.registers instruction.base) = true
  · cases rmw : fetchAddQWord state.memory (state.registers instruction.base)
        (instruction.delta state) with
    | error error => simp [execute, data, rmw]
    | ok result => simp [execute, data, rmw]
  · have denied := Bool.eq_false_iff.mpr data
    rw [execute_not_data state instruction denied]
    constructor
    · intro failed
      exact Or.inl ⟨denied, (Except.error.inj failed).symm⟩
    · rintro (⟨_, rfl⟩ | ⟨contradiction, _⟩)
      · rfl
      · simp only [denied, Bool.false_eq_true] at contradiction

theorem step_error_iff (state : State) (fault : Error) :
    step state = .error fault ↔ decodeAt state = .error fault ∨
      ∃ instruction, decodeAt state = .ok instruction ∧ execute state instruction = .error fault := by
  cases decoded : decodeAt state with
  | error error => simp [step, decoded]
  | ok instruction => simp [step, decoded]

theorem execute_primitive_error {state : State} {instruction : Instruction} {fault : Error}
    (data : dataOnly64 state.memory (state.registers instruction.base) = true)
    (failed : execute state instruction = .error fault) :
    (atomicAddressable64 (state.registers instruction.base) = false ∧
      fault = .unsupportedAtomicAddress (state.registers instruction.base)) ∨
    (atomicAddressable64 (state.registers instruction.base) = true ∧
      canStoreQWord state.memory (state.registers instruction.base) = false ∧
      fault = .writeDenied (state.registers instruction.base)) := by
  have primitive : fetchAddQWord state.memory (state.registers instruction.base)
      (instruction.delta state) = .error fault := by
    have alternatives := (execute_error_iff state instruction fault).mp failed
    simpa only [data, Bool.true_eq_false, false_and, false_or, true_and] using alternatives
  exact (fetchAddQWord_error_iff _ _ _ _).mp primitive

end EDSL.X86.AddRMW64
