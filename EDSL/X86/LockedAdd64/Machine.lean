/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedAdd64.Decode
import EDSL.X86.Sequential.Flags

namespace EDSL.X86.LockedAdd64

/-- Only the source register receives the complete old qword. Address, delta,
and incoming flags come from the prestate, even when base and source alias. -/
def afterAdd (state : State) (instruction : Instruction) (memory : Memory)
    (event : FetchAddEvent64) : State :=
  { state.writeRegister instruction.source event.event.before with
    memory := memory
    rip := state.rip + 5
    flags := Sequential.addFlags64 state.flags event.event.before
      (state.registers instruction.source) }

/-- One abstract indivisible primitive on current RAM, preceded by the
additional fixed-code gate. No ordinary sequential semantics are duplicated. -/
def execute (state : State) (instruction : Instruction) : Except Error Observation := do
  let address := state.registers instruction.base
  let delta := state.registers instruction.source
  if !dataOnly64 state.memory address then throw (.writeDenied address)
  let result ← fetchAddQWord state.memory address delta
  return ⟨result.2, afterAdd state instruction result.1 result.2, instruction.accesses state⟩

/-- Separate reusable locked-family dispatch; ordinary instructions are outside
this family and must be delegated by a future scheduler to Sequential. -/
def step (state : State) : Except Error Observation := do
  execute state (← decodeAt state)

theorem step_eq_execute {state : State} {instruction : Instruction}
    (decoded : decodeAt state = .ok instruction) : step state = execute state instruction := by
  simp only [step, decoded, ok_bind]

/-- A successful operation witnesses its actual primitive, source write, flags
and PC. The primitive witness is obtained from execution, never trusted as an
input to decoding or to the enabledness theorem. -/
structure Effect (initial : State) (instruction : Instruction)
    (event : FetchAddEvent64) (final : State) : Prop where
  primitive : fetchAddQWord initial.memory (initial.registers instruction.base)
    (initial.registers instruction.source) = .ok (final.memory, event)
  dataOnly : dataOnly64 initial.memory (initial.registers instruction.base) = true
  registers : final.registers =
    (initial.writeRegister instruction.source event.event.before).registers
  rip : final.rip = initial.rip + 5
  flags : final.flags = Sequential.addFlags64 initial.flags event.event.before
    (initial.registers instruction.source)

theorem execute_sound {initial : State} {instruction : Instruction} {observation : Observation}
    (success : execute initial instruction = .ok observation) :
    Effect initial instruction observation.event observation.state ∧
      observation.accesses = instruction.accesses initial := by
  by_cases data : dataOnly64 initial.memory (initial.registers instruction.base) = true
  · cases rmw : fetchAddQWord initial.memory (initial.registers instruction.base)
        (initial.registers instruction.source) with
    | error fault => simp [execute, data, rmw] at success
    | ok result =>
      simp [execute, data, rmw] at success
      subst observation
      exact ⟨⟨rmw, data, rfl, rfl, rfl⟩, rfl⟩
  · simp [execute, data] at success

theorem Effect.transition {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    RMWTransition64 initial.memory event.event final.memory :=
  (fetchAddQWord_sound _ _ _ _ effect.primitive).1

theorem Effect.delta {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) : event.delta = initial.registers instruction.source :=
  (fetchAddQWord_sound _ _ _ _ effect.primitive).2.1

theorem Effect.address {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) : event.event.address = initial.registers instruction.base :=
  (fetchAddQWord_sound _ _ _ _ effect.primitive).2.2.1

theorem Effect.after {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) : event.event.after = event.event.before + event.delta := by
  rw [effect.delta]
  exact (fetchAddQWord_sound _ _ _ _ effect.primitive).2.2.2

theorem Effect.modular {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    event.event.after.toNat = (event.event.before.toNat + event.delta.toNat) % 2^64 := by
  rw [effect.delta]
  exact fetchAddQWord_modular _ _ _ _ effect.primitive

theorem Effect.old {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    loadQWord initial.memory event.event.address = .ok event.event.before := effect.transition.2.2.1

theorem Effect.source_old {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    final.registers instruction.source = event.event.before := by
  simp [effect.registers, State.writeRegister]

theorem Effect.register_frame {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (register : Register)
    (other : register ≠ instruction.source) : final.registers register = initial.registers register := by
  simp [effect.registers, State.writeRegister, other]

theorem Effect.readback {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    loadQWord final.memory event.event.address = .ok event.event.after := effect.transition.readback

theorem Effect.permissions {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    final.memory.executable = initial.memory.executable ∧
    final.memory.writable = initial.memory.writable := effect.transition.permissions

theorem Effect.full_permissions {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (offset : Nat) (bound : offset < 8) :
    initial.memory.writable (event.event.address + BitVec.ofNat 64 offset) = true ∧
    (initial.memory.read (event.event.address + BitVec.ofNat 64 offset)).isSome = true :=
  effect.transition.full_permissions offset bound

theorem Effect.frame {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (query : Word)
    (outside : 8 ≤ (query - event.event.address).toNat) :
    final.memory.read query = initial.memory.read query := effect.transition.frame query outside

theorem Effect.preserves_code {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (base : Word) (bytes : List Byte)
    (code : CodeAt initial.memory base bytes)
    (disjoint : QWordDisjoint event.event.address base bytes.length) :
    CodeAt final.memory base bytes := effect.transition.preserves_code base bytes code disjoint

/-- The fixed-code gate itself separates the operand from every currently
executable code byte; a client need not supply an expected operand address. -/
theorem Effect.code_disjoint {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (base : Word) (bytes : List Byte)
    (code : CodeAt initial.memory base bytes) :
    QWordDisjoint event.event.address base bytes.length := by
  intro offset bound
  let query := base + BitVec.ofNat 64 offset
  by_cases outside : 8 ≤ (query - event.event.address).toNat
  · exact outside
  have small : (query - event.event.address).toNat < 8 := by omega
  have nonExecutable := dataOnly64_bytes initial.memory (initial.registers instruction.base)
    effect.dataOnly (query - event.event.address).toNat small
  have location : event.event.address + BitVec.ofNat 64 (query - event.event.address).toNat = query := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [← effect.address, location] at nonExecutable
  let byte := bytes[offset]'bound
  have present : bytes[offset]? = some byte := List.getElem?_eq_getElem bound
  have fetched := code.2 offset byte present
  unfold fetchByte at fetched
  split at fetched
  next allowed =>
    have executable := (Bool.and_eq_true_iff.mp allowed).2
    rw [nonExecutable] at executable
    contradiction
  next => cases fetched

theorem Effect.preserves_all_code {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (base : Word) (bytes : List Byte)
    (code : CodeAt initial.memory base bytes) : CodeAt final.memory base bytes :=
  effect.preserves_code base bytes code (effect.code_disjoint base bytes code)

theorem Effect.nonarithmetic_flags {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask := by
  rw [effect.flags]
  exact Sequential.addFlags64_preserves ..

/-- All six ADD flags reuse the established flag laws, including defined AF. -/
theorem Effect.flag_bits {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    final.flags.getLsbD 0 = event.event.before.uaddOverflow event.delta ∧
    final.flags.getLsbD 2 = evenParity (event.event.after.setWidth 8) ∧
    final.flags.getLsbD 4 = (event.event.before.setWidth 4).uaddOverflow (event.delta.setWidth 4) ∧
    final.flags.getLsbD 6 = (event.event.after == 0) ∧
    final.flags.getLsbD 7 = event.event.after.msb ∧
    final.flags.getLsbD 11 = event.event.before.saddOverflow event.delta := by
  rw [effect.flags, effect.after, effect.delta]
  exact Sequential.addFlags64_bits ..

theorem Effect.carry {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    final.flags.getLsbD 0 = true ↔ 2^64 ≤ event.event.before.toNat + event.delta.toNat := by
  rw [effect.flags, effect.delta]
  exact Sequential.addFlags64_carry ..

theorem Effect.overflow {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    final.flags.getLsbD 11 = true ↔
      event.event.before.toInt + event.delta.toInt < -(2^63 : Int) ∨
      2^63 ≤ event.event.before.toInt + event.delta.toInt := by
  rw [effect.flags, effect.delta]
  exact Sequential.addFlags64_overflow ..

/-- Only current gates are premises: the old value is read, not supplied. -/
theorem execute_enabled (state : State) (instruction : Instruction)
    (data : dataOnly64 state.memory (state.registers instruction.base) = true)
    (supported : atomicAddressable64 (state.registers instruction.base) = true)
    (allowed : canStoreQWord state.memory (state.registers instruction.base) = true) :
    ∃ observation, execute state instruction = .ok observation := by
  obtain ⟨result, success⟩ := fetchAddQWord_enabled state.memory
    (state.registers instruction.base) (state.registers instruction.source) supported allowed
  exact ⟨⟨result.2, afterAdd state instruction result.1 result.2, instruction.accesses state⟩,
    by simp [execute, data, success]⟩

theorem execute_enabled_iff (state : State) (instruction : Instruction) :
    (∃ observation, execute state instruction = .ok observation) ↔
    dataOnly64 state.memory (state.registers instruction.base) = true ∧
    atomicAddressable64 (state.registers instruction.base) = true ∧
    canStoreQWord state.memory (state.registers instruction.base) = true := by
  constructor
  · rintro ⟨observation, success⟩
    have effect := (execute_sound success).1
    have supported := effect.transition.1
    have allowed := effect.transition.2.1
    rw [effect.address] at supported allowed
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
  have supported := effect.transition.1
  have allowed := effect.transition.2.1
  have read := effect.old
  rw [effect.address] at supported allowed read
  exact ⟨effect.dataOnly, supported, allowed, _, read⟩

/-- Actual decoding, bidirectional code binding, one atomic effect, and exact
RMW8 intent are obtained from step success. No expected code is an input. -/
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
    obtain ⟨instruction, _, code, effect, _⟩ := step_sound success
    have supported := effect.transition.1
    have allowed := effect.transition.2.1
    rw [effect.address] at supported allowed
    exact ⟨instruction, code, effect.dataOnly, supported, allowed⟩
  · rintro ⟨instruction, code, data, supported, allowed⟩
    exact step_enabled_of_code instruction code data supported allowed

/-- Operand identity uses the actual arithmetic event, with no DWORD or
logical-event conversion. There is one joint RMW8, not separate read/write events. -/
theorem step_event_accesses {state : State} {observation : Observation}
    (success : step state = .ok observation) :
    observation.accesses = [.rmw8 observation.event.event.address] := by
  obtain ⟨instruction, _, _, effect, accesses, _⟩ := step_sound success
  rw [accesses, effect.address]

/-- Frozen [RDI],RAX receives the entire old qword, including its high half. -/
theorem frozen_rax_old {initial : State} {observation : Observation}
    (decoded : decodeAt initial = .ok frozen) (success : step initial = .ok observation) :
    observation.state.registers .rax = observation.event.event.before ∧
    observation.event.event.address = initial.registers .rdi ∧
    observation.event.delta = initial.registers .rax := by
  rw [step_eq_execute decoded] at success
  have effect := (execute_sound success).1
  exact ⟨effect.source_old, effect.address, effect.delta⟩

/-- Data/code exclusion precedes the primitive, even at zero delta. -/
theorem execute_not_data (state : State) (instruction : Instruction)
    (denied : dataOnly64 state.memory (state.registers instruction.base) = false) :
    execute state instruction = .error (.writeDenied (state.registers instruction.base)) := by
  simp [execute, denied]

/-- Exact failure alternatives after successful current decoding. Errors carry
no replacement state/event, so no partial result can escape any failed gate. -/
theorem execute_error_iff (state : State) (instruction : Instruction) (fault : Error) :
    execute state instruction = .error fault ↔
      (dataOnly64 state.memory (state.registers instruction.base) = false ∧
        fault = .writeDenied (state.registers instruction.base)) ∨
      (dataOnly64 state.memory (state.registers instruction.base) = true ∧
        fetchAddQWord state.memory (state.registers instruction.base)
          (state.registers instruction.source) = .error fault) := by
  by_cases data : dataOnly64 state.memory (state.registers instruction.base) = true
  · cases rmw : fetchAddQWord state.memory (state.registers instruction.base)
        (state.registers instruction.source) with
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

/-- The inherited primitive classification refines the second error case into
unsupported-address or current full-eight-byte permission denial. -/
theorem execute_primitive_error {state : State} {instruction : Instruction} {fault : Error}
    (data : dataOnly64 state.memory (state.registers instruction.base) = true)
    (failed : execute state instruction = .error fault) :
    (atomicAddressable64 (state.registers instruction.base) = false ∧
      fault = .unsupportedAtomicAddress (state.registers instruction.base)) ∨
    (atomicAddressable64 (state.registers instruction.base) = true ∧
      canStoreQWord state.memory (state.registers instruction.base) = false ∧
      fault = .writeDenied (state.registers instruction.base)) := by
  have primitive : fetchAddQWord state.memory (state.registers instruction.base)
      (state.registers instruction.source) = .error fault := by
    have cases := (execute_error_iff state instruction fault).mp failed
    simpa only [data, Bool.true_eq_false, false_and, false_or, true_and] using cases
  exact (fetchAddQWord_error_iff _ _ _ _).mp primitive

end EDSL.X86.LockedAdd64
