/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedLogical64.Decode
import EDSL.X86.Sequential.Flags

namespace EDSL.X86.LockedLogical64

/-- LOCK OR has no register result, including no fetched-old value in RAX. -/
def afterOr (state : State) (memory : Memory) (value : Word) (af : Bool) : State :=
  { state with
    memory := memory
    rip := state.rip + 4
    flags := Sequential.logicalFlags64 state.flags value af }

/-- The operation and mask are selected from the instruction and CURRENT RSI.
The separate fixed-code gate checks all eight execute bits. AF is an independent
unspecified choice; no default Boolean is chosen by this profile. -/
def execute (state : State) (instruction : Instruction) (af : Bool) : Except Error Observation := do
  match instruction with
  | .orRdiRsi =>
    if !dataOnly64 state.memory (state.registers .rdi) then
      throw (.writeDenied (state.registers .rdi))
    let result ← logicalRmwQWord .bor state.memory (state.registers .rdi) (state.registers .rsi)
    return ⟨.atomic64 result.2 (afterOr state result.1 result.2.event.after af),
      instruction.accesses state⟩
  | .ret => return ⟨.returned (← X86.executeRet state), instruction.accesses state⟩

def step (af : Bool) (state : State) : Except Error Observation := do
  let instruction ← decodeAt state
  execute state instruction af

theorem step_eq_execute {state : State} {instruction : Instruction} (af : Bool)
    (decoded : decodeAt state = .ok instruction) :
    step af state = execute state instruction af := by
  simp only [step, decoded, ok_bind]

/-- Exact operation-specific context, usable without unfolding memory reads. -/
theorem execute_orRdiRsi_context (state : State) (old : Word) (af : Bool)
    (supported : atomicAddressable64 (state.registers .rdi) = true)
    (allowed : canStoreQWord state.memory (state.registers .rdi) = true)
    (data : dataOnly64 state.memory (state.registers .rdi) = true)
    (read : loadQWord state.memory (state.registers .rdi) = .ok old) :
    execute state .orRdiRsi af = .ok ⟨.atomic64
      ⟨.bor, state.registers .rsi,
        ⟨state.registers .rdi, old, old ||| state.registers .rsi⟩⟩
      (afterOr state (writeQWordUnchecked state.memory (state.registers .rdi)
        (old ||| state.registers .rsi)) (old ||| state.registers .rsi) af),
      [.rmw8 (state.registers .rdi)]⟩ := by
  have rmw := logicalRmwQWord_success .bor state.memory (state.registers .rdi)
    (state.registers .rsi) old supported allowed read
  simp only [Sequential.LogicalOp.eval] at rmw
  simp [execute, data, rmw, Instruction.accesses]

/-- Frames and labels obtained from execution, never supplied by the caller. -/
structure OrEffect (initial : State) (af : Bool) (label : LogicalEvent64) (final : State) : Prop where
  transition : RMWTransition64 initial.memory label.event final.memory
  dataOnly : dataOnly64 initial.memory (initial.registers .rdi) = true
  op : label.op = .bor
  mask : label.mask = initial.registers .rsi
  address : label.event.address = initial.registers .rdi
  value : label.event.after = label.event.before ||| initial.registers .rsi
  registers : final.registers = initial.registers
  rip : final.rip = initial.rip + 4
  flags : final.flags = Sequential.logicalFlags64 initial.flags label.event.after af

theorem execute_orRdiRsi_sound {initial final : State} {af : Bool} {label : LogicalEvent64}
    {accesses : List Access}
    (success : execute initial .orRdiRsi af = .ok ⟨.atomic64 label final, accesses⟩) :
    OrEffect initial af label final := by
  by_cases data : dataOnly64 initial.memory (initial.registers .rdi) = true
  · cases rmw : logicalRmwQWord .bor initial.memory (initial.registers .rdi)
        (initial.registers .rsi) with
    | error fault => simp [execute, data, rmw] at success
    | ok result =>
      simp [execute, data, rmw] at success
      rcases success with ⟨⟨rfl, rfl⟩, rfl⟩
      have sound := logicalRmwQWord_sound _ _ _ _ _ rmw
      exact ⟨sound.1, data, sound.2.1, sound.2.2.1, sound.2.2.2.1,
        sound.2.2.2.2, rfl, rfl, rfl⟩
  · simp [execute, data] at success

theorem OrEffect.readback {initial final : State} {af : Bool} {label : LogicalEvent64}
    (effect : OrEffect initial af label final) :
    loadQWord final.memory label.event.address = .ok label.event.after := effect.transition.readback

theorem OrEffect.permissions {initial final : State} {af : Bool} {label : LogicalEvent64}
    (effect : OrEffect initial af label final) :
    final.memory.executable = initial.memory.executable ∧
    final.memory.writable = initial.memory.writable := effect.transition.permissions

theorem OrEffect.frame {initial final : State} {af : Bool} {label : LogicalEvent64}
    (effect : OrEffect initial af label final) (query : Word)
    (outside : 8 ≤ (query - label.event.address).toNat) :
    final.memory.read query = initial.memory.read query := effect.transition.frame query outside

theorem OrEffect.preserves_code {initial final : State} {af : Bool} {label : LogicalEvent64}
    (effect : OrEffect initial af label final) (base : Word) (bytes : List Byte)
    (code : CodeAt initial.memory base bytes)
    (disjoint : QWordDisjoint label.event.address base bytes.length) :
    CodeAt final.memory base bytes := effect.transition.preserves_code base bytes code disjoint

/-- In particular, a disjoint caller slot retains its actual eight-byte read. -/
theorem OrEffect.stack_frame {initial final : State} {af : Bool} {label : LogicalEvent64}
    (effect : OrEffect initial af label final) (address : Word)
    (disjoint : QWordDisjoint label.event.address address 8) :
    readWord final.memory address = readWord initial.memory address := by
  apply readWord_congr
  intro offset bound
  exact effect.frame _ (disjoint offset bound)

theorem OrEffect.data_frame {initial final : State} {af : Bool} {label : LogicalEvent64}
    (effect : OrEffect initial af label final) (address : Word)
    (disjoint : QWordDisjoint label.event.address address 8) :
    loadQWord final.memory address = loadQWord initial.memory address := by
  apply loadQWord_congr
  intro offset bound
  exact effect.frame _ (disjoint offset bound)

theorem OrEffect.nonarithmetic_flags {initial final : State} {af : Bool} {label : LogicalEvent64}
    (effect : OrEffect initial af label final) :
    final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask := by
  rw [effect.flags]
  exact Sequential.logicalFlags64_preserves ..

/-- Defined flags and the explicit AF choice, for arbitrary full64 results. -/
theorem OrEffect.flag_bits {initial final : State} {af : Bool} {label : LogicalEvent64}
    (effect : OrEffect initial af label final) :
    final.flags.getLsbD 0 = false ∧
    final.flags.getLsbD 2 = evenParity (label.event.after.setWidth 8) ∧
    final.flags.getLsbD 4 = af ∧
    final.flags.getLsbD 6 = (label.event.after == 0) ∧
    final.flags.getLsbD 7 = label.event.after.msb ∧ final.flags.getLsbD 11 = false := by
  rw [effect.flags]
  exact Sequential.logicalFlags64_bits ..

/-- Both choices cover exactly the abstract logical flag contract; this is
not an assertion about a physical processor's choice of undefined AF. -/
theorem afterOr_flags_admissible_iff (state : State) (memory : Memory) (value actual : Word) :
    Sequential.LogicalFlagsAdmissible state.flags actual
      (evenParity (value.setWidth 8)) (value == 0) value.msb ↔
      ∃ af, actual = (afterOr state memory value af).flags := by
  exact Sequential.logicalFlags64_admissible_iff ..

theorem execute_ret_context (state : State) (target : Word) (af : Bool)
    (read : readWord state.memory (state.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) :
    execute state .ret af = .ok ⟨.returned
      { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target },
      [.stack8 (state.registers .rsp)]⟩ := by
  simp [execute, X86.executeRet, read, canonicalTarget, Instruction.accesses]

structure RetEffect (initial final : State) : Prop where
  read : readWord initial.memory (initial.registers .rsp) = .ok final.rip
  canonical : canonical final.rip = true
  registers : final.registers = (initial.writeRegister .rsp (initial.registers .rsp + 8)).registers
  memory : final.memory = initial.memory
  flags : final.flags = initial.flags

theorem execute_ret_sound {initial final : State} {af : Bool} {accesses : List Access}
    (success : execute initial .ret af = .ok ⟨.returned final, accesses⟩) :
    RetEffect initial final := by
  cases read : readWord initial.memory (initial.registers .rsp) with
  | error fault => simp [execute, X86.executeRet, read] at success
  | ok target =>
    by_cases valid : canonical target = true
    · simp [execute, X86.executeRet, read, valid] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨read, valid, rfl, rfl, rfl⟩
    · simp [execute, X86.executeRet, read, valid] at success

theorem RetEffect.rsp {initial final : State} (effect : RetEffect initial final) :
    final.registers .rsp = initial.registers .rsp + 8 := by
  simp [effect.registers, State.writeRegister]

theorem RetEffect.register_frame {initial final : State} (effect : RetEffect initial final)
    (register : Register) (other : register ≠ .rsp) :
    final.registers register = initial.registers register := by
  simp [effect.registers, State.writeRegister, other]

/-- Complete observation footprints are generated by the actual instruction. -/
theorem execute_accesses {state : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (success : execute state instruction af = .ok observation) :
    observation.accesses = instruction.accesses state := by
  cases instruction with
  | orRdiRsi =>
    by_cases data : dataOnly64 state.memory (state.registers .rdi) = true
    · cases rmw : logicalRmwQWord .bor state.memory (state.registers .rdi) (state.registers .rsi) with
      | error fault => simp [execute, data, rmw] at success
      | ok result =>
        simp [execute, data, rmw] at success
        subst observation
        rfl
    · simp [execute, data] at success
  | ret =>
    cases result : X86.executeRet state with
    | error fault => simp [execute, result] at success
    | ok final =>
      simp [execute, result] at success
      subst observation
      rfl

theorem execute_atomic64_sound {initial final : State} {instruction : Instruction} {af : Bool}
    {label : LogicalEvent64} {accesses : List Access}
    (success : execute initial instruction af = .ok ⟨.atomic64 label final, accesses⟩) :
    instruction = .orRdiRsi ∧ OrEffect initial af label final := by
  cases instruction with
  | orRdiRsi => exact ⟨rfl, execute_orRdiRsi_sound success⟩
  | ret => cases result : X86.executeRet initial <;> simp [execute, result] at success

theorem execute_returned_sound {initial final : State} {instruction : Instruction} {af : Bool}
    {accesses : List Access}
    (success : execute initial instruction af = .ok ⟨.returned final, accesses⟩) :
    instruction = .ret ∧ RetEffect initial final := by
  cases instruction with
  | ret => exact ⟨rfl, execute_ret_sound success⟩
  | orRdiRsi =>
    by_cases data : dataOnly64 initial.memory (initial.registers .rdi) = true
    · cases rmw : logicalRmwQWord .bor initial.memory (initial.registers .rdi) (initial.registers .rsi) <;>
        simp [execute, data, rmw] at success
    · simp [execute, data] at success

theorem execute_accesses_succeed {state : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (success : execute state instruction af = .ok observation) :
    ∀ access ∈ observation.accesses, AccessSucceeds state access := by
  rcases observation with ⟨result, accesses⟩
  have exactAccesses := execute_accesses success
  rw [exactAccesses]
  cases instruction with
  | orRdiRsi =>
    cases result with
    | returned final =>
      have := execute_returned_sound success
      cases this.1
    | atomic64 label final =>
      have effect := execute_orRdiRsi_sound success
      intro access member
      simp only [Instruction.accesses, List.mem_singleton] at member
      subst access
      rcases effect.transition with ⟨supported, allowed, read, _⟩
      rw [effect.address] at supported allowed read
      exact ⟨supported, effect.dataOnly, allowed, _, read⟩
  | ret =>
    cases result with
    | atomic64 label final =>
      have := execute_atomic64_sound success
      cases this.1
    | returned final =>
      have effect := execute_ret_sound success
      intro access member
      simp only [Instruction.accesses, List.mem_singleton] at member
      subst access
      exact ⟨final.rip, effect.read⟩

/-- Fetch and execute are both actual successful transitions. -/
theorem step_sound {initial : State} {af : Bool} {observation : Observation}
    (success : step af initial = .ok observation) :
    ∃ instruction, decodeAt initial = .ok instruction ∧
      execute initial instruction af = .ok observation := by
  cases decoded : decodeAt initial with
  | error fault => simp [step, decoded] at success
  | ok instruction =>
    exact ⟨instruction, rfl, by simpa only [step, decoded, ok_bind] using success⟩

theorem step_accesses {initial : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (decoded : decodeAt initial = .ok instruction)
    (success : step af initial = .ok observation) :
    observation.accesses = instruction.accesses initial ∧
      ∀ access ∈ observation.accesses, AccessSucceeds initial access := by
  rw [step_eq_execute af decoded] at success
  exact ⟨execute_accesses success, execute_accesses_succeed success⟩

theorem step_atomic64_sound {initial final : State} {af : Bool} {label : LogicalEvent64}
    {accesses : List Access}
    (success : step af initial = .ok ⟨.atomic64 label final, accesses⟩) :
    decodeAt initial = .ok .orRdiRsi ∧ OrEffect initial af label final ∧
      accesses = [.rmw8 (initial.registers .rdi)] := by
  obtain ⟨instruction, decoded, executed⟩ := step_sound success
  obtain ⟨rfl, effect⟩ := execute_atomic64_sound executed
  exact ⟨decoded, effect, execute_accesses executed⟩

theorem step_returned_sound {initial final : State} {af : Bool} {accesses : List Access}
    (success : step af initial = .ok ⟨.returned final, accesses⟩) :
    decodeAt initial = .ok .ret ∧ RetEffect initial final ∧
      accesses = [.stack8 (initial.registers .rsp)] := by
  obtain ⟨instruction, decoded, executed⟩ := step_sound success
  obtain ⟨rfl, effect⟩ := execute_returned_sound executed
  exact ⟨decoded, effect, execute_accesses executed⟩

end EDSL.X86.LockedLogical64
