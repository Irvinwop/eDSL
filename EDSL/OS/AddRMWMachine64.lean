/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicFetchAddMachine64
import EDSL.X86.AddRMW64

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.Atomics64
open X86 AddressSpace

/-- Couple the unchanged checked OS fetch-add to the instruction actually
decoded from current CPU RAM. Address and delta come from the prestate,
including XADD base/source aliases and source RSP. ADD/INC have no source
writeback; their complete old/delta/new response still identifies one RMW8.

This is an abstract coherent-WB-RAM bridge under the existing long-mode,
CET-disabled, stable-translation/no-alias and protected-resource assumptions.
It proves neither physical LOCK refinement nor an unrestricted kernel step. -/
theorem addRmw_step (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (initial : X86.State)
    (instruction : AddRMW64.Instruction) (result : State × FetchAddEvent)
    (success : fetchAdd state actor identifier (instruction.delta initial) = .ok result)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers instruction.base = cell.address)
    (decoded : AddRMW64.decodeAt initial = .ok instruction) :
    AddRMW64.step initial = .ok ⟨result.2.arithmetic,
      AddRMW64.afterRmw initial instruction (toMemory result.1.legacy.shared.resources.space)
        result.2.arithmetic, [.rmw8 cell.address]⟩ := by
  have identity := fetchAdd_identity _ _ _ _ _ _ _ success authorized
  have data := (authorize_ok _ _ _ _ authorized).2.2.2.2.2
  have primitive := fetchAdd_primitive _ _ _ _ _ success
  rw [identity.2] at primitive
  rw [AddRMW64.step_eq_execute decoded]
  simp [AddRMW64.execute, memory, operand, data, primitive, AddRMW64.Instruction.accesses]

/-- Present WellFormed, current authority, base/cell binding and fetched code
derive both successes for the captured delta. No desired old value, successor
or future successful OS/CPU transition is a premise. -/
theorem addRmw_step_enabled (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (initial : X86.State)
    (instruction : AddRMW64.Instruction) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers instruction.base = cell.address)
    (decoded : AddRMW64.decodeAt initial = .ok instruction) :
    ∃ result, fetchAdd state actor identifier (instruction.delta initial) = .ok result ∧
      AddRMW64.step initial = .ok ⟨result.2.arithmetic,
        AddRMW64.afterRmw initial instruction (toMemory result.1.legacy.shared.resources.space)
          result.2.arithmetic, [.rmw8 cell.address]⟩ := by
  obtain ⟨result, success⟩ := fetchAdd_enabled _ _ _ _ _ _ valid authorized
  exact ⟨result, success, addRmw_step _ _ _ _ _ _ _ _ success authorized memory operand decoded⟩

/-- Current CodeAt supplies exactly the decoded instruction's four or five
bytes. In particular INC needs no executable fifth byte. -/
theorem addRmw_step_enabled_of_code (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (initial : X86.State)
    (instruction : AddRMW64.Instruction) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers instruction.base = cell.address)
    (code : CodeAt initial.memory initial.rip instruction.bytes) :
    ∃ result, fetchAdd state actor identifier (instruction.delta initial) = .ok result ∧
      AddRMW64.step initial = .ok ⟨result.2.arithmetic,
        AddRMW64.afterRmw initial instruction (toMemory result.1.legacy.shared.resources.space)
          result.2.arithmetic, [.rmw8 cell.address]⟩ :=
  addRmw_step_enabled _ _ _ _ _ _ _ valid authorized memory operand
    (AddRMW64.decodeAt_of_code instruction code)

/-- The actual checked OS call, current decode/code/step, complete arithmetic
event, whole initial/final RAM projections and exact singleton access agree.
Actor, handle and cell identities remain OS identities, independent of any
scheduler tid. The CPU effect uses an optional old-value destination. -/
structure AddRMWMachineEffect (before : State) (actor : Nat) (identifier : HandleId64)
    (initial : X86.State) (instruction : AddRMW64.Instruction)
    (result : State × FetchAddEvent) (observation : AddRMW64.Observation) : Prop where
  checked : fetchAdd before actor identifier (instruction.delta initial) = .ok result
  initialMemory : initial.memory = toMemory before.legacy.shared.resources.space
  decoded : AddRMW64.decodeAt initial = .ok instruction
  code : CodeAt initial.memory initial.rip instruction.bytes
  step : AddRMW64.step initial = .ok observation
  event : observation.event = result.2.arithmetic
  memory : observation.state.memory = toMemory result.1.legacy.shared.resources.space
  os : FetchAddEffect before result.1 result.2
  cpu : AddRMW64.Effect initial instruction result.2.arithmetic observation.state
  accesses : observation.accesses = [.rmw8 result.2.arithmetic.event.address]

theorem addRmw_step_effect (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (initial : X86.State)
    (instruction : AddRMW64.Instruction) (result : State × FetchAddEvent)
    (success : fetchAdd state actor identifier (instruction.delta initial) = .ok result)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers instruction.base = cell.address)
    (decoded : AddRMW64.decodeAt initial = .ok instruction) :
    AddRMWMachineEffect state actor identifier initial instruction result
      ⟨result.2.arithmetic, AddRMW64.afterRmw initial instruction
        (toMemory result.1.legacy.shared.resources.space) result.2.arithmetic, [.rmw8 cell.address]⟩ := by
  have dispatch := addRmw_step _ _ _ _ _ _ _ _ success authorized memory operand decoded
  have executed := dispatch
  rw [AddRMW64.step_eq_execute decoded] at executed
  have identity := fetchAdd_identity _ _ _ _ _ _ _ success authorized
  exact ⟨success, memory, decoded, AddRMW64.decodeAt_code decoded, dispatch, rfl, rfl,
    fetchAdd_effect _ _ _ _ _ success, (AddRMW64.execute_sound executed).1,
    by simp only [identity.2]⟩

/-- Converse for an actual current CPU step. Operand binding is required for
the instruction actually decoded, and the OS input is its prestate delta.
Neither old-value writeback nor a source-register oracle is required. -/
theorem step_addRmw (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (initial : X86.State)
    (observation : AddRMW64.Observation) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : ∀ instruction, AddRMW64.decodeAt initial = .ok instruction →
      initial.registers instruction.base = cell.address)
    (success : AddRMW64.step initial = .ok observation) :
    ∃ instruction result,
      AddRMWMachineEffect state actor identifier initial instruction result observation := by
  obtain ⟨instruction, decoded, _, _, _, _⟩ := AddRMW64.step_sound success
  obtain ⟨result, changed, dispatch⟩ := addRmw_step_enabled _ _ _ _ _ _ _ valid authorized
    memory (operand instruction decoded) decoded
  have same := Except.ok.inj (dispatch.symm.trans success)
  subst observation
  exact ⟨instruction, result, addRmw_step_effect _ _ _ _ _ _ _ _ changed authorized
    memory (operand instruction decoded) decoded⟩

namespace AddRMWMachineEffect
section Generic
variable {before : State} {actor : Nat} {identifier : HandleId64}
  {initial : X86.State} {instruction : AddRMW64.Instruction}
  {result : State × FetchAddEvent} {observation : AddRMW64.Observation}
  (effect : AddRMWMachineEffect before actor identifier initial instruction result observation)
include effect

theorem wellFormed (valid : WellFormed before) : WellFormed result.1 :=
  fetchAdd_wellFormed _ _ _ _ _ valid effect.checked

/-- Allocation identity, owner, epoch and region are retained, together with
the registries, loan records and frontiers in effect.os. -/
theorem current (owner : Nat) (ticket : Ownership.Ticket) :
    Ownership.Current result.1.legacy.shared.resources owner ticket ↔
      Ownership.Current before.legacy.shared.resources owner ticket :=
  fetchAdd_current_retained _ _ _ _ _ effect.checked owner ticket

theorem context : ∃ handle cell,
    before.handles identifier = some handle ∧ handle.actor = actor ∧
      before.cells handle.cell = some cell ∧ ValidCell before.legacy.shared cell ∧
      result.2.cell = handle.cell ∧ result.2.arithmetic.event.address = cell.address :=
  fetchAdd_context _ _ _ _ _ effect.checked

theorem actor_handle : result.2.actor = actor ∧ result.2.handle = identifier :=
  (fetchAdd_sound _ _ _ _ _ effect.checked).2.2.2

theorem reserved (valid : WellFormed before) (cellId : CellId64) (cell : Cell)
    (live : before.cells cellId = some cell) :
    EDSL.OS.Atomics64.reserved result.1 cell.ticket.identifier = true :=
  fetchAdd_reserved _ _ _ _ _ valid effect.checked cellId cell live

theorem blocks_mutation (valid : WellFormed before) (cellId : CellId64) (cell : Cell)
    (live : before.cells cellId = some cell) (operation : Ownership.Mutation)
    (target : operation.target = some cell.ticket.identifier) :
    mutate result.1 operation = .error .reserved :=
  fetchAdd_blocks_mutation _ _ _ _ _ valid effect.checked cellId cell live operation target

theorem authority_retained (valid : WellFormed before) (otherActor : Nat) (otherId : HandleId64)
    (handle : Handle) (cell : Cell) (live : before.handles otherId = some handle)
    (acts : handle.actor = otherActor) (linked : before.cells handle.cell = some cell) :
    authorize result.1 otherActor otherId = .ok (handle, cell) :=
  fetchAdd_authority_retained _ _ _ _ _ valid effect.checked otherActor otherId handle cell live acts linked

theorem delta : result.2.arithmetic.delta = instruction.delta initial := effect.cpu.delta

theorem rip : observation.state.rip = initial.rip + BitVec.ofNat 64 instruction.length := effect.cpu.rip

theorem flags : observation.state.flags = instruction.flagsAfter initial.flags
    result.2.arithmetic.event.before (instruction.delta initial) := effect.cpu.flags

theorem nonarithmetic_flags : observation.state.flags &&& ~~~arithmeticFlagMask =
    initial.flags &&& ~~~arithmeticFlagMask := effect.cpu.nonarithmetic_flags

/-- Only an actual old-value destination is exempt from this frame. ADD/INC
preserve all GPRs; arbitrary XADD sources retain their existing ABI limits. -/
theorem register_frame (register : Register) (other : instruction.oldDestination ≠ some register) :
    observation.state.registers register = initial.registers register :=
  effect.cpu.register_frame register other

theorem all_registers (noDestination : instruction.oldDestination = none) :
    observation.state.registers = initial.registers := effect.cpu.all_registers noDestination

theorem preserves_all_code (base : Word) (bytes : List Byte)
    (code : CodeAt initial.memory base bytes) :
    CodeAt observation.state.memory base bytes := effect.cpu.preserves_all_code base bytes code

theorem permissions : observation.state.memory.executable = initial.memory.executable ∧
    observation.state.memory.writable = initial.memory.writable := effect.cpu.permissions

/-- The current full eight bytes are present, readable, writable and
nonexecutable, even when the modular result equals the old word. -/
theorem full_permissions (offset : Nat) (bound : offset < 8) :
    let address := result.2.arithmetic.event.address + BitVec.ofNat 64 offset
    initial.memory.writable address = true ∧ (initial.memory.read address).isSome = true ∧
      initial.memory.executable address = false := by
  rw [effect.initialMemory]
  exact fetchAdd_full_permissions _ _ _ _ _ effect.checked offset bound

theorem frame (query : Word) (outside : 8 ≤ (query - result.2.arithmetic.event.address).toNat) :
    observation.state.memory.read query = initial.memory.read query := effect.cpu.frame query outside

theorem loan_contents (valid : WellFormed before) (loanId : Nat) (loan : Borrowing.Loan)
    (live : before.legacy.shared.loans loanId = some loan) :
    ∀ query, loan.region.Contains query →
      result.1.legacy.shared.resources.space.cells query = before.legacy.shared.resources.space.cells query :=
  fetchAdd_loan_contents _ _ _ _ _ valid effect.checked loanId loan live

theorem loan_read (valid : WellFormed before) (borrower loanId : Nat) (address value : Word)
    (read : Borrowing.loadWord64 before.legacy.shared borrower loanId address = .ok value) :
    Borrowing.loadWord64 result.1.legacy.shared borrower loanId address = .ok value ∧
      loadQWord observation.state.memory address = .ok value ∧
      readWord observation.state.memory address = .ok value := by
  have retained := fetchAdd_loan_read _ _ _ _ _ valid effect.checked borrower loanId address value read
  have observed := (Borrowing.loadWord64_ok _ _ _ _ _ retained).choose_spec.2.2
  rw [← effect.memory] at observed
  exact ⟨retained, observed, readWord_of_loadQWord _ _ _ observed⟩

/-- Even when XADD writes RSP, the ORIGINAL caller resource and contents at
the original address survive. This does not establish RET enabledness. -/
theorem original_caller_loan (valid : WellFormed before) (borrower loanId : Nat) (value : Word)
    (read : Borrowing.loadWord64 before.legacy.shared borrower loanId
      (initial.registers .rsp) = .ok value) :
    Borrowing.loadWord64 result.1.legacy.shared borrower loanId (initial.registers .rsp) = .ok value ∧
      loadQWord observation.state.memory (initial.registers .rsp) = .ok value ∧
      readWord observation.state.memory (initial.registers .rsp) = .ok value :=
  effect.loan_read valid borrower loanId _ value read

/-- The original loan bounds remain authoritative. A changed RSP or readable
replacement address does not create replacement-slot authority. -/
theorem outside_original_loan (borrower loanId : Nat) (loan : Borrowing.Loan) (address : Word)
    (authorized : Borrowing.authorize before.legacy.shared borrower loanId = .ok loan)
    (outside : ¬Borrowing.Subregion (qwordRegion address) loan.region) :
    Borrowing.loadWord64 result.1.legacy.shared borrower loanId address = .error .outsideLoan := by
  obtain ⟨live, owns⟩ := Borrowing.authorize_ok _ _ _ _ authorized
  have retained : Borrowing.authorize result.1.legacy.shared borrower loanId = .ok loan := by
    simp [Borrowing.authorize, effect.os.shared.loans, live, owns]
  simp [Borrowing.loadWord64, retained, outside, Except.mapError]

end Generic

/-- Explicit XADD compatibility recovers the entire legacy joint effect,
including its exact source/flags/length contracts, without changing old APIs.
It asserts tagged successful decoding, not global decoder equality. -/
theorem xadd_iff {before : State} {actor : Nat} {identifier : HandleId64}
    {initial : X86.State} {old : LockedAdd64.Instruction}
    {result : State × FetchAddEvent} {observation : AddRMW64.Observation} :
    AddRMWMachineEffect before actor identifier initial (.xadd old) result observation ↔
      FetchAddMachineEffect before actor identifier initial old result observation := by
  constructor
  · intro effect
    have decoded := (AddRMW64.decodeAt_xadd_iff initial old).mp effect.decoded
    exact ⟨effect.checked, effect.initialMemory, decoded, effect.code,
      (AddRMW64.step_xadd decoded).symm.trans effect.step, effect.event, effect.memory,
      effect.os, (AddRMW64.effect_xadd_iff initial old _ _).mp effect.cpu, effect.accesses⟩
  · intro effect
    exact ⟨effect.checked, effect.initialMemory,
      (AddRMW64.decodeAt_xadd_iff initial old).mpr effect.decoded, effect.code,
      (AddRMW64.step_xadd effect.decoded).trans effect.step, effect.event, effect.memory,
      effect.os, (AddRMW64.effect_xadd_iff initial old _ _).mpr effect.cpu, effect.accesses⟩

theorem xadd {before : State} {actor : Nat} {identifier : HandleId64}
    {initial : X86.State} {old : LockedAdd64.Instruction}
    {result : State × FetchAddEvent} {observation : AddRMW64.Observation}
    (effect : AddRMWMachineEffect before actor identifier initial (.xadd old) result observation) :
    FetchAddMachineEffect before actor identifier initial old result observation := xadd_iff.mp effect

/-- Old-source writeback exists only under the XADD tag, including aliases/RSP. -/
theorem source_old {before : State} {actor : Nat} {identifier : HandleId64}
    {initial : X86.State} {old : LockedAdd64.Instruction}
    {result : State × FetchAddEvent} {observation : AddRMW64.Observation}
    (effect : AddRMWMachineEffect before actor identifier initial (.xadd old) result observation) :
    observation.state.registers old.source = result.2.arithmetic.event.before := effect.xadd.source_old

theorem addImm8_registers {before : State} {actor : Nat} {identifier : HandleId64}
    {initial : X86.State} {encoding : AddRMW64.AddImm8Encoding}
    {result : State × FetchAddEvent} {observation : AddRMW64.Observation}
    (effect : AddRMWMachineEffect before actor identifier initial (.addImm8 encoding) result observation) :
    observation.state.registers = initial.registers := effect.all_registers rfl

theorem inc_registers {before : State} {actor : Nat} {identifier : HandleId64}
    {initial : X86.State} {encoding : AddRMW64.IncEncoding}
    {result : State × FetchAddEvent} {observation : AddRMW64.Observation}
    (effect : AddRMWMachineEffect before actor identifier initial (.inc encoding) result observation) :
    observation.state.registers = initial.registers := effect.all_registers rfl

theorem inc_carry {before : State} {actor : Nat} {identifier : HandleId64}
    {initial : X86.State} {encoding : AddRMW64.IncEncoding}
    {result : State × FetchAddEvent} {observation : AddRMW64.Observation}
    (effect : AddRMWMachineEffect before actor identifier initial (.inc encoding) result observation) :
    observation.state.flags.getLsbD 0 = initial.flags.getLsbD 0 := effect.cpu.inc_carry

end AddRMWMachineEffect
end EDSL.OS.Atomics64
