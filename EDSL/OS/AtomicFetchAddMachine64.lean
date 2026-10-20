/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicFetchAdd64
import EDSL.X86.LockedAdd64.Machine
import EDSL.X86.StackRead64

namespace EDSL.OS.Atomics64
open X86 AddressSpace

/-- Current OS authority and actual instruction dispatch agree on the complete
typed arithmetic response, whole RAM, source write, ADD flags and one RMW8.
Both operands are captured from the prestate, including base/source aliases
and source RSP. The CPU memory must be the CURRENT OS projection.

This is the abstract locked-family semantics. Its long-mode, CET-disabled,
WB/translation/alias and managed-access environmental obligations remain those
of LockedAdd64 and atomicAddressable64; no physical LOCK refinement is proved. -/
theorem fetchAdd_step (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (initial : X86.State)
    (instruction : LockedAdd64.Instruction) (result : State × FetchAddEvent)
    (success : fetchAdd state actor identifier (initial.registers instruction.source) = .ok result)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers instruction.base = cell.address)
    (decoded : LockedAdd64.decodeAt initial = .ok instruction) :
    LockedAdd64.step initial = .ok ⟨result.2.arithmetic,
      LockedAdd64.afterAdd initial instruction (toMemory result.1.legacy.shared.resources.space)
        result.2.arithmetic, [.rmw8 cell.address]⟩ := by
  have identity := fetchAdd_identity _ _ _ _ _ _ _ success authorized
  have data := (authorize_ok _ _ _ _ authorized).2.2.2.2.2
  have primitive := fetchAdd_primitive _ _ _ _ _ success
  rw [identity.2] at primitive
  rw [LockedAdd64.step_eq_execute decoded]
  simp [LockedAdd64.execute, memory, operand, data, primitive,
    LockedAdd64.Instruction.accesses]

/-- Enabledness derives both successful operations from present invariants,
live actor/handle/cell authorization (including current owner and epoch), and
current fetched code. No future successful mutation is assumed. -/
theorem fetchAdd_step_enabled (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (initial : X86.State)
    (instruction : LockedAdd64.Instruction) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers instruction.base = cell.address)
    (decoded : LockedAdd64.decodeAt initial = .ok instruction) :
    ∃ result, fetchAdd state actor identifier (initial.registers instruction.source) = .ok result ∧
      LockedAdd64.step initial = .ok ⟨result.2.arithmetic,
        LockedAdd64.afterAdd initial instruction (toMemory result.1.legacy.shared.resources.space)
          result.2.arithmetic, [.rmw8 cell.address]⟩ := by
  obtain ⟨result, success⟩ := fetchAdd_enabled _ _ _ _ _ _ valid authorized
  exact ⟨result, success, fetchAdd_step _ _ _ _ _ _ _ _ success authorized memory operand decoded⟩

theorem fetchAdd_step_enabled_of_code (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (initial : X86.State)
    (instruction : LockedAdd64.Instruction) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers instruction.base = cell.address)
    (code : CodeAt initial.memory initial.rip instruction.bytes) :
    ∃ result, fetchAdd state actor identifier (initial.registers instruction.source) = .ok result ∧
      LockedAdd64.step initial = .ok ⟨result.2.arithmetic,
        LockedAdd64.afterAdd initial instruction (toMemory result.1.legacy.shared.resources.space)
          result.2.arithmetic, [.rmw8 cell.address]⟩ :=
  fetchAdd_step_enabled _ _ _ _ _ _ _ valid authorized memory operand
    (LockedAdd64.decodeAt_of_code instruction code)

/-- Reusable joint effect. The OS response retains actor, handle and cell
identity, while the machine response remains FetchAddEvent64 throughout. -/
structure FetchAddMachineEffect (before : State) (actor : Nat) (identifier : HandleId64)
    (initial : X86.State) (instruction : LockedAdd64.Instruction)
    (result : State × FetchAddEvent) (observation : LockedAdd64.Observation) : Prop where
  checked : fetchAdd before actor identifier (initial.registers instruction.source) = .ok result
  initialMemory : initial.memory = toMemory before.legacy.shared.resources.space
  decoded : LockedAdd64.decodeAt initial = .ok instruction
  code : CodeAt initial.memory initial.rip instruction.bytes
  step : LockedAdd64.step initial = .ok observation
  event : observation.event = result.2.arithmetic
  memory : observation.state.memory = toMemory result.1.legacy.shared.resources.space
  os : FetchAddEffect before result.1 result.2
  cpu : LockedAdd64.Effect initial instruction result.2.arithmetic observation.state
  accesses : observation.accesses = [.rmw8 result.2.arithmetic.event.address]

theorem fetchAdd_step_effect (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (initial : X86.State)
    (instruction : LockedAdd64.Instruction) (result : State × FetchAddEvent)
    (success : fetchAdd state actor identifier (initial.registers instruction.source) = .ok result)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers instruction.base = cell.address)
    (decoded : LockedAdd64.decodeAt initial = .ok instruction) :
    FetchAddMachineEffect state actor identifier initial instruction result
      ⟨result.2.arithmetic, LockedAdd64.afterAdd initial instruction
        (toMemory result.1.legacy.shared.resources.space) result.2.arithmetic, [.rmw8 cell.address]⟩ := by
  have dispatch := fetchAdd_step _ _ _ _ _ _ _ _ success authorized memory operand decoded
  have executed := dispatch
  rw [LockedAdd64.step_eq_execute decoded] at executed
  have identity := fetchAdd_identity _ _ _ _ _ _ _ success authorized
  exact ⟨success, memory, decoded, LockedAdd64.decodeAt_code decoded, dispatch, rfl, rfl,
    fetchAdd_effect _ _ _ _ _ success, (LockedAdd64.execute_sound executed).1,
    by simp only [identity.2]⟩

/-- Converse from actual fetch/decode/step. Operand binding is checked for the
instruction actually decoded, never for a supplied expected body. The delta is
the prestate SOURCE register, never reconstructed by subtracting event values. -/
theorem step_fetchAdd (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (initial : X86.State)
    (observation : LockedAdd64.Observation) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : ∀ instruction, LockedAdd64.decodeAt initial = .ok instruction →
      initial.registers instruction.base = cell.address)
    (success : LockedAdd64.step initial = .ok observation) :
    ∃ instruction result,
      FetchAddMachineEffect state actor identifier initial instruction result observation := by
  obtain ⟨instruction, decoded, _, _, _, _⟩ := LockedAdd64.step_sound success
  obtain ⟨result, changed, dispatch⟩ := fetchAdd_step_enabled _ _ _ _ _ _ _ valid authorized
    memory (operand instruction decoded) decoded
  have same := Except.ok.inj (dispatch.symm.trans success)
  subst observation
  exact ⟨instruction, result, fetchAdd_step_effect _ _ _ _ _ _ _ _ changed authorized
    memory (operand instruction decoded) decoded⟩

namespace FetchAddMachineEffect
variable {before : State} {actor : Nat} {identifier : HandleId64}
  {initial : X86.State} {instruction : LockedAdd64.Instruction}
  {result : State × FetchAddEvent} {observation : LockedAdd64.Observation}
  (effect : FetchAddMachineEffect before actor identifier initial instruction result observation)
include effect

theorem wellFormed (valid : WellFormed before) : WellFormed result.1 :=
  fetchAdd_wellFormed _ _ _ _ _ valid effect.checked

/-- All allocation records (owner/epoch/region), registries, loan records and
frontiers are retained by effect.os; Current is consequently an equivalence. -/
theorem current (owner : Nat) (ticket : Ownership.Ticket) :
    Ownership.Current result.1.legacy.shared.resources owner ticket ↔
      Ownership.Current before.legacy.shared.resources owner ticket :=
  fetchAdd_current_retained _ _ _ _ _ effect.checked owner ticket

theorem context : ∃ handle cell,
    before.handles identifier = some handle ∧ handle.actor = actor ∧
      before.cells handle.cell = some cell ∧ ValidCell before.legacy.shared cell ∧
      result.2.cell = handle.cell ∧ result.2.arithmetic.event.address = cell.address :=
  fetchAdd_context _ _ _ _ _ effect.checked

theorem delta : result.2.arithmetic.delta = initial.registers instruction.source := effect.cpu.delta

theorem rip : observation.state.rip = initial.rip + 5 := effect.cpu.rip

theorem flags : observation.state.flags = Sequential.addFlags64 initial.flags
    result.2.arithmetic.event.before (initial.registers instruction.source) := effect.cpu.flags

theorem source_old : observation.state.registers instruction.source =
    result.2.arithmetic.event.before := effect.cpu.source_old

/-- Only the actual source register is exempt from the register frame. No
general ABI promise is made for arbitrary callee-saved sources or source RSP. -/
theorem register_frame (register : Register) (other : register ≠ instruction.source) :
    observation.state.registers register = initial.registers register :=
  effect.cpu.register_frame register other

theorem preserves_all_code (base : Word) (bytes : List Byte)
    (code : CodeAt initial.memory base bytes) :
    CodeAt observation.state.memory base bytes := effect.cpu.preserves_all_code base bytes code

theorem permissions : observation.state.memory.executable = initial.memory.executable ∧
    observation.state.memory.writable = initial.memory.writable := effect.cpu.permissions

theorem frame (query : Word) (outside : 8 ≤ (query - result.2.arithmetic.event.address).toNat) :
    observation.state.memory.read query = initial.memory.read query := effect.cpu.frame query outside

theorem loan_read (valid : WellFormed before) (borrower loanId : Nat) (address value : Word)
    (read : Borrowing.loadWord64 before.legacy.shared borrower loanId address = .ok value) :
    Borrowing.loadWord64 result.1.legacy.shared borrower loanId address = .ok value ∧
      loadQWord observation.state.memory address = .ok value ∧
      readWord observation.state.memory address = .ok value := by
  have retained := fetchAdd_loan_read _ _ _ _ _ valid effect.checked borrower loanId address value read
  have observed := (Borrowing.loadWord64_ok _ _ _ _ _ retained).choose_spec.2.2
  rw [← effect.memory] at observed
  exact ⟨retained, observed, readWord_of_loadQWord _ _ _ observed⟩

/-- A source-RSP write still preserves the ORIGINAL caller resource and its
contents at the original address. It neither preserves RSP nor enables RET. -/
theorem original_caller_loan (valid : WellFormed before) (borrower loanId : Nat) (value : Word)
    (read : Borrowing.loadWord64 before.legacy.shared borrower loanId
      (initial.registers .rsp) = .ok value) :
    Borrowing.loadWord64 result.1.legacy.shared borrower loanId (initial.registers .rsp) = .ok value ∧
      loadQWord observation.state.memory (initial.registers .rsp) = .ok value ∧
      readWord observation.state.memory (initial.registers .rsp) = .ok value :=
  effect.loan_read valid borrower loanId _ value read

/-- No replacement-slot authority is created. This holds even if raw RAM at
the new source-RSP value happens to be readable: the ORIGINAL loan bounds apply. -/
theorem outside_original_loan (borrower loanId : Nat) (loan : Borrowing.Loan) (address : Word)
    (authorized : Borrowing.authorize before.legacy.shared borrower loanId = .ok loan)
    (outside : ¬Borrowing.Subregion (qwordRegion address) loan.region) :
    Borrowing.loadWord64 result.1.legacy.shared borrower loanId address = .error .outsideLoan := by
  obtain ⟨live, owns⟩ := Borrowing.authorize_ok _ _ _ _ authorized
  have retained : Borrowing.authorize result.1.legacy.shared borrower loanId = .ok loan := by
    simp [Borrowing.authorize, effect.os.shared.loans, live, owns]
  simp [Borrowing.loadWord64, retained, outside, Except.mapError]

end FetchAddMachineEffect
end EDSL.OS.Atomics64
