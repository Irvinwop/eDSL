/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.ArrayResources64
import EDSL.OS.Borrowing.Read64

set_option warningAsError true

/-!
Current-resource bridges for ordinary sequential memory-source ADD64. The
checked borrowing read is of the whole qword at the PRE-instruction effective
address, under a named live loan for the current worker's principal. Its
success checks borrower, natural-address containment and actual current RAM;
decoding or raw CPU readability alone supplies no loan authority.

The complete current RAM coupling and the pure-call environmental assumptions
are retained: stable ordinary sequential RAM, the modeled CPU canonicality and
alignment profile, ordinary RET without CET, and no asynchronous interference.
These lemmas make no Linux-kernel, concurrent-execution or source-preservation
claim. Compatible read-only aliases require no additional disjointness.
-/

namespace EDSL.OS.CallResources
open X86 X86.Sequential AddressSpace

/-- A named current checked loan read enables ADD64 for either AF choice. Both
operands are from the old CPU state, including destination/base/index aliases
and RSP. The same world retains all metadata, permissions, code and the original
caller-slot loan; a changed RSP does not rebind that slot or authorize RET there.
The final conjunct identifies the exact loan used by the checked read. -/
theorem addMem64_enabled {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (destination : Register) (address : Address)
    {identifier : Nat} {value : Word}
    (checked : Borrowing.loadWord64 shared (Threads.principal call.worker) identifier
      (address.eval before) = .ok value) (af : Bool) :
    ∃ after,
      execute before (.addMem64 destination address) af =
        .ok ⟨.next after, [⟨.data, address.eval before, 8⟩]⟩ ∧
      Current call shared after ∧
      after.registers destination = before.registers destination + value ∧
      (∀ register, register ≠ destination → after.registers register = before.registers register) ∧
      after.memory = before.memory ∧
      after.flags = addFlags64 before.flags (before.registers destination) value ∧
      after.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask ∧
      after.rip = before.rip + BitVec.ofNat 64 (Instruction.addMem64 destination address).length ∧
      loadQWord before.memory (address.eval before) = .ok value ∧
      ArrayResources.ReadPermission shared call.worker ⟨.data, address.eval before, 8⟩ ∧
      OperandReadSucceeds before ⟨.data, address.eval before, 8⟩ ∧
      ∃ loan, Borrowing.authorize shared (Threads.principal call.worker) identifier = .ok loan ∧
        Borrowing.Subregion (qwordRegion (address.eval before)) loan.region := by
  obtain ⟨loan, authorized, fits, observed⟩ := Borrowing.loadWord64_ok _ _ _ _ _ checked
  have loaded : loadQWord before.memory (address.eval before) = .ok value := by
    rw [current.coupled]
    exact observed
  obtain ⟨after, executed, assigned, other, memory, flags, pc⟩ :=
    execute_addMem64_context af loaded
  refine ⟨after, executed, current.sameMemory memory, assigned, other, memory, flags, ?_, pc,
    loaded, ⟨identifier, loan, authorized, fits⟩, ⟨value, loaded⟩, loan, authorized, fits⟩
  rw [flags]
  exact addFlags64_preserves ..

/-- Actual current decoding and a checked present loan read derive a real
machine step. No future execution or postcondition callback is a premise. -/
theorem current_addMem64_step {call : Call} {shared : Shared} {before : State}
    {destination : Register} {address : Address} {identifier : Nat} {value : Word}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.addMem64 destination address))
    (checked : Borrowing.loadWord64 shared (Threads.principal call.worker) identifier
      (address.eval before) = .ok value) (af : Bool) :
    ∃ after,
      step af before = .ok ⟨.next after, [⟨.data, address.eval before, 8⟩]⟩ ∧
      Current call shared after ∧
      after.registers destination = before.registers destination + value ∧
      (∀ register, register ≠ destination → after.registers register = before.registers register) ∧
      after.memory = before.memory ∧
      after.flags = addFlags64 before.flags (before.registers destination) value ∧
      after.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask ∧
      after.rip = before.rip + BitVec.ofNat 64 (Instruction.addMem64 destination address).length ∧
      loadQWord before.memory (address.eval before) = .ok value ∧
      ArrayResources.ReadPermission shared call.worker ⟨.data, address.eval before, 8⟩ ∧
      OperandReadSucceeds before ⟨.data, address.eval before, 8⟩ ∧
      ∃ loan, Borrowing.authorize shared (Threads.principal call.worker) identifier = .ok loan ∧
        Borrowing.Subregion (qwordRegion (address.eval before)) loan.region := by
  rw [step_eq_execute af decoded]
  exact addMem64_enabled current destination address checked af

end EDSL.OS.CallResources

namespace EDSL.OS.ArrayResources64
open X86 X86.Sequential AddressSpace

/-- Current array values and the complete current input loan enable the actual
full-width memory-source addition. No snapshot, alignment or register
nonaliasing premise is needed. Changing RSP retains the ORIGINAL caller slot. -/
theorem addMem64_enabled {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (destination : Register) (address : Address)
    {position : Nat} {value : Word} (present : call.values[position]? = some value)
    (effective : address.eval before = call.base + BitVec.ofNat 64 (8 * position)) (af : Bool) :
    ∃ after,
      execute before (.addMem64 destination address) af =
        .ok ⟨.next after, [⟨.data, call.base + BitVec.ofNat 64 (8 * position), 8⟩]⟩ ∧
      Current call shared after ∧
      after.registers destination = before.registers destination + value ∧
      (∀ register, register ≠ destination → after.registers register = before.registers register) ∧
      after.memory = before.memory ∧
      after.flags = addFlags64 before.flags (before.registers destination) value ∧
      after.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask ∧
      after.rip = before.rip + BitVec.ofNat 64 (Instruction.addMem64 destination address).length ∧
      ArrayResources.ReadPermission shared call.worker
        ⟨.data, call.base + BitVec.ofNat 64 (8 * position), 8⟩ ∧
      OperandReadSucceeds before ⟨.data, call.base + BitVec.ofNat 64 (8 * position), 8⟩ := by
  have checked : Borrowing.loadWord64 shared (Threads.principal call.worker) call.inputLoan
      (address.eval before) = .ok value := by
    rw [effective]
    exact element_loadWord64 current.contract present
  obtain ⟨after, executed, _, assigned, other, memory, flags, preserved, pc, _, _, _, _⟩ :=
    CallResources.addMem64_enabled current.pureCall destination address checked af
  obtain ⟨inside, _⟩ := List.getElem_of_getElem? present
  refine ⟨after, ?_, current.sameMemory memory, assigned, other, memory, flags, preserved, pc,
    arrayRead_permission current.contract ⟨rfl, rfl, position, inside, rfl⟩,
    value, current.array position value present⟩
  simpa only [effective] using executed

/-- Decoding actual current bytes plus present array resources yields the
actual DATA8 step and exact ADD flags for either AF choice. The same call and
shared world include all permissions and original loans after the step. -/
theorem current_addMem64_step {call : Call} {shared : Shared} {before : State}
    {destination : Register} {address : Address} {position : Nat} {value : Word}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.addMem64 destination address))
    (present : call.values[position]? = some value)
    (effective : address.eval before = call.base + BitVec.ofNat 64 (8 * position)) (af : Bool) :
    ∃ after,
      step af before =
        .ok ⟨.next after, [⟨.data, call.base + BitVec.ofNat 64 (8 * position), 8⟩]⟩ ∧
      Current call shared after ∧
      after.registers destination = before.registers destination + value ∧
      (∀ register, register ≠ destination → after.registers register = before.registers register) ∧
      after.memory = before.memory ∧
      after.flags = addFlags64 before.flags (before.registers destination) value ∧
      after.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask ∧
      after.rip = before.rip + BitVec.ofNat 64 (Instruction.addMem64 destination address).length ∧
      ArrayResources.ReadPermission shared call.worker
        ⟨.data, call.base + BitVec.ofNat 64 (8 * position), 8⟩ ∧
      OperandReadSucceeds before ⟨.data, call.base + BitVec.ofNat 64 (8 * position), 8⟩ := by
  rw [step_eq_execute af decoded]
  exact addMem64_enabled current destination address present effective af

end EDSL.OS.ArrayResources64
