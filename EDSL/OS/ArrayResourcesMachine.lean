/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.ArrayResourcesHistory
import EDSL.X86.Sequential.Machine

namespace EDSL.OS.ArrayResources
open X86 AddressSpace

/-- The SIB address uses the entire index and base registers. This is an
equality of successful nonwrapping natural addresses, not 32-bit truncation. -/
theorem indexed_address {shared : Borrowing.State} {call : Call} {machine : X86.State}
    (contract : Contract shared call) (base index : Register) {position : Nat}
    (inside : position < call.values.length)
    (atBase : machine.registers base = call.base)
    (atIndex : machine.registers index = BitVec.ofNat 64 position) :
    (Sequential.Address.indexed base index 2).eval machine =
      call.base + BitVec.ofNat 64 (4 * position) ∧
    ((Sequential.Address.indexed base index 2).eval machine).toNat =
      call.base.toNat + 4 * position := by
  have indexBound : position < 2^64 := by
    have limit : call.base.toNat + 4 * call.values.length ≤ 2^64 := contract.bound
    omega
  have shift : (BitVec.ofNat 64 position <<< 2) = BitVec.ofNat 64 (4 * position) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt indexBound, Nat.mul_comm]
  have address : (Sequential.Address.indexed base index 2).eval machine =
      call.base + BitVec.ofNat 64 (4 * position) := by
    simp only [Sequential.Address.eval, atBase, atIndex]
    change call.base + (BitVec.ofNat 64 position <<< (2 : Nat)) = _
    rw [shift]
  exact ⟨address, address ▸ element_address contract.bound inside⟩

/-- Static operand-footprint evidence and actual generic execution metadata
yield current loan permission for every observed data read. This is a theorem
about successful execution, not an assumption in resource admission. -/
theorem execute_data_reads_permission {shared : Borrowing.State} {call : Call}
    {machine : X86.State} {instruction : Sequential.Instruction} {af : Bool}
    {observation : Sequential.Observation} (admitted : Admission shared call machine)
    (footprint : ∀ read ∈ instruction.operandReads machine,
      read.kind = .data → ArrayRead call read)
    (success : Sequential.execute machine instruction af = .ok observation) :
    ∀ read ∈ observation.reads, read.kind = .data →
      ReadPermission shared call.worker read ∧ Sequential.OperandReadSucceeds machine read := by
  intro read member data
  have actual := Sequential.execute_reads success
  have contained := footprint read (actual ▸ member) data
  exact ⟨arrayRead_permission admitted.resources contained,
    Sequential.execute_reads_succeed success read member⟩

/-- A contained ADD reads its independently specified CURRENT value and is
enabled for either undefined-AF choice. No future execution is supplied. -/
theorem addMem32_enabled {shared : Borrowing.State} {call : Call} {machine : X86.State}
    (admitted : Admission shared call machine) (destination : Register)
    (address : Sequential.Address) (af : Bool) {position : Nat} {value : BitVec 32}
    (present : call.values[position]? = some value)
    (effective : address.eval machine = call.base + BitVec.ofNat 64 (4 * position)) :
    ∃ observation, Sequential.execute machine (.addMem32 destination address) af = .ok observation ∧
      observation.reads = [⟨.data, call.base + BitVec.ofNat 64 (4 * position), 4⟩] ∧
      ∀ read ∈ observation.reads, ReadPermission shared call.worker read := by
  have loaded := admitted.current.2.2 position value present
  rw [← effective] at loaded
  rw [Sequential.execute_addMem32, loaded]
  simp only [ok_bind, pure_ok]
  refine ⟨_, rfl, by simp only [effective], ?_⟩
  intro read member
  simp only [List.mem_singleton] at member
  subst read
  obtain ⟨inside, _⟩ := List.getElem_of_getElem? present
  exact arrayRead_permission admitted.resources ⟨rfl, rfl, position, inside, effective⟩

theorem execute_ret_reads_permission {shared : Borrowing.State} {call : Call}
    {machine : X86.State} {af : Bool} {observation : Sequential.Observation}
    (admitted : Admission shared call machine) (stack : machine.registers .rsp = call.stack)
    (success : Sequential.execute machine (.legacy .ret) af = .ok observation) :
    ∀ read ∈ observation.reads, ReadPermission shared call.worker read := by
  rw [Sequential.execute_reads success]
  intro read member
  simp only [Sequential.Instruction.operandReads, List.mem_singleton] at member
  subst read
  rw [stack]
  exact stackRead_permission admitted.resources

end EDSL.OS.ArrayResources
