/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.ArrayMemory64
import EDSL.OS.CallResources
import EDSL.OS.Borrowing.Read64

set_option warningAsError true

namespace EDSL.OS.ArrayResources64
open X86 AddressSpace

abbrev Shared := CallResources.Shared

/-- Exact eight-byte element span; the empty span needs no allocation. -/
def arrayRegion (base : Word) (values : List Word) : Region :=
  ⟨base, 8 * values.length⟩

/-- Array handles extend the ordinary immutable code/caller-slot handles. -/
structure Call extends CallResources.Call where
  base : Word
  values : List Word
  inputLoan : Nat

def Call.inputRegion (call : Call) : Region := arrayRegion call.base call.values

/-- Current observations and authority, with no future execution premise.
Compatible read-only aliases may share regions and loan IDs. Empty input
requires no live input loan, allocation, alignment, or canonical base. -/
structure Contract (call : Call) (shared : Shared) : Prop where
  pureCall : CallResources.Contract call.toCall shared
  array : ArrayAt64 (toMemory shared.resources.space) call.base call.values
  bound : ArrayBound64 call.base call.values
  input : call.values ≠ [] →
    Threads.HasLoan shared call.worker call.inputLoan call.inputRegion

/-- Complete current RAM coupling, including all permission functions.
CPU features and interference assumptions are those of the pure-call bridge. -/
structure Current (call : Call) (shared : Shared) (machine : X86.State) : Prop where
  contract : Contract call shared
  coupled : machine.memory = toMemory shared.resources.space

/-- Reuse scalar call/return/branch helpers without weakening RAM coupling. -/
theorem Current.pureCall {call : Call} {shared : Shared} {machine : X86.State}
    (current : Current call shared machine) :
    CallResources.Current call.toCall shared machine :=
  ⟨current.contract.pureCall, current.coupled⟩

theorem Current.sameMemory {call : Call} {shared : Shared} {before after : X86.State}
    (current : Current call shared before) (memory : after.memory = before.memory) :
    Current call shared after := ⟨current.contract, memory.trans current.coupled⟩

theorem Current.array {call : Call} {shared : Shared} {machine : X86.State}
    (current : Current call shared machine) : ArrayAt64 machine.memory call.base call.values := by
  rw [current.coupled]
  exact current.contract.array

theorem Current.current {call : Call} {shared : Shared} {machine : X86.State}
    (current : Current call shared machine) :
    CodeAt machine.memory call.code call.bytes ∧
      readWord machine.memory call.stack = .ok call.returnAddress ∧
      ArrayAt64 machine.memory call.base call.values := by
  rw [current.coupled]
  exact ⟨current.contract.pureCall.code, current.contract.pureCall.stack, current.contract.array⟩

/-- The caller slot and code suffice for an empty input at every unused base
and input-loan ID, including an absent ID or a code/stack alias. -/
theorem Contract.of_nil {call : Call} {shared : Shared}
    (pureCall : CallResources.Contract call.toCall shared) (empty : call.values = []) :
    Contract call shared := by
  refine ⟨pureCall, ?_, ?_, ?_⟩
  · rw [empty]
    exact ArrayAt64.nil _ _
  · rw [empty]
    exact ArrayBound64.nil _
  · intro nonempty
    exact False.elim (nonempty empty)

/-- Full natural addresses for every actual element, with no truncation. -/
theorem element_address {base : Word} {values : List Word}
    (bound : ArrayBound64 base values) {index : Nat} (inside : index < values.length) :
    (base + BitVec.ofNat 64 (8 * index)).toNat = base.toNat + 8 * index :=
  bound.element_address inside

theorem element_fits {base : Word} {values : List Word}
    (bound : ArrayBound64 base values) {index : Nat} (inside : index < values.length) :
    Borrowing.Subregion (qwordRegion (base + BitVec.ofNat 64 (8 * index)))
      (arrayRegion base values) := by
  have address := element_address bound inside
  simp only [Borrowing.Subregion, qwordRegion, arrayRegion, address]
  omega

/-- The live current loan and independently specified current array contents
supply the complete eight-byte borrowing operation. -/
theorem element_loadWord64 {call : Call} {shared : Shared}
    (contract : Contract call shared) {index : Nat} {value : Word}
    (present : call.values[index]? = some value) :
    Borrowing.loadWord64 shared (Threads.principal call.worker) call.inputLoan
      (call.base + BitVec.ofNat 64 (8 * index)) = .ok value := by
  obtain ⟨inside, _⟩ := List.getElem_of_getElem? present
  have nonempty : call.values ≠ [] := by intro empty; simp [empty] at inside
  obtain ⟨loan, live, borrower, region⟩ := contract.input nonempty
  have authorized : Borrowing.authorize shared (Threads.principal call.worker)
      call.inputLoan = .ok loan := by simp [Borrowing.authorize, live, borrower]
  apply Borrowing.loadWord64_success _ _ _ _ _ loan authorized
  · rw [region]
    exact element_fits contract.bound inside
  · exact contract.array index value present

/-- All eight actual bytes, including the last element's last byte, lie in
the current input loan and are canonical. No alignment is required. -/
theorem element_bytes {call : Call} {shared : Shared}
    (contract : Contract call shared) {index offset : Nat}
    (inside : index < call.values.length) (byte : offset < 8) :
    call.inputRegion.Contains
      ((call.base + BitVec.ofNat 64 (8 * index)) + BitVec.ofNat 64 offset) ∧
    canonical ((call.base + BitVec.ofNat 64 (8 * index)) + BitVec.ofNat 64 offset) = true := by
  have nonempty : call.values ≠ [] := by intro empty; simp [empty] at inside
  obtain ⟨loan, live, _, region⟩ := contract.input nonempty
  obtain ⟨_, _, _, _, _, _, valid, _⟩ := contract.pureCall.wellFormed.2 _ _ live
  have fits : Borrowing.Subregion
      (qwordRegion (call.base + BitVec.ofNat 64 (8 * index))) loan.region := by
    rw [region]
    exact element_fits contract.bound inside
  have contained := Borrowing.qword_inside loan valid _ fits offset byte
  exact ⟨region ▸ contained, valid_contains_canonical loan.region valid _ contained⟩

/-- Structural operand evidence, independent of decoder/execution evidence. -/
def ArrayRead (call : Call) (read : Sequential.Read) : Prop :=
  read.kind = .data ∧ read.bytes = 8 ∧
    ∃ index, index < call.values.length ∧
      read.address = call.base + BitVec.ofNat 64 (8 * index)

theorem arrayRead_permission {call : Call} {shared : Shared}
    (contract : Contract call shared) {read : Sequential.Read} (footprint : ArrayRead call read) :
    ArrayResources.ReadPermission shared call.worker read := by
  obtain ⟨_, width, index, inside, address⟩ := footprint
  have nonempty : call.values ≠ [] := by intro empty; simp [empty] at inside
  obtain ⟨loan, live, borrower, region⟩ := contract.input nonempty
  refine ⟨call.inputLoan, loan, by simp [Borrowing.authorize, live, borrower], ?_⟩
  rw [width, address, region]
  exact element_fits contract.bound inside

theorem stackRead_permission {call : Call} {shared : Shared}
    (contract : Contract call shared) :
    ArrayResources.ReadPermission shared call.worker ⟨.stack, call.stack, 8⟩ :=
  (CallResources.stackRead_permission contract.pureCall).2.2.2

theorem no_empty_arrayRead {call : Call} (empty : call.values = []) (read : Sequential.Read) :
    ¬ArrayRead call read := by
  rintro ⟨_, _, index, inside, _⟩
  simp [empty] at inside

/-- The actual SIB scale exponent is three: full-width base plus eight times
the full-width index. The accessed natural address is nonwrapping. -/
theorem indexed_address {call : Call} {shared : Shared} {machine : X86.State}
    (contract : Contract call shared) (base index : Register) {position : Nat}
    (inside : position < call.values.length)
    (atBase : machine.registers base = call.base)
    (atIndex : machine.registers index = BitVec.ofNat 64 position) :
    (Sequential.Address.indexed base index 3).eval machine =
      call.base + BitVec.ofNat 64 (8 * position) ∧
    ((Sequential.Address.indexed base index 3).eval machine).toNat =
      call.base.toNat + 8 * position := by
  have indexBound : position < 2^64 := by
    have lengthBound := contract.bound.length_lt
    omega
  have shift : (BitVec.ofNat 64 position <<< 3) = BitVec.ofNat 64 (8 * position) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt indexBound, Nat.mul_comm]
  have address : (Sequential.Address.indexed base index 3).eval machine =
      call.base + BitVec.ofNat 64 (8 * position) := by
    simp only [Sequential.Address.eval, atBase, atIndex]
    change call.base + (BitVec.ofNat 64 position <<< (3 : Nat)) = _
    rw [shift]
  exact ⟨address, address ▸ element_address contract.bound inside⟩

/-- Successful execution observations have current loan authority and actual
complete operand-read success whenever their static data footprint is an array
read. This implication is a result, never a resource admission premise. -/
theorem execute_data_reads_permission {call : Call} {shared : Shared}
    {machine : X86.State} {instruction : Sequential.Instruction} {af : Bool}
    {observation : Sequential.Observation} (current : Current call shared machine)
    (footprint : ∀ read ∈ instruction.operandReads machine,
      read.kind = .data → ArrayRead call read)
    (success : Sequential.execute machine instruction af = .ok observation) :
    ∀ read ∈ observation.reads, read.kind = .data →
      ArrayResources.ReadPermission shared call.worker read ∧
        Sequential.OperandReadSucceeds machine read := by
  intro read member data
  have actual := Sequential.execute_reads success
  have contained := footprint read (actual ▸ member) data
  exact ⟨arrayRead_permission current.contract contained,
    Sequential.execute_reads_succeed success read member⟩

/-- Actual load execution is enabled by the current array and coupling. It
preserves the complete OS world, RAM, permissions and flags for either AF
choice, including when destination aliases an address register. -/
theorem loadMem64_enabled {call : Call} {shared : Shared} {before : X86.State}
    (current : Current call shared before) (destination : Register)
    (address : Sequential.Address) {position : Nat} {value : Word}
    (present : call.values[position]? = some value)
    (effective : address.eval before = call.base + BitVec.ofNat 64 (8 * position)) (af : Bool) :
    ∃ after,
      Sequential.execute before (.loadMem64 destination address) af =
        .ok ⟨.next after, [⟨.data, call.base + BitVec.ofNat 64 (8 * position), 8⟩]⟩ ∧
      Current call shared after ∧
      after.registers destination = value ∧
      (∀ register, register ≠ destination → after.registers register = before.registers register) ∧
      after.memory = before.memory ∧ after.flags = before.flags ∧
      after.rip = before.rip +
        BitVec.ofNat 64 (Sequential.Instruction.loadMem64 destination address).length ∧
      ArrayResources.ReadPermission shared call.worker
        ⟨.data, call.base + BitVec.ofNat 64 (8 * position), 8⟩ ∧
      Sequential.OperandReadSucceeds before
        ⟨.data, call.base + BitVec.ofNat 64 (8 * position), 8⟩ := by
  have observed := current.array position value present
  have loaded : loadQWord before.memory (address.eval before) = .ok value := by
    rw [effective]
    exact observed
  obtain ⟨after, executed, assigned, other, memory, flags, pc⟩ :=
    Sequential.execute_loadMem64_context af loaded
  obtain ⟨inside, _⟩ := List.getElem_of_getElem? present
  refine ⟨after, ?_, current.sameMemory memory, assigned, other, memory, flags, pc,
    arrayRead_permission current.contract ⟨rfl, rfl, position, inside, rfl⟩, ?_⟩
  · simpa only [effective] using executed
  · exact ⟨value, observed⟩

/-- Decoding the actual current bytes yields a real machine step; no future
execution or admitted postcondition is supplied as a premise. -/
theorem current_loadMem64_step {call : Call} {shared : Shared} {before : X86.State}
    {destination : Register} {address : Sequential.Address} {position : Nat} {value : Word}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.loadMem64 destination address))
    (present : call.values[position]? = some value)
    (effective : address.eval before = call.base + BitVec.ofNat 64 (8 * position)) (af : Bool) :
    ∃ after,
      Sequential.step af before =
        .ok ⟨.next after, [⟨.data, call.base + BitVec.ofNat 64 (8 * position), 8⟩]⟩ ∧
      Current call shared after ∧
      after.registers destination = value ∧
      (∀ register, register ≠ destination → after.registers register = before.registers register) ∧
      after.memory = before.memory ∧ after.flags = before.flags ∧
      after.rip = before.rip +
        BitVec.ofNat 64 (Sequential.Instruction.loadMem64 destination address).length ∧
      ArrayResources.ReadPermission shared call.worker
        ⟨.data, call.base + BitVec.ofNat 64 (8 * position), 8⟩ ∧
      Sequential.OperandReadSucceeds before
        ⟨.data, call.base + BitVec.ofNat 64 (8 * position), 8⟩ := by
  rw [Sequential.step_eq_execute af decoded]
  exact loadMem64_enabled current destination address present effective af

end EDSL.OS.ArrayResources64
