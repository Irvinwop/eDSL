/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.BufferCall.Contract
import EDSL.OS.CallResources
import EDSL.OS.Borrowing.Read64
import EDSL.Grading.ReadOnlyTask.Core

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.BufferCall
open X86 X86.Sequential OS

/-- Exact natural byte extent; an empty extent has no resource requirement. -/
def Buffer.region (buffer : Buffer) : AddressSpace.Region :=
  ⟨buffer.base, buffer.bytes.length⟩

structure Resources (spec : Spec) where
  shared : Borrowing.State
  call : CallResources.Call
  value : spec.Input
  inputLoan : Buffer → Nat

def resourceInput {spec : Spec} (resource : Resources spec) : Invocation spec :=
  ⟨resource.value, resource.call.returnAddress⟩

/-- Current manager resources and current byte snapshots, with no future-run
premise. Read-only overlaps and identical loan IDs for compatible identical
extents are admitted. An empty snapshot never consults its input-loan ID. -/
structure ResourceContract {spec : Spec} (resource : Resources spec)
    (shared : Borrowing.State) : Prop where
  call : CallResources.Contract resource.call shared
  buffers : ∀ buffer ∈ spec.buffers resource.value,
    BufferAt (AddressSpace.toMemory shared.resources.space) buffer.base buffer.bytes
  inputs : ∀ buffer ∈ spec.buffers resource.value, buffer.bytes ≠ [] →
    Threads.HasLoan shared resource.call.worker (resource.inputLoan buffer) buffer.region

/-- Complete current RAM, readable/writable/executable permissions included. -/
structure Current {spec : Spec} (resource : Resources spec) (machine : State) : Prop where
  contract : ResourceContract resource resource.shared
  coupled : machine.memory = AddressSpace.toMemory resource.shared.resources.space

structure ResourcePre (spec : Spec) (bytes : List Byte)
    (resource : Resources spec) (initial : State) : Prop where
  current : Current resource initial
  code : resource.call.bytes = bytes
  entry : initial.rip = resource.call.code
  stack : initial.registers .rsp = resource.call.stack
  domain : spec.domain resource.value
  arguments : Bound spec resource.value initial

theorem Current.sameMemory {spec : Spec} {resource : Resources spec} {before after : State}
    (current : Current resource before) (memory : after.memory = before.memory) :
    Current resource after := ⟨current.contract, memory.trans current.coupled⟩

theorem Current.pureCall {spec : Spec} {resource : Resources spec} {machine : State}
    (current : Current resource machine) :
    CallResources.Current resource.call resource.shared machine :=
  ⟨current.contract.call, current.coupled⟩

theorem Current.buffer {spec : Spec} {resource : Resources spec} {machine : State}
    (current : Current resource machine) {buffer : Buffer}
    (member : buffer ∈ spec.buffers resource.value) :
    BufferAt machine.memory buffer.base buffer.bytes := by
  rw [current.coupled]
  exact current.contract.buffers buffer member

/-- Empty inputs need only the original call resources, for arbitrary bases
and arbitrary unused input-loan IDs. No allocation or pointer test is hidden. -/
theorem ResourceContract.of_empty {spec : Spec} {resource : Resources spec}
    {shared : Borrowing.State} (call : CallResources.Contract resource.call shared)
    (empty : ∀ buffer ∈ spec.buffers resource.value, buffer.bytes = []) :
    ResourceContract resource shared := by
  refine ⟨call, ?_, ?_⟩
  · intro buffer member
    rw [empty buffer member]
    exact Buffer.empty _ _
  · intro buffer member nonempty
    exact False.elim (nonempty (empty buffer member))

theorem ResourcePre.machine {spec : Spec} {bytes : List Byte} {resource : Resources spec}
    {initial : State} (pre : ResourcePre spec bytes resource initial) :
    Pre spec bytes (resourceInput resource) initial := by
  have contract := pre.current.contract.call
  refine ⟨pre.domain, pre.arguments, ?_, ?_, ?_, contract.returnCanonical, ?_, ?_⟩
  · intro buffer member
    exact pre.current.buffer member
  · rw [pre.current.coupled, pre.entry, ← pre.code]
    exact contract.code
  · rw [pre.current.coupled, pre.stack]
    exact contract.stack
  · rw [pre.stack]
    exact contract.stackBound
  · rw [pre.stack]
    exact contract.postStackCanonical

/-- Exact, nontruncated natural addresses throughout a readable snapshot. -/
theorem Buffer.offset_address {memory : Memory} {buffer : Buffer}
    (snapshot : BufferAt memory buffer.base buffer.bytes) {offset : Nat}
    (inside : offset < buffer.bytes.length) :
    (buffer.base + BitVec.ofNat 64 offset).toNat = buffer.base.toNat + offset := by
  have bound := snapshot.1
  have small : offset < 2^64 := by omega
  have sum : buffer.base.toNat + offset < 2^64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt sum]

theorem Buffer.offset_inside {memory : Memory} {buffer : Buffer}
    (snapshot : BufferAt memory buffer.base buffer.bytes) {offset : Nat}
    (inside : offset < buffer.bytes.length) :
    buffer.region.Contains (buffer.base + BitVec.ofNat 64 offset) := by
  change buffer.base.toNat ≤ (buffer.base + BitVec.ofNat 64 offset).toNat ∧
    (buffer.base + BitVec.ofNat 64 offset).toNat < buffer.base.toNat + buffer.bytes.length
  rw [buffer.offset_address snapshot inside]
  omega

theorem Buffer.span_nonempty {buffer : Buffer} {address : Word} {width : Nat}
    (span : buffer.Contains address width) : buffer.bytes ≠ [] := by
  intro empty
  obtain ⟨positive, lower, upper⟩ := span
  rw [empty] at upper
  simp only [List.length_nil, Nat.add_zero] at upper
  omega

theorem Buffer.span_fits {buffer : Buffer} {address : Word} {width : Nat}
    (span : buffer.Contains address width) :
    Borrowing.Subregion ⟨address, width⟩ buffer.region := span.2

/-- Every byte of a positive contained operand is inside the natural snapshot,
including the final byte. A readable neighbor cannot enlarge the span. -/
theorem Buffer.span_byte {memory : Memory} {buffer : Buffer}
    (snapshot : BufferAt memory buffer.base buffer.bytes) {address : Word} {width offset : Nat}
    (span : buffer.Contains address width) (byte : offset < width) :
    buffer.region.Contains (address + BitVec.ofNat 64 offset) := by
  obtain ⟨positive, lower, upper⟩ := span
  have bound := snapshot.1
  have small : offset < 2^64 := by omega
  have sum : address.toNat + offset < 2^64 := by omega
  change buffer.base.toNat ≤ (address + BitVec.ofNat 64 offset).toNat ∧
    (address + BitVec.ofNat 64 offset).toNat < buffer.base.toNat + buffer.bytes.length
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt sum]
  omega

/-- A permitted buffer read has actual present borrowing authority. -/
theorem ResourceContract.dataRead_permission {spec : Spec} {resource : Resources spec}
    {shared : Borrowing.State} (contract : ResourceContract resource shared) {read : Read}
    (footprint : DataRead (spec.buffers resource.value) read) :
    ArrayResources.ReadPermission shared resource.call.worker read := by
  obtain ⟨_, buffer, member, span⟩ := footprint
  obtain ⟨loan, live, borrower, region⟩ := contract.inputs buffer member (Buffer.span_nonempty span)
  exact ⟨resource.inputLoan buffer, loan, by simp [Borrowing.authorize, live, borrower],
    by rw [region]; exact Buffer.span_fits span⟩

/-- Complete current resource authority and successful actual byte accesses
are consequences of the current manager, not an execution-success premise. -/
theorem ResourceContract.dataRead_bytes {spec : Spec} {resource : Resources spec}
    {shared : Borrowing.State} (contract : ResourceContract resource shared) {read : Read}
    (footprint : DataRead (spec.buffers resource.value) read) {offset : Nat}
    (byte : offset < read.bytes) :
    ∃ identifier loan value,
      Borrowing.authorize shared (Threads.principal resource.call.worker) identifier = .ok loan ∧
      loan.region.Contains (read.address + BitVec.ofNat 64 offset) ∧
      canonical (read.address + BitVec.ofNat 64 offset) = true ∧
      readDataByte (AddressSpace.toMemory shared.resources.space)
        (read.address + BitVec.ofNat 64 offset) = .ok value := by
  obtain ⟨_, buffer, member, span⟩ := footprint
  obtain ⟨loan, live, borrower, region⟩ := contract.inputs buffer member (Buffer.span_nonempty span)
  have valid := (contract.call.wellFormed.2 _ _ live).2
  obtain ⟨_, _, _, _, _, regionValid, readable⟩ := valid
  have inside : loan.region.Contains (read.address + BitVec.ofNat 64 offset) := by
    rw [region]
    exact Buffer.span_byte (contract.buffers buffer member) span byte
  obtain ⟨cell, stored, canRead⟩ := readable _ inside
  have canonical := AddressSpace.valid_contains_canonical _ regionValid _ inside
  exact ⟨resource.inputLoan buffer, loan, cell.byte,
    by simp [Borrowing.authorize, live, borrower], inside, canonical,
    by simp [readDataByte, canonical, AddressSpace.toMemory, stored, canRead]⟩

/-- The existing checked borrowing operations support any contained DATA4/8
span, including unaligned spans, without assuming a later machine execution. -/
theorem ResourceContract.dataRead_loadWord {spec : Spec} {resource : Resources spec}
    {shared : Borrowing.State} (contract : ResourceContract resource shared) {read : Read}
    (footprint : DataRead (spec.buffers resource.value) read) (width : read.bytes = 4) :
    ∃ identifier value,
      Borrowing.loadWord shared (Threads.principal resource.call.worker) identifier read.address =
        .ok value := by
  obtain ⟨identifier, loan, authorized, fits⟩ := contract.dataRead_permission footprint
  have span : Borrowing.Subregion (AddressSpace.wordRegion read.address) loan.region := by
    simpa only [AddressSpace.wordRegion, width] using fits
  obtain ⟨value, loaded⟩ := Borrowing.loadWord_exists shared _ identifier _ loan
    contract.call.wellFormed authorized span
  exact ⟨identifier, value, loaded⟩

theorem ResourceContract.dataRead_loadWord64 {spec : Spec} {resource : Resources spec}
    {shared : Borrowing.State} (contract : ResourceContract resource shared) {read : Read}
    (footprint : DataRead (spec.buffers resource.value) read) (width : read.bytes = 8) :
    ∃ identifier value,
      Borrowing.loadWord64 shared (Threads.principal resource.call.worker) identifier read.address =
        .ok value := by
  obtain ⟨identifier, loan, authorized, fits⟩ := contract.dataRead_permission footprint
  have span : Borrowing.Subregion (AddressSpace.qwordRegion read.address) loan.region := by
    simpa only [AddressSpace.qwordRegion, width] using fits
  obtain ⟨value, loaded⟩ := Borrowing.loadWord64_exists shared _ identifier _ loan
    contract.call.wellFormed authorized span
  exact ⟨identifier, value, loaded⟩

/-- Structural call policy AND actual live loan authority. An unrelated live
loan cannot turn a forbidden data or replacement-stack read into a call read. -/
def ReadAllowed {spec : Spec} (resource : Resources spec) (read : Read) : Prop :=
  CallResources.ReadAllowed resource.call resource.shared read ∨
    (DataRead (spec.buffers resource.value) read ∧
      ArrayResources.ReadPermission resource.shared resource.call.worker read)

theorem ReadAllowed.permission {spec : Spec} {resource : Resources spec} {read : Read}
    (allowed : ReadAllowed resource read) :
    ArrayResources.ReadPermission resource.shared resource.call.worker read := by
  rcases allowed with stack | data
  · exact stack.2.2.2
  · exact data.2

theorem ResourcePre.read_permission {spec : Spec} {bytes : List Byte}
    {resource : Resources spec} {initial : State} (pre : ResourcePre spec bytes resource initial)
    {read : Read} (allowed : RawRead spec (resourceInput resource) initial read) :
    ReadAllowed resource read := by
  rcases allowed with stack | data
  · left
    have same : read = ⟨.stack, resource.call.stack, 8⟩ := by
      cases read with
      | mk kind address bytes =>
        change kind = .stack ∧ address = initial.registers .rsp ∧ bytes = 8 at stack
        obtain ⟨rfl, addressEq, rfl⟩ := stack
        rw [addressEq, pre.stack]
    rw [same]
    exact CallResources.stackRead_permission pre.current.contract.call
  · exact .inr ⟨data, pre.current.contract.dataRead_permission data⟩

/-- The independent registered spec, including snapshots and resource policy,
is fixed once. No byte decoder, code shape, rank or proof evidence is admitted. -/
def readOnlyTask (spec : Spec) : Grading.ReadOnlyTask where
  profile := .sequentialReadOnlyX86CallableV1
  Input := Invocation spec
  pre := Pre spec
  post := Post spec
  useful input := spec.useful input.value
  Resource := Resources spec
  input := resourceInput
  resourcePre := ResourcePre spec
  current := Current
  permission resource _ := ReadAllowed resource

/-- Total raw correctness and prefix policy imply the fixed resource claim.
Whole-memory frames retain current code, stack and input loans at every actual
prefix and return in the same OS world. Admission has no future-run callback. -/
theorem semantics_of_raw {spec : Spec} {bytes : List Byte}
    (raw : ∀ input initial, Pre spec bytes input initial →
      AllExecutions initial (fun result => Post spec input initial result.state) ∧
        RawPolicy spec input initial) :
    Grading.ReadOnlySemanticClaim (readOnlyTask spec) bytes := by
  constructor
  · intro input initial pre
    obtain ⟨executions, policy⟩ := raw input initial pre
    exact ⟨executions, policy.mono (by intros; trivial) (by intros; trivial)⟩
  · intro resource initial pre
    obtain ⟨executions, policy⟩ := raw (resourceInput resource) initial pre.machine
    refine ⟨?_, policy.mono ?_ ?_⟩
    · intro choices
      obtain ⟨result, execution, post⟩ := executions choices
      exact ⟨result, execution, post, pre.current.sameMemory post.memory⟩
    · intro before memory
      exact pre.current.sameMemory memory
    · intro before read allowed
      exact pre.read_permission allowed

theorem nonvacuous_of_resource {spec : Spec} {bytes : List Byte}
    (resource : Resources spec) (initial : State) (useful : spec.useful resource.value)
    (pre : ResourcePre spec bytes resource initial) :
    Grading.ReadOnlyNonvacuous (readOnlyTask spec) bytes :=
  ⟨⟨resourceInput resource, initial, useful, pre.machine⟩,
    ⟨resource, initial, useful, pre⟩⟩

/-- Only original nonempty input loans must survive. Endpoint liveness is
sufficient because checked managed histories never recycle loan identifiers. -/
structure Retained {spec : Spec} (resource : Resources spec) (after : Borrowing.State) : Prop where
  code : (after.loans resource.call.codeLoan).isSome = true
  stack : (after.loans resource.call.stackLoan).isSome = true
  inputs : ∀ buffer ∈ spec.buffers resource.value, buffer.bytes ≠ [] →
    (after.loans (resource.inputLoan buffer)).isSome = true

/-- The manager's actual loan history preserves all snapshot bytes and their
permissions, together with current authority; other allocations may change. -/
theorem Buffer.loan_frame {before after : Borrowing.State} {buffer : Buffer}
    {worker identifier : Nat} (snapshot : BufferAt (AddressSpace.toMemory before.resources.space)
      buffer.base buffer.bytes) (held : Threads.HasLoan before worker identifier buffer.region)
    (valid : Borrowing.WellFormed before) (history : Borrowing.History before after)
    (survives : (after.loans identifier).isSome = true) :
    Threads.HasLoan after worker identifier buffer.region ∧
      BufferAt (AddressSpace.toMemory after.resources.space) buffer.base buffer.bytes := by
  have same := ArrayResources.surviving_loan held valid history survives
  obtain ⟨loan, live, borrower, region⟩ := held
  have below := (valid.2 _ _ live).1
  have finalLive := same.trans live
  refine ⟨(Threads.HasLoan.frame ⟨loan, live, borrower, region⟩ valid history same).1, ?_⟩
  apply history.buffer_stable valid identifier below loan finalLive buffer.base buffer.bytes
  · intro offset inside
    rw [region]
    exact Buffer.offset_inside snapshot inside
  · exact snapshot

/-- Original call resources and every initial byte snapshot survive an actual
checked managed history retaining those loans. No global RAM equality across
peer operations is asserted. Aliases share the same framing argument. -/
theorem ResourceContract.frame {spec : Spec} {resource : Resources spec}
    {before after : Borrowing.State} (contract : ResourceContract resource before)
    (history : Borrowing.History before after) (kept : Retained resource after) :
    ResourceContract resource after := by
  have valid := contract.call.wellFormed
  obtain ⟨codeAfter, codeCells⟩ := contract.call.codeLoan.frame valid history
    (ArrayResources.surviving_loan contract.call.codeLoan valid history kept.code)
  obtain ⟨stackAfter, stackCells⟩ := contract.call.stackLoan.frame valid history
    (ArrayResources.surviving_loan contract.call.stackLoan valid history kept.stack)
  have framed : ∀ buffer ∈ spec.buffers resource.value, buffer.bytes ≠ [] →
      Threads.HasLoan after resource.call.worker (resource.inputLoan buffer) buffer.region ∧
      BufferAt (AddressSpace.toMemory after.resources.space) buffer.base buffer.bytes := by
    intro buffer member nonempty
    exact Buffer.loan_frame (contract.buffers buffer member) (contract.inputs buffer member nonempty)
      valid history (kept.inputs buffer member nonempty)
  refine ⟨⟨history.wellFormed valid, codeAfter, stackAfter,
    AddressSpace.agrees_code _ _ _ _ codeCells contract.call.code,
    (readWord_congr _ _ _ (AddressSpace.agrees_read _ _ _ _ stackCells)).trans contract.call.stack,
    contract.call.returnCanonical, contract.call.stackBound, contract.call.postStackCanonical⟩, ?_, ?_⟩
  · intro buffer member
    by_cases empty : buffer.bytes = []
    · rw [empty]
      exact Buffer.empty _ _
    · exact (framed buffer member empty).2
  · intro buffer member nonempty
    exact (framed buffer member nonempty).1

/-- Re-couple the current machine to the actual later world after a retained
managed history. This is a resource frame, not concurrent ISA execution. -/
theorem Current.frame {spec : Spec} {resource : Resources spec} {before after : State}
    {sharedAfter : Borrowing.State} (current : Current resource before)
    (history : Borrowing.History resource.shared sharedAfter)
    (kept : Retained resource sharedAfter)
    (coupled : after.memory = AddressSpace.toMemory sharedAfter.resources.space) :
    Current {resource with shared := sharedAfter} after := by
  have framed := current.contract.frame history kept
  exact ⟨⟨framed.call, framed.buffers, framed.inputs⟩, coupled⟩

end EDSL.BufferCall
