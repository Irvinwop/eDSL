/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory

namespace EDSL.OS.AddressSpace

open X86

/-- A byte-granular sequential contract. This is not a Linux syscall, page-table,
physical-backing, allocation-ownership, or concurrent revocation semantics. -/
structure Permissions where
  readable : Bool
  writable : Bool
  executable : Bool
  deriving DecidableEq, Repr

/-- The current X86.Memory interface fetches instructions through readable bytes.
Requests for write-only or execute-only mappings therefore fail explicitly. -/
def Permissions.supported (permissions : Permissions) : Bool :=
  permissions.readable || !(permissions.writable || permissions.executable)

def readWrite : Permissions := ⟨true, true, false⟩
def readOnly : Permissions := ⟨true, false, false⟩
def readExecute : Permissions := ⟨true, false, true⟩
def inaccessible : Permissions := ⟨false, false, false⟩

structure Cell where
  byte : Byte
  permissions : Permissions
  deriving DecidableEq, Repr

structure Space where
  cells : Word → Option Cell

def empty : Space := ⟨fun _ => none⟩

structure Region where
  base : Word
  length : Nat
  deriving DecidableEq, Repr

/-- Half-open interval in natural addresses, never a modular wrapping interval. -/
def Region.Contains (region : Region) (address : Word) : Prop :=
  region.base.toNat ≤ address.toNat ∧ address.toNat < region.base.toNat + region.length

instance (region : Region) (address : Word) : Decidable (region.Contains address) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Nonempty intervals lie wholly in one canonical half of the pinned four-level
x86 address profile. No page alignment is implied by this abstract contract. -/
def Region.valid (region : Region) : Bool :=
  decide (0 < region.length ∧ region.base.toNat + region.length ≤ 2^64 ∧
    (region.base.toNat + region.length ≤ 2^47 ∨ 2^64 - 2^47 ≤ region.base.toNat))

def Region.addresses (region : Region) : List Word :=
  (List.range region.length).map fun offset => region.base + BitVec.ofNat 64 offset

def allUnmapped (space : Space) (region : Region) : Bool :=
  region.addresses.all fun address => (space.cells address).isNone

def allMapped (space : Space) (region : Region) : Bool :=
  region.addresses.all fun address => (space.cells address).isSome

inductive Fault where
  | invalidRegion
  | unsupportedPermissions
  | overlap
  | notMapped
  | denied
  | noncanonicalAddress
  deriving DecidableEq, Repr

/-- Stored contents survive removal of read permission. They are distinct from
the accessible bytes exposed by toMemory. -/
def contents (space : Space) (address : Word) : Option Byte :=
  (space.cells address).map Cell.byte

def toMemory (space : Space) : X86.Memory where
  read address := do
    let cell ← space.cells address
    if cell.permissions.readable then some cell.byte else none
  writable address :=
    match space.cells address with
    | none => false
    | some cell => cell.permissions.readable && cell.permissions.writable
  executable address :=
    match space.cells address with
    | none => false
    | some cell => cell.permissions.readable && cell.permissions.executable

def mapUnchecked (space : Space) (region : Region) (permissions : Permissions) : Space :=
  ⟨fun address => if region.Contains address then some ⟨0, permissions⟩ else space.cells address⟩

def protectUnchecked (space : Space) (region : Region) (permissions : Permissions) : Space :=
  ⟨fun address => if region.Contains address then
    (space.cells address).map fun cell => { cell with permissions := permissions }
    else space.cells address⟩

def unmapUnchecked (space : Space) (region : Region) : Space :=
  ⟨fun address => if region.Contains address then none else space.cells address⟩

/-- Fresh, zero-initialized mapping; existing mapped cells are never replaced. -/
def map (space : Space) (region : Region) (permissions : Permissions) : Except Fault Space :=
  if region.valid then
    if permissions.supported then
      if allUnmapped space region then .ok (mapUnchecked space region permissions)
      else .error .overlap
    else .error .unsupportedPermissions
  else .error .invalidRegion

/-- Protection is all-or-nothing and requires the entire region to be mapped,
including cells whose contents are currently inaccessible. -/
def protect (space : Space) (region : Region) (permissions : Permissions) : Except Fault Space :=
  if region.valid then
    if permissions.supported then
      if allMapped space region then .ok (protectUnchecked space region permissions)
      else .error .notMapped
    else .error .unsupportedPermissions
  else .error .invalidRegion

/-- The abstract unmap contract requires full mappedness, unlike interfaces that
allow holes. This operation says nothing about physical page reclamation. -/
def unmap (space : Space) (region : Region) : Except Fault Space :=
  if region.valid then
    if allMapped space region then .ok (unmapUnchecked space region)
    else .error .notMapped
  else .error .invalidRegion

/-- Sequential byte write. No atomicity or synchronization with another thread
is established by this functional update. -/
def writeByte (space : Space) (address : Word) (byte : Byte) : Except Fault Space :=
  if canonical address then
    match space.cells address with
    | none => .error .notMapped
    | some cell =>
      if cell.permissions.readable && cell.permissions.writable then
        .ok ⟨fun query => if query = address then some { cell with byte := byte }
          else space.cells query⟩
      else .error .denied
  else .error .noncanonicalAddress

theorem valid_contains_canonical (region : Region) (valid : region.valid = true)
    (address : Word) (inside : region.Contains address) : canonical address = true := by
  simp only [Region.valid, decide_eq_true_eq] at valid
  simp only [Region.Contains] at inside
  simp only [canonical, decide_eq_true_eq]
  rcases valid.2.2 with lower | upper
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- The executable finite range check covers every byte in the semantic interval,
including its last byte. No modular aliasing is used to establish this fact. -/
theorem contains_mem_addresses (region : Region) (address : Word)
    (inside : region.Contains address) : address ∈ region.addresses := by
  have lower := inside.1
  have upper := inside.2
  have addressBound := address.isLt
  have offsetBound : address.toNat - region.base.toNat < 2^64 := by omega
  have sum : region.base.toNat + (address.toNat - region.base.toNat) = address.toNat := by omega
  apply List.mem_map.mpr
  refine ⟨address.toNat - region.base.toNat, List.mem_range.mpr (by omega), ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt offsetBound, sum, Nat.mod_eq_of_lt addressBound]

theorem allUnmapped_inside (space : Space) (region : Region)
    (unmapped : allUnmapped space region = true) (address : Word)
    (inside : region.Contains address) : space.cells address = none := by
  have atAddress := List.all_eq_true.mp unmapped address (contains_mem_addresses region address inside)
  cases cellAt : space.cells address <;> simp_all

theorem allMapped_inside (space : Space) (region : Region)
    (mapped : allMapped space region = true) (address : Word)
    (inside : region.Contains address) : ∃ cell, space.cells address = some cell := by
  have atAddress := List.all_eq_true.mp mapped address (contains_mem_addresses region address inside)
  cases cellAt : space.cells address <;> simp_all

theorem map_inside (space : Space) (region : Region) (permissions : Permissions)
    (address : Word) (inside : region.Contains address) :
    (mapUnchecked space region permissions).cells address = some ⟨0, permissions⟩ := by
  simp [mapUnchecked, inside]

theorem map_frame (space : Space) (region : Region) (permissions : Permissions)
    (address : Word) (outside : ¬region.Contains address) :
    (mapUnchecked space region permissions).cells address = space.cells address := by
  simp [mapUnchecked, outside]

theorem protect_frame (space : Space) (region : Region) (permissions : Permissions)
    (address : Word) (outside : ¬region.Contains address) :
    (protectUnchecked space region permissions).cells address = space.cells address := by
  simp [protectUnchecked, outside]

theorem unmap_frame (space : Space) (region : Region)
    (address : Word) (outside : ¬region.Contains address) :
    (unmapUnchecked space region).cells address = space.cells address := by
  simp [unmapUnchecked, outside]

/-- A protection change preserves every stored byte, including inaccessible
contents and contents outside the protected interval. -/
theorem protect_preserves_contents (space : Space) (region : Region)
    (permissions : Permissions) (address : Word) :
    contents (protectUnchecked space region permissions) address = contents space address := by
  simp only [contents, protectUnchecked]
  split
  · cases space.cells address <;> rfl
  · rfl

theorem protect_denies_writes (space : Space) (region : Region)
    (permissions : Permissions) (address : Word)
    (inside : region.Contains address) (noWrites : permissions.writable = false) :
    (toMemory (protectUnchecked space region permissions)).writable address = false := by
  simp only [toMemory, protectUnchecked, ite_eq_left inside]
  cases space.cells address <;> simp [noWrites]

theorem protect_denies_store (space : Space) (region : Region)
    (permissions : Permissions) (address : Word) (value : BitVec 32)
    (inside : region.Contains address) (noWrites : permissions.writable = false) :
    storeDWord (toMemory (protectUnchecked space region permissions)) address value =
      .error (.writeDenied address) := by
  have denied := protect_denies_writes space region permissions address inside noWrites
  simp [storeDWord, canStoreDWord, dwordWritable, denied]

theorem unmap_inside (space : Space) (region : Region) (address : Word)
    (inside : region.Contains address) : (unmapUnchecked space region).cells address = none := by
  simp [unmapUnchecked, inside]

theorem unmap_denies_access (space : Space) (region : Region) (address : Word)
    (inside : region.Contains address) :
    (toMemory (unmapUnchecked space region)).read address = none ∧
    (toMemory (unmapUnchecked space region)).writable address = false ∧
    (toMemory (unmapUnchecked space region)).executable address = false := by
  simp [toMemory, unmap_inside space region address inside]

theorem unmap_denies_read (space : Space) (region : Region) (address : Word)
    (inside : region.Contains address) :
    readDataByte (toMemory (unmapUnchecked space region)) address =
      .error (.inaccessibleData address) := by
  have denied := (unmap_denies_access space region address inside).1
  simp [readDataByte, denied]

theorem unmap_denies_fetch (space : Space) (region : Region) (address : Word)
    (inside : region.Contains address) :
    fetchByte (toMemory (unmapUnchecked space region)) address =
      .error (.inaccessibleInstruction address) := by
  have denied := (unmap_denies_access space region address inside).2.2
  simp [fetchByte, denied]

theorem unmap_denies_store (space : Space) (region : Region) (address : Word)
    (value : BitVec 32) (inside : region.Contains address) :
    storeDWord (toMemory (unmapUnchecked space region)) address value =
      .error (.writeDenied address) := by
  have denied := (unmap_denies_access space region address inside).2.1
  simp [storeDWord, canStoreDWord, dwordWritable, denied]

/-- Cell framing implies the exact same machine read/write/execute observations. -/
theorem toMemory_agrees_at (left right : Space) (address : Word)
    (same : left.cells address = right.cells address) :
    (toMemory left).read address = (toMemory right).read address ∧
    (toMemory left).writable address = (toMemory right).writable address ∧
    (toMemory left).executable address = (toMemory right).executable address := by
  simp only [toMemory, same, and_self]

theorem map_success (space : Space) (region : Region) (permissions : Permissions)
    (valid : region.valid = true) (supported : permissions.supported = true)
    (free : allUnmapped space region = true) :
    map space region permissions = .ok (mapUnchecked space region permissions) := by
  simp [map, valid, supported, free]

theorem protect_success (space : Space) (region : Region) (permissions : Permissions)
    (valid : region.valid = true) (supported : permissions.supported = true)
    (mapped : allMapped space region = true) :
    protect space region permissions = .ok (protectUnchecked space region permissions) := by
  simp [protect, valid, supported, mapped]

theorem unmap_success (space : Space) (region : Region)
    (valid : region.valid = true) (mapped : allMapped space region = true) :
    unmap space region = .ok (unmapUnchecked space region) := by
  simp [unmap, valid, mapped]

theorem map_ok (space result : Space) (region : Region) (permissions : Permissions)
    (success : map space region permissions = .ok result) :
    result = mapUnchecked space region permissions ∧ region.valid = true ∧
      permissions.supported = true ∧ allUnmapped space region = true := by
  unfold map at success
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all

theorem protect_ok (space result : Space) (region : Region) (permissions : Permissions)
    (success : protect space region permissions = .ok result) :
    result = protectUnchecked space region permissions ∧ region.valid = true ∧
      permissions.supported = true ∧ allMapped space region = true := by
  unfold protect at success
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all

theorem unmap_ok (space result : Space) (region : Region)
    (success : unmap space region = .ok result) :
    result = unmapUnchecked space region ∧ region.valid = true ∧
      allMapped space region = true := by
  unfold unmap at success
  split at success <;> simp_all
  split at success <;> simp_all

/-- Successful fresh mapping preserves every previously mapped cell, so it cannot
silently replace the contents or permissions of an existing allocation. -/
theorem map_preserves_existing (space result : Space) (region : Region)
    (permissions : Permissions) (success : map space region permissions = .ok result)
    (address : Word) (cell : Cell) (existing : space.cells address = some cell) :
    result.cells address = some cell := by
  obtain ⟨resultEq, _, _, free⟩ := map_ok space result region permissions success
  have outside : ¬region.Contains address := by
    intro inside
    have missing := allUnmapped_inside space region free address inside
    rw [existing] at missing
    contradiction
  rw [resultEq, map_frame space region permissions address outside, existing]

theorem writeByte_success (space : Space) (address : Word) (byte : Byte) (cell : Cell)
    (valid : canonical address = true) (mapped : space.cells address = some cell)
    (readable : cell.permissions.readable = true) (writable : cell.permissions.writable = true) :
    ∃ result, writeByte space address byte = .ok result ∧
      (toMemory result).read address = some byte ∧
      (∀ query, query ≠ address → result.cells query = space.cells query) := by
  refine ⟨⟨fun query => if query = address then some { cell with byte := byte }
    else space.cells query⟩, ?_, ?_, ?_⟩
  · simp [writeByte, valid, mapped, readable, writable]
  · simp [toMemory, readable]
  · intro query different
    simp [different]

end EDSL.OS.AddressSpace
