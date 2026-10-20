/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.ELFResources
import EDSL.BufferCall.Resources
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

/-! Common full-image indexing and checked byte-buffer/caller construction.
All authority starts in a new modeled registry over the supplied complete space.
No native ownership or successful candidate execution is inferred. -/

namespace EDSL.Corpus.BufferResources
open X86 OS OS.AddressSpace

/-- The kernel checks Eq.refl against the original equality. This avoids
recursive elaborator unification of a complete checked setup, as in the existing
FetchAddResources helper; it adds no evaluation/proof rule or limit override. -/
elab "buffer_resource_kernel_rfl" : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let some (_, _, rhs) := (← Lean.Meta.whnf (← goal.getType)).eq? |
      Lean.throwError "expected an equality"
    let proof ← Lean.Meta.mkEqRefl rhs
    Lean.Elab.Tactic.closeMainGoal `buffer_resource_kernel_rfl proof

def installed (file : List Byte) (input : FunctionInput) : ELF.Loaded :=
  ELFResources.loaded file input ⟨empty, 0, 0, 0, 0, 0⟩

theorem admittedWith {maxBytes : Nat} {file name : List Byte} {input : FunctionInput}
    (checked : input.checkWith maxBytes file name = true) :
    input.admitWith maxBytes file name empty = .ok (installed file input) := by
  have fresh : ELF.fresh input.table.image empty = true := by
    apply List.all_eq_true.mpr
    intro segment _
    apply List.all_eq_true.mpr
    intro address _
    rfl
  exact ELFResources.admittedWith (caller := ⟨empty, 0, 0, 0, 0, 0⟩) checked fresh

private theorem segmentCell_permissions (file : List Byte) (segment : ELF.Segment)
    (address : Nat) (cell : AddressSpace.Cell)
    (found : ELF.segmentCell file segment address = some cell) :
    cell.permissions = segment.permissions := by
  dsimp only [ELF.segmentCell] at found
  split at found
  · cases byte : file[segment.offset + (address - segment.virtualAddress)]? with
    | none => simp [byte] at found
    | some value =>
      simp only [byte, Option.map_some, Option.some.injEq] at found
      subst cell
      rfl
  · cases Option.some.inj found
    rfl

theorem installed_cellWith {maxBytes : Nat} {file name : List Byte} {input : FunctionInput}
    (checked : input.checkWith maxBytes file name = true)
    (permissions : ∀ segment ∈ input.table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute)
    (index : Nat) (bound : index < input.bytes.length) :
    (installed file input).space.cells (input.function.window.base + BitVec.ofNat 64 index) =
      some ⟨input.bytes[index], readExecute⟩ := by
  have code := (ELF.FunctionSymbol.admitted_soundWith (admittedWith checked)).2.2.2.2.1
  have fetched := code.2 index input.bytes[index] (List.getElem?_eq_getElem bound)
  let address := input.function.window.base + BitVec.ofNat 64 index
  change fetchByte (toMemory (installed file input).space) address = .ok _ at fetched
  cases found : (installed file input).space.cells address with
  | none => simp [fetchByte, toMemory, found] at fetched
  | some current =>
    have facts : canonical address = true ∧ current.permissions.readable = true ∧
        current.permissions.executable = true ∧ current.byte = input.bytes[index] := by
      cases canonical : X86.canonical address <;>
        cases readable : current.permissions.readable <;>
        cases executable : current.permissions.executable <;>
        simp_all [fetchByte, toMemory]
    have currentPermissions : current.permissions = readExecute := by
      cases selected : ELF.segmentAt input.table.image address.toNat with
      | none => simp [installed, ELFResources.loaded, ELF.CallerResources.loaded, ELF.install, selected, empty] at found
      | some segment =>
        have raw : ELF.segmentCell file segment address.toNat = some current := by
          simpa only [installed, ELFResources.loaded, ELF.CallerResources.loaded, ELF.install, selected] using found
        have projected := segmentCell_permissions _ _ _ _ raw
        exact projected.trans (permissions segment (List.mem_of_find?_eq_some selected)
          (projected ▸ facts.2.2.1))
    have equal : current = ⟨input.bytes[index], readExecute⟩ := by
      cases current
      simp_all
    exact congrArg some equal

/-- Extensionally the COMPLETE installed space. Only its checked function
slice has a faster index; every other loaded cell and permission is retained. -/
def programSpace (file : List Byte) (input : FunctionInput) : Space where
  cells address :=
    if (⟨input.function.window.base, input.bytes.length⟩ : Region).Contains address then
      some ⟨(input.bytes[address.toNat - input.function.window.base.toNat]?).getD 0, readExecute⟩
    else (installed file input).space.cells address

theorem programSpace_eqWith {maxBytes : Nat} {file name : List Byte} {input : FunctionInput}
    (checked : input.checkWith maxBytes file name = true)
    (permissions : ∀ segment ∈ input.table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute) :
    programSpace file input = (installed file input).space := by
  apply congrArg Space.mk
  funext address
  change (programSpace file input).cells address = (installed file input).space.cells address
  by_cases inside : (⟨input.function.window.base, input.bytes.length⟩ : Region).Contains address
  · let offset := address.toNat - input.function.window.base.toNat
    change input.function.window.base.toNat ≤ address.toNat ∧
      address.toNat < input.function.window.base.toNat + input.bytes.length at inside
    have bound : offset < input.bytes.length := by
      dsimp [offset]; rcases inside with ⟨lower, upper⟩; omega
    have small : offset < 2^64 := by dsimp [offset]; have := address.isLt; omega
    have sum : input.function.window.base.toNat + offset = address.toNat := by
      dsimp [offset]; have := inside.1; omega
    have same : input.function.window.base + BitVec.ofNat 64 offset = address := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, sum,
        Nat.mod_eq_of_lt address.isLt]
    have original := installed_cellWith checked permissions offset bound
    rw [same] at original
    change (if _ then some (⟨_, readExecute⟩ : AddressSpace.Cell) else _) = _
    change (if (input.function.window.base.toNat ≤ address.toNat ∧
      address.toNat < input.function.window.base.toNat + input.bytes.length)
      then some (⟨_, readExecute⟩ : AddressSpace.Cell) else _) = _
    rw [ite_eq_left inside, original]
    change some (⟨(input.bytes[offset]?).getD 0, readExecute⟩ : AddressSpace.Cell) = _
    rw [List.getElem?_eq_getElem bound, Option.getD_some]
  · change (if _ then some (⟨_, readExecute⟩ : AddressSpace.Cell) else _) = _
    rw [ite_eq_right inside]

theorem admitted {file name : List Byte} {input : FunctionInput}
    (checked : input.check file name = true) :
    input.admit file name empty = .ok (installed file input) :=
  admittedWith checked

theorem installed_cell {file name : List Byte} {input : FunctionInput}
    (checked : input.check file name = true)
    (permissions : ∀ segment ∈ input.table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute)
    (index : Nat) (bound : index < input.bytes.length) :
    (installed file input).space.cells (input.function.window.base + BitVec.ofNat 64 index) =
      some ⟨input.bytes[index], readExecute⟩ :=
  installed_cellWith checked permissions index bound

theorem programSpace_eq {file name : List Byte} {input : FunctionInput}
    (checked : input.check file name = true)
    (permissions : ∀ segment ∈ input.table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute) :
    programSpace file input = (installed file input).space :=
  programSpace_eqWith checked permissions

structure Managed where
  shared : Borrowing.State
  valid : Borrowing.WellFormed shared

def seed (space : Space) : Managed :=
  ⟨Borrowing.empty (Ownership.empty space),
    Borrowing.empty_wellFormed _ (Ownership.empty_wellFormed _)⟩

def mutate (before : Managed) (operation : Ownership.Mutation) :
    Except Borrowing.Fault (Managed × Option Ownership.Ticket) :=
  match success : Borrowing.mutate before.shared operation with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1,
      Borrowing.mutate_wellFormed _ _ _ before.valid success⟩, result.2)

def readBorrow (before : Managed) (owner : Nat) (ticket : Ownership.Ticket)
    (worker : Nat) (region : Region) : Except Borrowing.Fault (Managed × Nat) :=
  match success : Borrowing.readBorrow before.shared owner ticket (Threads.principal worker) region with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1,
      (Borrowing.readBorrow_wellFormed _ _ _ _ _ _ before.valid success).1⟩, result.2)

def ticket : Option Ownership.Ticket → Except Borrowing.Fault Ownership.Ticket
  | none => .error (.ownership .missingAllocation)
  | some result => .ok result

/-- A private caller allocation is initialized before protection and borrowing. -/
def caller (before : Managed) (owner worker : Nat) (stack returnAddress : Word) :
    Except Borrowing.Fault (Managed × Nat) := do
  let (allocated, output) ← mutate before (.allocate owner ⟨stack, 8⟩ readWrite)
  let allocation ← ticket output
  let (written, _) ← mutate allocated (.store64 owner allocation stack returnAddress)
  let (readable, _) ← mutate written (.protect owner allocation readOnly)
  readBorrow readable owner allocation worker ⟨stack, 8⟩

/-- Little-endian packing into the manager's existing checked qword writer. -/
def pack : List Byte → Word
  | [] => 0
  | byte :: tail => BitVec.ofNat 64 byte.toNat + 256 * pack tail

def words (values : List Byte) : List Word :=
  (List.range ((values.length + 7) / 8)).map fun index => pack ((values.drop (8 * index)).take 8)

def storeWords (before : Managed) (owner : Nat) (allocation : Ownership.Ticket)
    (base : Word) : List Word → Except Borrowing.Fault Managed
  | [] => .ok before
  | value :: tail => do
      let (written, _) ← mutate before (.store64 owner allocation base value)
      storeWords written owner allocation (base + 8) tail

/-- General byte snapshots use checked stores into a padded private allocation,
then a loan of EXACTLY the requested bytes. No count cap is added to a spec.
Empty snapshots do not allocate, test the pointer, or consult a data loan. -/
def dataByteBuffer (before : Managed) (owner worker : Nat) (buffer : BufferCall.Buffer)
    (unused : Nat := 0) : Except Borrowing.Fault (Managed × Nat) := do
  if buffer.bytes = [] then return (before, unused)
  let values := words buffer.bytes
  let (allocated, output) ← mutate before (.allocate owner ⟨buffer.base, 8 * values.length⟩ readWrite)
  let allocation ← ticket output
  let written ← storeWords allocated owner allocation buffer.base values
  let (readable, _) ← mutate written (.protect owner allocation readOnly)
  readBorrow readable owner allocation worker buffer.region

theorem dataByteBuffer_empty (before : Managed) (owner worker unused : Nat) (base : Word) :
    dataByteBuffer before owner worker ⟨base, []⟩ unused = .ok (before, unused) := rfl

structure Layout where
  codeOwner : Nat
  callerOwner : Nat
  dataOwner : Nat
  worker : Nat
  stack : Word
  returnAddress : Word

structure Ready where
  managed : Managed
  codeLoan : Nat
  callerLoan : Nat
  inputLoan : Nat

/-- The supplied space is retained at the start; all mutations pass through
the checked borrowing/ownership manager and carry its preservation theorem. -/
def setup (space : Space) (entry : Word) (bytes : List Byte) (layout : Layout)
    (buffer : BufferCall.Buffer) : Except Borrowing.Fault Ready := do
  let (adopted, output) ← mutate (seed space)
    (.adopt layout.codeOwner ⟨entry, bytes.length⟩)
  let allocation ← ticket output
  let (code, codeLoan) ← readBorrow adopted layout.codeOwner allocation layout.worker
    ⟨entry, bytes.length⟩
  let (original, callerLoan) ← caller code layout.callerOwner layout.worker
    layout.stack layout.returnAddress
  let (data, inputLoan) ← dataByteBuffer original layout.dataOwner layout.worker buffer
  return ⟨data, codeLoan, callerLoan, inputLoan⟩

/-- Memory projection used for normalization only, never to supply authority. -/
def freshQWord (before : Space) (address value : Word) : Space :=
  protectUnchecked (writeQWordCells (mapUnchecked before ⟨address, 8⟩ readWrite) address value)
    ⟨address, 8⟩ readOnly

theorem freshQWord_frame (before : Space) (address value query : Word)
    (outside : ¬ (⟨address, 8⟩ : Region).Contains query) :
    (freshQWord before address value).cells query = before.cells query := by
  simp only [freshQWord, protectUnchecked, writeQWordCells, mapUnchecked,
    qwordRegion, ite_eq_right outside]

end EDSL.Corpus.BufferResources
#audit_edsl
