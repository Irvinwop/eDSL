/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.BufferResources
import EDSL.OS.Atomics64
import EDSL.OS.Ownership.ProtectRead64
import EDSL.Grading.ConcurrentTask.Plain64.Admission

set_option autoImplicit false
set_option warningAsError true

/-! Checked present-resource construction over an arbitrary COMPLETE space.
The extra policy permits writes/protection only in regions absent from that
original space. It is not a weaker ownership gate: the real Atomics64,
Borrowing and Ownership operations still perform all their checks.
-/

namespace EDSL.Corpus.PlainResources
open X86 OS OS.AddressSpace

private theorem bind_ok {ε α β : Type} {operation : Except ε α}
    {next : α → Except ε β} {result : β}
    (success : (operation >>= next) = .ok result) :
    ∃ input, operation = .ok input ∧ next input = .ok result := by
  cases operation with
  | error fault => simp at success
  | ok input => exact ⟨input, rfl, success⟩

/-- Retain a checked operation's equation as proof data. Forgetting that proof
returns exactly the original success or fault. -/
private def checkedResult {ε α : Type} (operation : Except ε α) :
    Except ε {result : α // operation = .ok result} :=
  match _success : operation with
  | .error fault => .error fault
  | .ok result => .ok ⟨result, rfl⟩

private theorem checkedResult_forget {ε α : Type} (operation : Except ε α) :
    (checkedResult operation).map Subtype.val = operation := by
  cases operation <;> rfl

def Retains (original current : Space) : Prop :=
  ∀ address cell, original.cells address = some cell → current.cells address = some cell

theorem Retains.refl (space : Space) : Retains space space := fun _ _ live => live

theorem Retains.trans {first middle last : Space}
    (one : Retains first middle) (two : Retains middle last) : Retains first last :=
  fun address cell live => two address cell (one address cell live)

private theorem fresh_outside {original : Space} {region : Region}
    (fresh : allUnmapped original region = true) {address : Word} {cell : AddressSpace.Cell}
    (live : original.cells address = some cell) : ¬region.Contains address := by
  intro inside
  have missing := allUnmapped_inside original region fresh address inside
  rw [live] at missing
  cases missing

/-- This finite policy is about ORIGINAL cells, never a desired result or a
future machine state. Adoption changes no cells. Targeted edits of original
ELF mappings, transfer, release and the unused dword writer are excluded. -/
def freshEdits (original : Space) (before : Ownership.World)
    (operation : Ownership.Mutation) : Bool :=
  match operation with
  | .adopt .. => true
  | .allocate _ region _ => allUnmapped original region
  | .store64 _ _ address _ => allUnmapped original (qwordRegion address)
  | .protect owner ticket _ =>
    match Ownership.authorize before owner ticket with
    | .error _ => false
    | .ok allocation => allUnmapped original allocation.region
  | _ => false

private theorem ownership_retains {original : Space} {before : Ownership.World}
    {operation : Ownership.Mutation} {result : Ownership.World × Option Ownership.Ticket}
    (retained : Retains original before.space)
    (policy : freshEdits original before operation = true)
    (success : operation.run before = .ok result) : Retains original result.1.space := by
  cases operation with
  | allocate owner region permissions =>
    cases performed : Ownership.allocate before owner region permissions with
    | error fault => simp [Ownership.Mutation.run, performed, Except.map] at success
    | ok output =>
      simp only [Ownership.Mutation.run, performed, Except.map, Except.ok.injEq] at success
      cases success
      intro address cell live
      exact (Ownership.allocate_initialized _ _ _ _ _ performed).2 address cell
        (retained address cell live)
  | adopt owner region =>
    cases performed : Ownership.adopt before owner region with
    | error fault => simp [Ownership.Mutation.run, performed, Except.map] at success
    | ok output =>
      simp only [Ownership.Mutation.run, performed, Except.map, Except.ok.injEq] at success
      cases success
      have shape := (Ownership.adopt_ok _ _ _ _ performed).1
      simpa only [shape, Ownership.install] using retained
  | protect owner ticket permissions =>
    cases performed : Ownership.protect before owner ticket permissions with
    | error fault => simp [Ownership.Mutation.run, performed, Except.map] at success
    | ok output =>
      simp only [Ownership.Mutation.run, performed, Except.map, Except.ok.injEq] at success
      cases success
      intro address cell live
      have frame := Ownership.protect_frame _ _ _ _ _ performed address (by
        intro allocation authorized
        have fresh : allUnmapped original allocation.region = true := by
          simpa only [freshEdits, authorized] using policy
        exact fresh_outside fresh live)
      exact frame.trans (retained address cell live)
  | store64 owner ticket address value =>
    cases performed : Ownership.storeWord64 before owner ticket address value with
    | error fault => simp [Ownership.Mutation.run, performed, Except.map] at success
    | ok output =>
      simp only [Ownership.Mutation.run, performed, Except.map, Except.ok.injEq] at success
      cases success
      obtain ⟨_, space, _, _, written, shape⟩ := Ownership.storeWord64_ok _ _ _ _ _ _ performed
      have projected := (AddressSpace.storeQWord_ok _ _ _ _ written).1
      intro query cell live
      have outside := fresh_outside policy live
      simpa only [shape, projected, writeQWordCells, ite_eq_right outside] using
        retained query cell live
  | transfer owner ticket newOwner => simp [freshEdits] at policy
  | release owner ticket => simp [freshEdits] at policy
  | store owner ticket address value => simp [freshEdits] at policy

private theorem mutation_retains {original : Space} {before : Atomics64.State}
    {operation : Ownership.Mutation} {result : Atomics64.State × Option Ownership.Ticket}
    (retained : Retains original before.legacy.shared.resources.space)
    (policy : freshEdits original before.legacy.shared.resources operation = true)
    (success : Atomics64.mutate before operation = .ok result) :
    Retains original result.1.legacy.shared.resources.space := by
  obtain ⟨_, legacy, changed, outer⟩ := Atomics64.mutate_ok _ _ _ success
  obtain ⟨_, shared, borrowed, middle⟩ := Atomics.mutate_ok _ _ _ changed
  obtain ⟨_, resources, performed, inner⟩ := Borrowing.mutate_ok _ _ _ borrowed
  simpa only [outer, middle, inner] using ownership_retains retained policy performed

structure Managed (original : Space) where
  world : Atomics64.State
  valid : Atomics64.WellFormed world
  retained : Retains original world.legacy.shared.resources.space

def seed (original : Space) : Managed original :=
  ⟨Atomics64.empty (Atomics.empty (Borrowing.empty (Ownership.empty original))),
    Atomics64.empty_wellFormed _ (Atomics.empty_wellFormed _
      (Borrowing.empty_wellFormed _ (Ownership.empty_wellFormed _))), Retains.refl original⟩

structure Mutated {original : Space} (before : Managed original)
    (operation : Ownership.Mutation) where
  managed : Managed original
  output : Option Ownership.Ticket
  performed : Atomics64.mutate before.world operation = .ok (managed.world, output)

def mutate {original : Space} (before : Managed original) (operation : Ownership.Mutation) :
    Except Atomics64.Fault (Mutated before operation) :=
  if policy : freshEdits original before.world.legacy.shared.resources operation = true then
    match success : Atomics64.mutate before.world operation with
    | .error fault => .error fault
    | .ok result => .ok ⟨⟨result.1,
        Atomics64.mutate_wellFormed _ _ _ before.valid success,
        mutation_retains before.retained policy success⟩, result.2, success⟩
  else .error .executable

/-- All three checked mutation layers retain the loan registry and frontier.
This is a projection of their actual successful outputs, not a replacement
state admitted as an environment operation. -/
theorem mutate_loan_metadata {before : Atomics64.State} {operation : Ownership.Mutation}
    {result : Atomics64.State × Option Ownership.Ticket}
    (success : Atomics64.mutate before operation = .ok result) :
    result.1.legacy.shared.loans = before.legacy.shared.loans ∧
      result.1.legacy.shared.nextLoan = before.legacy.shared.nextLoan := by
  obtain ⟨_, legacy, changed, outer⟩ := Atomics64.mutate_ok _ _ _ success
  obtain ⟨_, shared, borrowed, middle⟩ := Atomics.mutate_ok _ _ _ changed
  obtain ⟨_, resources, _, inner⟩ := Borrowing.mutate_ok _ _ _ borrowed
  simp only [outer, middle, inner, and_self]

/-- The initial read authenticates the old loan ID. A derived registry frame
then supplies endpoint liveness to the production history read theorem. -/
private theorem read_stable {before after : Atomics64.State}
    (history : Borrowing.History before.legacy.shared after.legacy.shared)
    (valid : Atomics64.WellFormed before)
    (loans : ∀ identifier, identifier < before.legacy.shared.nextLoan →
      after.legacy.shared.loans identifier = before.legacy.shared.loans identifier)
    {actor identifier : Nat} {address value : Word}
    (read : Borrowing.loadWord64 before.legacy.shared actor identifier address = .ok value) :
    Borrowing.loadWord64 after.legacy.shared actor identifier address = .ok value := by
  obtain ⟨loan, authorized, _, _⟩ := Borrowing.loadWord64_ok _ _ _ _ _ read
  have live := (Borrowing.authorize_ok _ _ _ _ authorized).1
  have below := (valid.legacy.shared.2 _ _ live).1
  have survives : (after.legacy.shared.loans identifier).isSome = true := by
    rw [loans identifier below, live]
    rfl
  exact history.loadWord64_stable valid.legacy.shared actor identifier address value read survives

theorem Mutated.nextLoan {original : Space} {before : Managed original}
    {operation : Ownership.Mutation} (result : Mutated before operation) :
    result.managed.world.legacy.shared.nextLoan = before.world.legacy.shared.nextLoan :=
  (mutate_loan_metadata result.performed).2

theorem Mutated.preserves_read {original : Space} {before : Managed original}
    {operation : Ownership.Mutation} (result : Mutated before operation)
    {actor identifier : Nat} {address value : Word}
    (read : Borrowing.loadWord64 before.world.legacy.shared actor identifier address = .ok value) :
    Borrowing.loadWord64 result.managed.world.legacy.shared actor identifier address = .ok value :=
  read_stable (Atomics64.Step.mutate result.performed).borrowing before.valid
    (fun identifier _ => congrFun (mutate_loan_metadata result.performed).1 identifier) read

/-- The returned ID is the old fresh frontier. Existing IDs below it retain
their exact records, while only the checked borrow's own record is installed. -/
theorem readBorrow_loan_metadata {before : Atomics64.State} {owner actor : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Atomics64.State × Nat}
    (success : Atomics64.readBorrow before owner ticket actor region = .ok result) :
    result.2 = before.legacy.shared.nextLoan ∧
    result.1.legacy.shared.nextLoan = before.legacy.shared.nextLoan + 1 ∧
    result.1.legacy.shared.loans result.2 = some ⟨ticket, owner, actor, region⟩ ∧
    ∀ identifier, identifier < before.legacy.shared.nextLoan →
      result.1.legacy.shared.loans identifier = before.legacy.shared.loans identifier := by
  obtain ⟨_, legacy, changed, outer⟩ := Atomics64.readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨_, shared, raw, middle⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ changed
  obtain ⟨_, _, _, _, _, inner⟩ := Borrowing.readBorrow_ok _ _ _ _ _ _ raw
  refine ⟨by simp only [outer, middle, inner],
    by simp only [outer, middle, inner, Borrowing.installLoan],
    by simp [outer, middle, inner, Borrowing.installLoan], ?_⟩
  intro identifier below
  have old : identifier ≠ before.legacy.shared.nextLoan := by omega
  simp only [outer, middle, inner, Borrowing.installLoan, ite_eq_right old]

private theorem borrow_space {before : Atomics64.State} {owner actor : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Atomics64.State × Nat}
    (success : Atomics64.readBorrow before owner ticket actor region = .ok result) :
    result.1.legacy.shared.resources.space = before.legacy.shared.resources.space := by
  obtain ⟨_, legacy, changed, outer⟩ := Atomics64.readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨_, shared, raw, middle⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ changed
  obtain ⟨_, _, _, _, _, shape⟩ := Borrowing.readBorrow_ok _ _ _ _ _ _ raw
  simp only [outer, middle, shape, Borrowing.installLoan]

structure Borrowed {original : Space} (before : Managed original) where
  managed : Managed original
  identifier : Nat
  space : managed.world.legacy.shared.resources.space = before.world.legacy.shared.resources.space

def borrow {original : Space} (before : Managed original) (owner : Nat)
    (ticket : Ownership.Ticket) (actor : Nat) (region : Region) :
    Except Atomics64.Fault (Borrowed before) :=
  match success : Atomics64.readBorrow before.world owner ticket actor region with
  | .error fault => .error fault
  | .ok result =>
    have same := borrow_space success
    .ok ⟨⟨result.1, Atomics64.readBorrow_wellFormed _ _ _ _ _ _ before.valid success,
      by simpa only [same] using before.retained⟩, result.2, same⟩

theorem borrow_performed {original : Space} {before : Managed original} {owner actor : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Borrowed before}
    (success : borrow before owner ticket actor region = .ok result) :
    Atomics64.readBorrow before.world owner ticket actor region =
      .ok (result.managed.world, result.identifier) := by
  unfold borrow at success
  split at success
  next fault raw => cases success
  next output raw =>
    cases success
    exact raw

theorem borrow_frontier {original : Space} {before : Managed original} {owner actor : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Borrowed before}
    (success : borrow before owner ticket actor region = .ok result) :
    result.identifier = before.world.legacy.shared.nextLoan ∧
      result.managed.world.legacy.shared.nextLoan = before.world.legacy.shared.nextLoan + 1 := by
  have metadata := readBorrow_loan_metadata (borrow_performed success)
  exact ⟨metadata.1, metadata.2.1⟩

def ticket : Option Ownership.Ticket → Except Atomics64.Fault Ownership.Ticket
  | none => .error .missingCell
  | some result => .ok result

/-- The checked qword store supplies arbitrary-word serialization/readback.
This theorem does not evaluate the word or assume a desired load result. -/
theorem store_readback {before after : Atomics64.State} {owner : Nat}
    {allocation : Ownership.Ticket} {address value : Word} {output : Option Ownership.Ticket}
    (success : Atomics64.mutate before (.store64 owner allocation address value) = .ok (after, output)) :
    loadQWord (toMemory after.legacy.shared.resources.space) address = .ok value := by
  obtain ⟨_, legacy, changed, outer⟩ := Atomics64.mutate_ok _ _ _ success
  obtain ⟨_, shared, borrowed, middle⟩ := Atomics.mutate_ok _ _ _ changed
  obtain ⟨_, resources, performed, inner⟩ := Borrowing.mutate_ok _ _ _ borrowed
  cases raw : Ownership.storeWord64 before.legacy.shared.resources owner allocation address value with
  | error fault => simp [Ownership.Mutation.run, raw, Except.map] at performed
  | ok world =>
    simp only [Ownership.Mutation.run, raw, Except.map, Except.ok.injEq] at performed
    cases performed
    obtain ⟨_, space, _, _, written, shape⟩ := Ownership.storeWord64_ok _ _ _ _ _ _ raw
    have afterEq : after = { before with legacy := legacy.1 } := congrArg Prod.fst outer
    simpa only [afterEq, middle, inner, shape] using
      (AddressSpace.storeQWord_sound _ _ _ _ written).2.1

/-- Checked protection changes readable permissions while retaining the word
authenticated by the preceding store. The loan is created only afterwards. -/
theorem protect_readback {before after : Atomics64.State} {owner : Nat}
    {allocation : Ownership.Ticket} {address value : Word} {output : Option Ownership.Ticket}
    (success : Atomics64.mutate before (.protect owner allocation readOnly) = .ok (after, output))
    (read : loadQWord (toMemory before.legacy.shared.resources.space) address = .ok value) :
    loadQWord (toMemory after.legacy.shared.resources.space) address = .ok value := by
  obtain ⟨_, legacy, changed, outer⟩ := Atomics64.mutate_ok _ _ _ success
  obtain ⟨_, shared, borrowed, middle⟩ := Atomics.mutate_ok _ _ _ changed
  obtain ⟨_, resources, performed, inner⟩ := Borrowing.mutate_ok _ _ _ borrowed
  cases raw : Ownership.protect before.legacy.shared.resources owner allocation readOnly with
  | error fault => simp [Ownership.Mutation.run, raw, Except.map] at performed
  | ok world =>
    simp only [Ownership.Mutation.run, raw, Except.map, Except.ok.injEq] at performed
    cases performed
    have afterEq : after = { before with legacy := legacy.1 } := congrArg Prod.fst outer
    simpa only [afterEq, middle, inner] using Ownership.protect_readback raw read

structure Enrolled {original : Space} (before : Managed original) (cell : Atomics64.Cell) where
  managed : Managed original
  identifier : Atomics64.CellId64
  live : managed.world.cells identifier = some cell
  space : managed.world.legacy.shared.resources.space = before.world.legacy.shared.resources.space

def enroll {original : Space} (before : Managed original) (owner : Nat)
    (allocation : Ownership.Ticket) (address : Word) :
    Except Atomics64.Fault (Enrolled before ⟨owner, allocation, address⟩) :=
  match success : Atomics64.enroll before.world owner allocation address with
  | .error fault => .error fault
  | .ok result =>
    have shape := (Atomics64.enroll_ok _ _ _ _ _ success).2.2.2.2
    have same : result.1.legacy.shared.resources.space = before.world.legacy.shared.resources.space := by
      simp only [shape, Atomics64.installCell]
    .ok ⟨⟨result.1, (Atomics64.enroll_wellFormed _ _ _ _ _ before.valid success).1,
      by simpa only [same] using before.retained⟩, result.2,
      (Atomics64.enroll_wellFormed _ _ _ _ _ before.valid success).2, same⟩

theorem enroll_performed {original : Space} {before : Managed original} {owner : Nat}
    {allocation : Ownership.Ticket} {address : Word}
    {result : Enrolled before ⟨owner, allocation, address⟩}
    (success : enroll before owner allocation address = .ok result) :
    Atomics64.enroll before.world owner allocation address =
      .ok (result.managed.world, result.identifier) := by
  unfold enroll at success
  split at success
  next fault raw => cases success
  next output raw =>
    cases success
    exact raw

theorem enroll_shared {before : Atomics64.State} {owner : Nat}
    {allocation : Ownership.Ticket} {address : Word} {result : Atomics64.State × Atomics64.CellId64}
    (success : Atomics64.enroll before owner allocation address = .ok result) :
    result.1.legacy.shared = before.legacy.shared := by
  have shape := (Atomics64.enroll_ok _ _ _ _ _ success).2.2.2.2
  simp only [shape, Atomics64.installCell]

theorem enroll_preserves_read {original : Space} {before : Managed original} {owner : Nat}
    {allocation : Ownership.Ticket} {address : Word}
    {result : Enrolled before ⟨owner, allocation, address⟩}
    (success : enroll before owner allocation address = .ok result)
    {actor identifier : Nat} {query value : Word}
    (read : Borrowing.loadWord64 before.world.legacy.shared actor identifier query = .ok value) :
    Borrowing.loadWord64 result.managed.world.legacy.shared actor identifier query = .ok value := by
  have raw := enroll_performed success
  apply read_stable (Atomics64.Step.enroll raw).borrowing before.valid _ read
  intro identifier _
  rw [enroll_shared raw]

structure Issued {original : Space} (before : Managed original) where
  managed : Managed original
  identifier : Atomics64.HandleId64
  cells : managed.world.cells = before.world.cells
  space : managed.world.legacy.shared.resources.space = before.world.legacy.shared.resources.space

def issue {original : Space} (before : Managed original) (owner : Nat)
    (cell : Atomics64.CellId64) (actor : Nat) : Except Atomics64.Fault (Issued before) :=
  match success : Atomics64.issue before.world owner cell actor with
  | .error fault => .error fault
  | .ok result =>
    have shape : result = (Atomics64.installHandle before.world ⟨actor, cell⟩,
        ⟨before.world.nextHandle⟩) := by
      obtain ⟨_, _, same⟩ := Atomics64.issue_ok _ _ _ _ _ success
      exact same
    have same : result.1.legacy.shared.resources.space = before.world.legacy.shared.resources.space := by
      simp only [shape, Atomics64.installHandle]
    .ok ⟨⟨result.1, (Atomics64.issue_wellFormed _ _ _ _ _ before.valid success).1,
      by simpa only [same] using before.retained⟩, result.2,
      by simp only [shape, Atomics64.installHandle], same⟩

theorem issue_performed {original : Space} {before : Managed original} {owner actor : Nat}
    {cell : Atomics64.CellId64} {result : Issued before}
    (success : issue before owner cell actor = .ok result) :
    Atomics64.issue before.world owner cell actor =
      .ok (result.managed.world, result.identifier) := by
  unfold issue at success
  split at success
  next fault raw => cases success
  next output raw =>
    cases success
    exact raw

theorem issue_shared {before : Atomics64.State} {owner actor : Nat}
    {cell : Atomics64.CellId64} {result : Atomics64.State × Atomics64.HandleId64}
    (success : Atomics64.issue before owner cell actor = .ok result) :
    result.1.legacy.shared = before.legacy.shared := by
  obtain ⟨_, _, shape⟩ := Atomics64.issue_ok _ _ _ _ _ success
  simp only [shape, Atomics64.installHandle]

theorem issue_preserves_read {original : Space} {before : Managed original} {owner actor : Nat}
    {cell : Atomics64.CellId64} {result : Issued before}
    (success : issue before owner cell actor = .ok result)
    {borrower identifier : Nat} {address value : Word}
    (read : Borrowing.loadWord64 before.world.legacy.shared borrower identifier address = .ok value) :
    Borrowing.loadWord64 result.managed.world.legacy.shared borrower identifier address = .ok value := by
  have raw := issue_performed success
  apply read_stable (Atomics64.Step.issue raw).borrowing before.valid _ read
  intro identifier _
  rw [issue_shared raw]

structure Layout where
  target : Word
  stackA : Word
  stackB : Word
  returnA : Word
  returnB : Word

def standard : Layout := ⟨0x10000, 0x700008, 0x710008, 0x654320, 0x654330⟩

structure CallerReady (original : Space) where
  managed : Managed original
  identifier : Nat

/-- Both caller slots go through allocate, store64, protect and readBorrow.
They are original private slots; a later change to RSP does not select a loan. -/
def caller {original : Space} (before : Managed original) (owner actor : Nat)
    (address continuation : Word) : Except Atomics64.Fault (CallerReady original) := do
  let allocated ← mutate before (.allocate owner ⟨address, 8⟩ readWrite)
  let allocation ← ticket allocated.output
  let written ← mutate allocated.managed (.store64 owner allocation address continuation)
  let guarded ← mutate written.managed (.protect owner allocation readOnly)
  let loan ← borrow guarded.managed owner allocation actor ⟨address, 8⟩
  return ⟨loan.managed, loan.identifier⟩

/-- Proof-only evidence for the existing `CallerReady original` API. The read
is of its actual installed loan. The remaining fields retain old loans through
the real checked construction and identify the one newly consumed loan ID. -/
structure CallerReady.ReadCertificate {original : Space} (before : Managed original)
    (result : CallerReady original) (actor : Nat) (address continuation : Word) : Prop where
  read : Borrowing.loadWord64 result.managed.world.legacy.shared actor result.identifier address =
    .ok continuation
  history : Borrowing.History before.world.legacy.shared result.managed.world.legacy.shared
  loans : ∀ identifier, identifier < before.world.legacy.shared.nextLoan →
    result.managed.world.legacy.shared.loans identifier = before.world.legacy.shared.loans identifier
  identifier_eq : result.identifier = before.world.legacy.shared.nextLoan
  nextLoan_eq : result.managed.world.legacy.shared.nextLoan = before.world.legacy.shared.nextLoan + 1

/-- Decompose only the abstract successful construction, never an image or
frozen setup. Store readback, readable protection, and the actual new loan's
stored authority jointly establish the caller's word. -/
theorem caller_read_certificate {original : Space} {before : Managed original}
    {owner actor : Nat} {address continuation : Word} {result : CallerReady original}
    (success : caller before owner actor address continuation = .ok result) :
    CallerReady.ReadCertificate before result actor address continuation := by
  unfold caller at success
  obtain ⟨allocated, _, tail⟩ := bind_ok success
  obtain ⟨allocation, _, tail⟩ := bind_ok tail
  obtain ⟨written, _, tail⟩ := bind_ok tail
  obtain ⟨guarded, _, tail⟩ := bind_ok tail
  obtain ⟨loan, borrowed, tail⟩ := bind_ok tail
  have resultEq : result = ⟨loan.managed, loan.identifier⟩ := (Except.ok.inj tail).symm
  subst result
  have raw := borrow_performed borrowed
  have metadata := readBorrow_loan_metadata raw
  have frontier : guarded.managed.world.legacy.shared.nextLoan =
      before.world.legacy.shared.nextLoan :=
    guarded.nextLoan.trans (written.nextLoan.trans allocated.nextLoan)
  have stored := store_readback written.performed
  have protectedRead := protect_readback guarded.performed stored
  have observed : loadQWord (toMemory loan.managed.world.legacy.shared.resources.space) address =
      .ok continuation := by
    rw [loan.space]
    exact protectedRead
  have authorized : Borrowing.authorize loan.managed.world.legacy.shared actor loan.identifier =
      .ok ⟨allocation, owner, actor, ⟨address, 8⟩⟩ := by
    have installed : loan.managed.world.legacy.shared.loans loan.identifier =
        some ⟨allocation, owner, actor, ⟨address, 8⟩⟩ := metadata.2.2.1
    simp [Borrowing.authorize, installed]
  refine ⟨Borrowing.loadWord64_success _ _ _ _ _ _ authorized
      ⟨Nat.le_refl _, Nat.le_refl _⟩ observed, ?_, ?_,
    metadata.1.trans frontier,
    metadata.2.1.trans (congrArg (fun next : Nat => next + 1) frontier)⟩
  · exact Atomics.borrowing_trans (Atomics64.Step.mutate allocated.performed).borrowing
      (Atomics.borrowing_trans (Atomics64.Step.mutate written.performed).borrowing
        (Atomics.borrowing_trans (Atomics64.Step.mutate guarded.performed).borrowing
          (Atomics64.Step.readBorrow raw).borrowing))
  · intro identifier below
    rw [metadata.2.2.2 identifier (by rw [frontier]; exact below),
      (mutate_loan_metadata guarded.performed).1,
      (mutate_loan_metadata written.performed).1,
      (mutate_loan_metadata allocated.performed).1]

theorem CallerReady.ReadCertificate.preserves_read {original : Space} {before : Managed original}
    {result : CallerReady original} {actor : Nat} {address continuation : Word}
    (certificate : CallerReady.ReadCertificate before result actor address continuation)
    {borrower identifier : Nat} {query value : Word}
    (read : Borrowing.loadWord64 before.world.legacy.shared borrower identifier query = .ok value) :
    Borrowing.loadWord64 result.managed.world.legacy.shared borrower identifier query = .ok value :=
  read_stable certificate.history before.valid certificate.loans read

theorem caller_read_ok {original : Space} {before : Managed original}
    {owner actor : Nat} {address continuation : Word} {result : CallerReady original}
    (success : caller before owner actor address continuation = .ok result) :
    Borrowing.loadWord64 result.managed.world.legacy.shared actor result.identifier address =
      .ok continuation :=
  (caller_read_certificate success).read

theorem caller_preserves_read {original : Space} {before : Managed original}
    {owner actor : Nat} {address continuation : Word} {result : CallerReady original}
    (success : caller before owner actor address continuation = .ok result)
    {borrower identifier : Nat} {query value : Word}
    (read : Borrowing.loadWord64 before.world.legacy.shared borrower identifier query = .ok value) :
    Borrowing.loadWord64 result.managed.world.legacy.shared borrower identifier query = .ok value :=
  (caller_read_certificate success).preserves_read read

theorem caller_frontier {original : Space} {before : Managed original}
    {owner actor : Nat} {address continuation : Word} {result : CallerReady original}
    (success : caller before owner actor address continuation = .ok result) :
    result.identifier = before.world.legacy.shared.nextLoan ∧
      result.managed.world.legacy.shared.nextLoan = before.world.legacy.shared.nextLoan + 1 := by
  have certificate := caller_read_certificate success
  exact ⟨certificate.identifier_eq, certificate.nextLoan_eq⟩

structure Ready (original : Space) (layout : Layout) (old : Word) where
  managed : Managed original
  codeA : Nat
  codeB : Nat
  callerA : Nat
  callerB : Nat
  atomicA : Atomics64.HandleId64
  atomicB : Atomics64.HandleId64
  target : Atomics64.CellId64
  cell : Atomics64.Cell
  live : managed.world.cells target = some cell
  address : cell.address = layout.target
  freshTarget : allUnmapped original ⟨layout.target, 8⟩ = true
  freshCallerA : allUnmapped original ⟨layout.stackA, 8⟩ = true
  freshCallerB : allUnmapped original ⟨layout.stackB, 8⟩ = true
  initialRead : loadQWord (toMemory managed.world.legacy.shared.resources.space) layout.target = .ok old
  callerReadA : Borrowing.loadWord64 managed.world.legacy.shared 11 callerA layout.stackA = .ok layout.returnA
  callerReadB : Borrowing.loadWord64 managed.world.legacy.shared 12 callerB layout.stackB = .ok layout.returnB

theorem Ready.target_aligned {original : Space} {layout : Layout} {old : Word}
    (ready : Ready original layout old) : layout.target.toNat % 8 = 0 := by
  have supported := (ready.managed.valid.cells _ _ ready.live).2.2.1
  have aligned := of_decide_eq_true (Bool.and_eq_true_iff.mp supported).2
  simpa only [ready.address] using aligned.1

/-- Reuse a code allocation for the same entire image. Different selected
images are adopted separately; overlapping unequal images fail the real
ownership checks. No opcode family, desired method or behavior is consulted. -/
def setup (original : Space) (first second : OS.ScalarCall64.Image)
    (layout : Layout) (old : Word) : Except Atomics64.Fault (Ready original layout old) := do
  if freshTarget : allUnmapped original ⟨layout.target, 8⟩ = true then
    if freshCallerA : allUnmapped original ⟨layout.stackA, 8⟩ = true then
      if freshCallerB : allUnmapped original ⟨layout.stackB, 8⟩ = true then
        let adoptedA ← mutate (seed original) (.adopt 23 ⟨first.base, first.bytes.length⟩)
        let ticketA ← ticket adoptedA.output
        let adoptedResult ← checkedResult (if first = second then pure (adoptedA.managed, ticketA) else do
          let adoptedB ← mutate adoptedA.managed (.adopt 23 ⟨second.base, second.bytes.length⟩)
          let ticketB ← ticket adoptedB.output
          pure (adoptedB.managed, ticketB))
        let adopted := adoptedResult.val.1
        let ticketB := adoptedResult.val.2
        let codeA ← borrow adopted 23 ticketA 11 ⟨first.base, first.bytes.length⟩
        let codeB ← borrow codeA.managed 23 ticketB 12 ⟨second.base, second.bytes.length⟩
        let callerAResult ← checkedResult (caller codeB.managed 21 11 layout.stackA layout.returnA)
        let callerA := callerAResult.val
        have certificateA := caller_read_certificate callerAResult.property
        let callerBResult ← checkedResult (caller callerA.managed 22 12 layout.stackB layout.returnB)
        let callerB := callerBResult.val
        have certificateB := caller_read_certificate callerBResult.property
        let allocated ← mutate callerB.managed (.allocate 7 ⟨layout.target, 8⟩ readWrite)
        let allocation ← ticket allocated.output
        -- The target initialization is the last memory mutation. Enrollment
        -- and both handle issues retain that exact space.
        let written ← mutate allocated.managed (.store64 7 allocation layout.target old)
        let registeredResult ← checkedResult (enroll written.managed 7 allocation layout.target)
        let registered := registeredResult.val
        let oneResult ← checkedResult (issue registered.managed 7 registered.identifier 11)
        let one := oneResult.val
        let twoResult ← checkedResult (issue one.managed 7 registered.identifier 12)
        let two := twoResult.val
        have callerAAtB := certificateB.preserves_read certificateA.read
        have callerAAtStore := written.preserves_read (allocated.preserves_read callerAAtB)
        have callerBAtStore := written.preserves_read (allocated.preserves_read certificateB.read)
        have callerAAtEnroll := enroll_preserves_read registeredResult.property callerAAtStore
        have callerBAtEnroll := enroll_preserves_read registeredResult.property callerBAtStore
        have callerAAtOne := issue_preserves_read oneResult.property callerAAtEnroll
        have callerBAtOne := issue_preserves_read oneResult.property callerBAtEnroll
        return ⟨two.managed, codeA.identifier, codeB.identifier,
          callerA.identifier, callerB.identifier, one.identifier, two.identifier,
          registered.identifier, ⟨7, allocation, layout.target⟩,
          by rw [two.cells, one.cells]; exact registered.live,
          rfl, freshTarget, freshCallerA, freshCallerB, by
            rw [two.space, one.space, registered.space]
            exact store_readback written.performed,
          issue_preserves_read twoResult.property callerAAtOne,
          issue_preserves_read twoResult.property callerBAtOne⟩
      else throw .executable
    else throw .executable
  else throw .executable

/-- Setup always consumes two code loan IDs before the caller loan IDs.
This follows from successful abstract operations and the seed frontier, for
either code-adoption branch and an arbitrary original complete space. -/
theorem setup_callerIds {original : Space} {first second : OS.ScalarCall64.Image}
    {layout : Layout} {old : Word} {ready : Ready original layout old}
    (success : setup original first second layout old = .ok ready) :
    ready.callerA = 2 ∧ ready.callerB = 3 := by
  have freshTarget : allUnmapped original ⟨layout.target, 8⟩ = true := by
    by_cases checked : allUnmapped original ⟨layout.target, 8⟩ = true
    · exact checked
    · simp [setup, checked] at success
  have freshCallerA : allUnmapped original ⟨layout.stackA, 8⟩ = true := by
    by_cases checked : allUnmapped original ⟨layout.stackA, 8⟩ = true
    · exact checked
    · simp [setup, freshTarget, checked] at success
  have freshCallerB : allUnmapped original ⟨layout.stackB, 8⟩ = true := by
    by_cases checked : allUnmapped original ⟨layout.stackB, 8⟩ = true
    · exact checked
    · simp [setup, freshTarget, freshCallerA, checked] at success
  simp only [setup, dite_eq_left freshTarget, dite_eq_left freshCallerA, dite_eq_left freshCallerB] at success
  obtain ⟨adoptedA, _, tail⟩ := bind_ok success
  obtain ⟨ticketA, _, tail⟩ := bind_ok tail
  obtain ⟨adoptedResult, _, tail⟩ := bind_ok tail
  rcases adoptedResult with ⟨⟨adopted, ticketB⟩, adoption⟩
  obtain ⟨codeA, codeASuccess, tail⟩ := bind_ok tail
  obtain ⟨codeB, codeBSuccess, tail⟩ := bind_ok tail
  obtain ⟨callerAResult, _, tail⟩ := bind_ok tail
  obtain ⟨callerBResult, _, tail⟩ := bind_ok tail
  obtain ⟨allocated, _, tail⟩ := bind_ok tail
  obtain ⟨allocation, _, tail⟩ := bind_ok tail
  obtain ⟨written, _, tail⟩ := bind_ok tail
  obtain ⟨registeredResult, _, tail⟩ := bind_ok tail
  obtain ⟨oneResult, _, tail⟩ := bind_ok tail
  obtain ⟨twoResult, _, tail⟩ := bind_ok tail
  have selectedA : callerAResult.val.identifier = ready.callerA :=
    congrArg (fun output : Ready original layout old => output.callerA) (Except.ok.inj tail)
  have selectedB : callerBResult.val.identifier = ready.callerB :=
    congrArg (fun output : Ready original layout old => output.callerB) (Except.ok.inj tail)
  have adoptedNext : adopted.world.legacy.shared.nextLoan = 0 := by
    by_cases same : first = second
    · simp only [ite_eq_left same] at adoption
      have managedEq : adoptedA.managed = adopted := congrArg Prod.fst (Except.ok.inj adoption)
      rw [← managedEq]
      exact adoptedA.nextLoan
    · simp only [ite_eq_right same] at adoption
      obtain ⟨adoptedB, _, remaining⟩ := bind_ok adoption
      obtain ⟨otherTicket, _, remaining⟩ := bind_ok remaining
      have managedEq : adoptedB.managed = adopted := congrArg Prod.fst (Except.ok.inj remaining)
      rw [← managedEq]
      exact adoptedB.nextLoan.trans adoptedA.nextLoan
  have codeAFrontier := borrow_frontier codeASuccess
  have codeBFrontier := borrow_frontier codeBSuccess
  have codeBNext : codeB.managed.world.legacy.shared.nextLoan = 2 := by
    rw [codeBFrontier.2, codeAFrontier.2, adoptedNext]
  have certificateA := caller_read_certificate callerAResult.property
  have certificateB := caller_read_certificate callerBResult.property
  have callerAId : callerAResult.val.identifier = 2 := certificateA.identifier_eq.trans codeBNext
  have callerANext : callerAResult.val.managed.world.legacy.shared.nextLoan = 3 := by
    rw [certificateA.nextLoan_eq, codeBNext]
  have callerBId : callerBResult.val.identifier = 3 := certificateB.identifier_eq.trans callerANext
  exact ⟨selectedA.symm.trans callerAId, selectedB.symm.trans callerBId⟩

end EDSL.Corpus.PlainResources

#audit_edsl
