/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.BufferResources
import EDSL.OS.Atomics64
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
        let (adopted, ticketB) ← if first = second then pure (adoptedA.managed, ticketA) else do
          let adoptedB ← mutate adoptedA.managed (.adopt 23 ⟨second.base, second.bytes.length⟩)
          let ticketB ← ticket adoptedB.output
          pure (adoptedB.managed, ticketB)
        let codeA ← borrow adopted 23 ticketA 11 ⟨first.base, first.bytes.length⟩
        let codeB ← borrow codeA.managed 23 ticketB 12 ⟨second.base, second.bytes.length⟩
        let callerA ← caller codeB.managed 21 11 layout.stackA layout.returnA
        let callerB ← caller callerA.managed 22 12 layout.stackB layout.returnB
        let allocated ← mutate callerB.managed (.allocate 7 ⟨layout.target, 8⟩ readWrite)
        let allocation ← ticket allocated.output
        -- The target initialization is the last memory mutation. Enrollment
        -- and both handle issues retain that exact space.
        let written ← mutate allocated.managed (.store64 7 allocation layout.target old)
        let registered ← enroll written.managed 7 allocation layout.target
        let one ← issue registered.managed 7 registered.identifier 11
        let two ← issue one.managed 7 registered.identifier 12
        return ⟨two.managed, codeA.identifier, codeB.identifier,
          callerA.identifier, callerB.identifier, one.identifier, two.identifier,
          registered.identifier, ⟨7, allocation, layout.target⟩,
          by rw [two.cells, one.cells]; exact registered.live,
          rfl, freshTarget, freshCallerA, freshCallerB, by
            rw [two.space, one.space, registered.space]
            exact store_readback written.performed⟩
      else throw .executable
    else throw .executable
  else throw .executable

end EDSL.Corpus.PlainResources

#audit_edsl
