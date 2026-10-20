/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallResources
import EDSL.X86.CodeCheckComplete

set_option warningAsError true

namespace EDSL.OS.CallResources.Domain
open X86 AddressSpace

/-- A declaration of a NEW modeled initial authority environment. The supplied
space is retained exactly; code/caller owners and the worker are proof-level
principals, not authenticated native OS identities. No prior resource world or
existing loan is accepted or transported by this constructor. -/
structure Initial where
  space : Space
  codeOwner : Nat
  callerOwner : Nat
  worker : Nat
  code : Word
  bytes : List Byte
  stack : Word
  returnAddress : Word

def codeRegion (initial : Initial) : Region := ⟨initial.code, initial.bytes.length⟩
def stackRegion (initial : Initial) : Region := ⟨initial.stack, 8⟩

/-- Semantic readability of a valid interval is equivalent to the finite
existing borrowing preflight; inaccessible mapped cells are not enough. -/
theorem allReadable_of_cells (space : Space) (region : Region) (valid : region.valid = true)
    (cells : ∀ address, region.Contains address →
      ∃ cell, space.cells address = some cell ∧ cell.permissions.readable = true) :
    Borrowing.allReadable space region = true := by
  apply List.all_eq_true.mpr
  intro address member
  obtain ⟨offset, inRange, addressEq⟩ := List.mem_map.mp member
  subst address
  have bound := List.mem_range.mp inRange
  have extent := (of_decide_eq_true valid).2.1
  have small : offset < 2^64 := by omega
  have total : region.base.toNat + offset < 2^64 := by omega
  have inside : region.Contains (region.base + BitVec.ofNat 64 offset) := by
    simp only [Region.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
    omega
  obtain ⟨cell, found, readable⟩ := cells _ inside
  simp only [found, readable]

/-- Exact current executable-byte evidence independently supplies all code
read permissions. No instruction decoding is used. -/
theorem code_readable (space : Space) (base : Word) (bytes : List Byte)
    (code : CodeAt (toMemory space) base bytes) :
    Borrowing.allReadable space ⟨base, bytes.length⟩ = true := by
  apply List.all_eq_true.mpr
  intro address member
  obtain ⟨offset, inRange, addressEq⟩ := List.mem_map.mp member
  subst address
  have bound : offset < bytes.length := List.mem_range.mp inRange
  have atIndex : bytes[offset]? = some bytes[offset] := List.getElem?_eq_getElem bound
  have fetched := code.2 offset bytes[offset] atIndex
  cases found : space.cells (base + BitVec.ofNat 64 offset) with
  | none => simp [fetchByte, toMemory, found] at fetched
  | some cell =>
    cases readable : cell.permissions.readable with
    | false => simp [fetchByte, toMemory, found, readable] at fetched
    | true => simp only [readable]

/-- Present mapping/value facts, independent of decoding or candidate execution.
Readability is checked over the entire registered intervals, including the
last caller byte. ABI alignment beyond the existing CallResources contract,
physical mappings and native ownership remain separate obligations. -/
structure Facts (initial : Initial) : Prop where
  codeValid : (codeRegion initial).valid = true
  stackValid : (stackRegion initial).valid = true
  separate : Ownership.Disjoint (codeRegion initial) (stackRegion initial)
  codeReadable : Borrowing.allReadable initial.space (codeRegion initial) = true
  stackReadable : Borrowing.allReadable initial.space (stackRegion initial) = true
  code : CodeAt (toMemory initial.space) initial.code initial.bytes
  stack : readWord (toMemory initial.space) initial.stack = .ok initial.returnAddress
  returnCanonical : canonical initial.returnAddress = true
  stackBound : initial.stack.toNat + 8 < 2^64
  postStackCanonical : canonical (initial.stack + 8) = true

def checkStack (initial : Initial) : Bool :=
  match readWord (toMemory initial.space) initial.stack with
  | .error _ => false
  | .ok actual => decide (actual = initial.returnAddress)

theorem checkStack_sound {initial : Initial} (checked : checkStack initial = true) :
    readWord (toMemory initial.space) initial.stack = .ok initial.returnAddress := by
  cases observed : readWord (toMemory initial.space) initial.stack with
  | error fault => simp [checkStack, observed] at checked
  | ok value =>
    have same : value = initial.returnAddress := by simpa [checkStack, observed] using checked
    exact congrArg Except.ok same

theorem checkStack_complete {initial : Initial}
    (observed : readWord (toMemory initial.space) initial.stack = .ok initial.returnAddress) :
    checkStack initial = true := by simp [checkStack, observed]

/-- Finite mapping preflight only. Success is not execution, a proof of a
functional contract, or evidence of native allocation/loan authority. -/
def check (initial : Initial) : Bool :=
  (codeRegion initial).valid && (stackRegion initial).valid &&
  decide (Ownership.Disjoint (codeRegion initial) (stackRegion initial)) &&
  Borrowing.allReadable initial.space (codeRegion initial) &&
  Borrowing.allReadable initial.space (stackRegion initial) &&
  X86.checkCode (toMemory initial.space) initial.code initial.bytes &&
  checkStack initial &&
  canonical initial.returnAddress && decide (initial.stack.toNat + 8 < 2^64) &&
  canonical (initial.stack + 8)

theorem check_sound {initial : Initial} (checked : check initial = true) : Facts initial := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at checked
  rcases checked with ⟨⟨⟨⟨⟨⟨⟨⟨⟨codeValid, stackValid⟩, separate⟩, codeReadable⟩,
    stackReadable⟩, code⟩, stack⟩, returnCanonical⟩, stackBound⟩, postStackCanonical⟩
  exact ⟨codeValid, stackValid, separate, codeReadable, stackReadable,
    X86.checkCode_sound _ _ _ code, checkStack_sound stack, returnCanonical, stackBound, postStackCanonical⟩

theorem check_complete {initial : Initial} (facts : Facts initial) : check initial = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨facts.codeValid, facts.stackValid⟩, facts.separate⟩,
    facts.codeReadable⟩, facts.stackReadable⟩, X86.checkCode_complete _ _ _ facts.code⟩,
    checkStack_complete facts.stack⟩, facts.returnCanonical⟩, facts.stackBound⟩, facts.postStackCanonical⟩

def codeTicket : Ownership.Ticket := ⟨0, 0⟩
def stackTicket : Ownership.Ticket := ⟨1, 0⟩

/-- First registration in the newly declared empty modeled registry. -/
def codeWorld (initial : Initial) : Ownership.World :=
  Ownership.install (Ownership.empty initial.space) initial.space initial.codeOwner (codeRegion initial)

/-- Exactly two disjoint registered resources. All unrelated supplied mappings
remain present and unregistered; no bytes, permissions or prior cells change. -/
def world (initial : Initial) : Ownership.World :=
  Ownership.install (codeWorld initial) initial.space initial.callerOwner (stackRegion initial)

def codeLoan (initial : Initial) : Borrowing.Loan :=
  ⟨codeTicket, initial.codeOwner, Threads.principal initial.worker, codeRegion initial⟩

def stackLoan (initial : Initial) : Borrowing.Loan :=
  ⟨stackTicket, initial.callerOwner, Threads.principal initial.worker, stackRegion initial⟩

def codeBorrowed (initial : Initial) : Borrowing.State :=
  Borrowing.installLoan (Borrowing.empty (world initial)) (codeLoan initial)

def shared (initial : Initial) : Borrowing.State :=
  Borrowing.installLoan (codeBorrowed initial) (stackLoan initial)

@[simp] theorem world_space (initial : Initial) : (world initial).space = initial.space := rfl
@[simp] theorem shared_space (initial : Initial) : (shared initial).resources.space = initial.space := rfl

theorem codeWorld_valid {initial : Initial} (facts : Facts initial) :
    Ownership.WellFormed (codeWorld initial) := by
  apply Ownership.install_wellFormed _ _ _ _ (Ownership.empty_wellFormed _) facts.codeValid
  · intro address inside
    obtain ⟨cell, found, _⟩ := Borrowing.allReadable_inside _ _ facts.codeReadable address inside
    exact ⟨cell, found⟩
  · intro _ _ found
    exact found
  · intro _ _ found
    simp [Ownership.empty] at found

theorem world_valid {initial : Initial} (facts : Facts initial) :
    Ownership.WellFormed (world initial) := by
  apply Ownership.install_wellFormed _ _ _ _ (codeWorld_valid facts) facts.stackValid
  · intro address inside
    obtain ⟨cell, found, _⟩ := Borrowing.allReadable_inside _ _ facts.stackReadable address inside
    exact ⟨cell, found⟩
  · intro _ _ found
    exact found
  · intro identifier allocation found
    by_cases zero : identifier = 0
    · subst identifier
      simp only [codeWorld, Ownership.install, Ownership.empty, ↓reduceIte,
        Option.some.injEq] at found
      subst allocation
      exact Ownership.disjoint_symm facts.separate
    · simp [codeWorld, Ownership.install, Ownership.empty, zero] at found

theorem code_owned (initial : Initial) :
    Ownership.authorize (world initial) initial.codeOwner codeTicket =
      .ok ⟨initial.codeOwner, 0, codeRegion initial⟩ := by
  simp [Ownership.authorize, world, codeWorld, Ownership.install, Ownership.empty, codeTicket]

theorem stack_owned (initial : Initial) :
    Ownership.authorize (world initial) initial.callerOwner stackTicket =
      .ok ⟨initial.callerOwner, 0, stackRegion initial⟩ := by
  simp [Ownership.authorize, world, codeWorld, Ownership.install, Ownership.empty, stackTicket]

theorem code_registered (initial : Initial) :
    (world initial).allocations 0 = some ⟨initial.codeOwner, 0, codeRegion initial⟩ := by
  simp [world, codeWorld, Ownership.install, Ownership.empty]

theorem stack_registered (initial : Initial) :
    (world initial).allocations 1 = some ⟨initial.callerOwner, 0, stackRegion initial⟩ := by
  simp [world, codeWorld, Ownership.install, Ownership.empty]

/-- Both live loans are actually issuable by the existing borrowing API in the
new modeled registry. This is not a transition from an externally owned world. -/
theorem borrow_code {initial : Initial} (facts : Facts initial) :
    Borrowing.readBorrow (Borrowing.empty (world initial)) initial.codeOwner codeTicket
      (Threads.principal initial.worker) (codeRegion initial) = .ok (codeBorrowed initial, 0) := by
  exact Borrowing.readBorrow_success _ _ _ _ _ _
    (Borrowing.empty_wellFormed _ (world_valid facts)) (code_owned initial) facts.codeValid
    ⟨Nat.le_refl _, Nat.le_refl _⟩ facts.codeReadable

theorem codeBorrowed_valid {initial : Initial} (facts : Facts initial) :
    Borrowing.WellFormed (codeBorrowed initial) :=
  (Borrowing.readBorrow_wellFormed _ _ _ _ _ _
    (Borrowing.empty_wellFormed _ (world_valid facts)) (borrow_code facts)).1

theorem borrow_stack {initial : Initial} (facts : Facts initial) :
    Borrowing.readBorrow (codeBorrowed initial) initial.callerOwner stackTicket
      (Threads.principal initial.worker) (stackRegion initial) = .ok (shared initial, 1) := by
  exact Borrowing.readBorrow_success _ _ _ _ _ _ (codeBorrowed_valid facts) (stack_owned initial)
    facts.stackValid ⟨Nat.le_refl _, Nat.le_refl _⟩ facts.stackReadable

theorem shared_valid {initial : Initial} (facts : Facts initial) :
    Borrowing.WellFormed (shared initial) :=
  (Borrowing.readBorrow_wellFormed _ _ _ _ _ _ (codeBorrowed_valid facts) (borrow_stack facts)).1

def call (initial : Initial) : Call :=
  ⟨initial.worker, initial.code, initial.stack, initial.returnAddress, initial.bytes, 0, 1⟩

theorem code_held (initial : Initial) :
    Threads.HasLoan (shared initial) initial.worker 0 (codeRegion initial) := by
  refine ⟨codeLoan initial, ?_, rfl, rfl⟩
  simp [shared, codeBorrowed, Borrowing.installLoan, Borrowing.empty]

theorem stack_held (initial : Initial) :
    Threads.HasLoan (shared initial) initial.worker 1 (stackRegion initial) := by
  refine ⟨stackLoan initial, ?_, rfl, rfl⟩
  simp [shared, codeBorrowed, Borrowing.installLoan, Borrowing.empty]

theorem contract {initial : Initial} (facts : Facts initial) : Contract (call initial) (shared initial) :=
  ⟨shared_valid facts, code_held initial, stack_held initial, facts.code, facts.stack,
    facts.returnCanonical, facts.stackBound, facts.postStackCanonical⟩

/-- The reverse implication authenticates the actual registered regions and
stored loans; it does not define admission to mean successful preflight. -/
theorem contract_facts {initial : Initial}
    (admitted : Contract (call initial) (shared initial)) : Facts initial := by
  have resources : Ownership.WellFormed (world initial) := admitted.wellFormed.1
  have codeValid := (resources.1 _ _ (code_registered initial)).2.1
  have stackValid := (resources.1 _ _ (stack_registered initial)).2.1
  have separate := resources.2 _ _ _ _ (code_registered initial) (stack_registered initial) (by decide)
  have stackLive : (shared initial).loans 1 = some (stackLoan initial) := by
    simp [shared, codeBorrowed, Borrowing.installLoan, Borrowing.empty]
  obtain ⟨_, _, _, _, _, valid, readable⟩ := (admitted.wellFormed.2 _ _ stackLive).2
  exact ⟨codeValid, stackValid, separate, code_readable _ _ _ admitted.code,
    allReadable_of_cells _ _ valid readable, admitted.code, admitted.stack,
    admitted.returnCanonical, admitted.stackBound, admitted.postStackCanonical⟩

/-- Original argument/ABI register choices and flags are arbitrary; only the
entry PC, original return-slot RSP and exact supplied memory are installed. -/
def machine (initial : Initial) (registers : Register → Word) (flags : Word) : X86.State where
  registers register := if register = .rsp then initial.stack else registers register
  flags := flags
  rip := initial.code
  memory := toMemory initial.space

theorem current {initial : Initial} (facts : Facts initial)
    (registers : Register → Word) (flags : Word) :
    Current (call initial) (shared initial) (machine initial registers flags) :=
  ⟨contract facts, rfl⟩

/-- An inhabited ordinary-call domain at the SUPPLIED numeric entry, with no
decode, CFG, execution, successful result or desired output premise. -/
structure Callable (initial : Initial) where
  state : X86.State
  admitted : Current (call initial) (shared initial) state
  entry : state.rip = initial.code
  caller : state.registers .rsp = initial.stack

def callable {initial : Initial} (facts : Facts initial)
    (registers : Register → Word) (flags : Word) : Callable initial :=
  ⟨machine initial registers flags, current facts registers flags, rfl, by simp [machine]⟩

theorem nonempty {initial : Initial} (facts : Facts initial) : Nonempty (Callable initial) :=
  ⟨callable facts (fun _ => 0) 0⟩

theorem checked_nonempty {initial : Initial} (checked : check initial = true) :
    Nonempty (Callable initial) := nonempty (check_sound checked)

/-- Exact nonvacuity characterization for this NEW modeled initial registry.
It grants no statement about an existing/native ownership environment. -/
theorem nonempty_iff (initial : Initial) : Nonempty (Callable initial) ↔ check initial = true := by
  constructor
  · rintro ⟨entry⟩
    exact check_complete (contract_facts entry.admitted.contract)
  · exact checked_nonempty

end EDSL.OS.CallResources.Domain
