/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Threads
import EDSL.Examples.Compiler.MemoryWitness
import EDSL.Audit

namespace EDSL.Tests.Threads
open X86 OS.AddressSpace
abbrev TState := OS.Threads.State
abbrev Fault := OS.Threads.Fault
abbrev Start := OS.Threads.Start
abbrev Ticket := OS.Ownership.Ticket

-- Independent byte layout: two data words, shared actual load/RET bytes and
-- separate return stacks. Permissions come from each region's purpose.
def seed : Space where
  cells address :=
    match address.toNat with
    | 4096 => some ⟨0x8b, readExecute⟩
    | 4097 => some ⟨0x07, readExecute⟩
    | 4098 => some ⟨0xc3, readExecute⟩
    | 32768 | 32784 => some ⟨0, readWrite⟩
    | 32769 => some ⟨0x20, readWrite⟩
    | 32785 => some ⟨0x30, readWrite⟩
    | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 |
      32786 | 32787 | 32788 | 32789 | 32790 | 32791 => some ⟨0, readWrite⟩
    | 65536 => some ⟨0x44, readWrite⟩
    | 65537 => some ⟨0x33, readWrite⟩
    | 65538 => some ⟨0x22, readWrite⟩
    | 65539 => some ⟨0x11, readWrite⟩
    | 65540 => some ⟨0xef, readWrite⟩
    | 65541 => some ⟨0xcd, readWrite⟩
    | 65542 => some ⟨0xab, readWrite⟩
    | 65543 => some ⟨0x89, readWrite⟩
    | _ => none

def entry (data stack : Word) : OS.Threads.Context where
  registers register := if register = .rdi then data else if register = .rsp then stack else 0
  rip := 4096
  flags := 0x202

def setupIn (space : Space) : Except Fault (TState × Start × Start) := do
  let (data, dataTicket) ← (OS.Ownership.adopt (OS.Ownership.empty space) 0 ⟨65536, 8⟩).mapError
    (fun fault => OS.Threads.Fault.borrowing (.ownership fault))
  let (code, codeTicket) ← (OS.Ownership.adopt data 0 ⟨4096, 3⟩).mapError
    (fun fault => OS.Threads.Fault.borrowing (.ownership fault))
  let (stackA, stackTicketA) ← (OS.Ownership.adopt code 0 ⟨32768, 8⟩).mapError
    (fun fault => OS.Threads.Fault.borrowing (.ownership fault))
  let (both, stackTicketB) ← (OS.Ownership.adopt stackA 0 ⟨32784, 8⟩).mapError
    (fun fault => OS.Threads.Fault.borrowing (.ownership fault))
  return (OS.Threads.empty (OS.Borrowing.empty both),
    ⟨entry 65536 32768, dataTicket, codeTicket, stackTicketA⟩,
    ⟨entry 65540 32784, dataTicket, codeTicket, stackTicketB⟩)

def setup : Except Fault (TState × Start × Start) := setupIn seed

def failureIs {α : Type} (operation : Except Fault α) (expected : Fault) : Bool :=
  match operation with
  | .error observed => decide (observed = expected)
  | .ok _ => false

def wordIs (operation : Except Error (BitVec 32)) (expected : BitVec 32) : Bool :=
  match operation with
  | .error _ => false
  | .ok actual => decide (actual = expected)

def twoResults (selections : List Nat) : Except Fault (Word × Word × Bool) := do
  let (initial, a, b) ← setup
  let (first, firstId) ← OS.Threads.spawn initial 0 a
  let (both, secondId) ← OS.Threads.spawn first 0 b
  let done ← OS.Threads.schedule both selections
  let (one, va) ← OS.Threads.join done 0 firstId
  let stillFrozen := failureIs (OS.Threads.mutate one (.store 0 a.dataTicket 65536 0)) (.borrowing .borrowed)
  let (joined, vb) ← OS.Threads.join one 0 secondId
  let (stored, _) ← OS.Threads.mutate joined (.store 0 a.dataTicket 65536 0xaabbccdd)
  return (va, vb, stillFrozen && wordIs (loadDWord (toMemory stored.shared.resources.space) 65536) 0xaabbccdd)

-- All six order-preserving interleavings of two actual two-instruction workers.
-- The expected words are independent of thread metadata and scheduler logic.
example : twoResults [0, 0, 1, 1] = .ok (0x11223344, 0x89abcdef, true) := by rfl
example : twoResults [0, 1, 0, 1] = .ok (0x11223344, 0x89abcdef, true) := by rfl
example : twoResults [0, 1, 1, 0] = .ok (0x11223344, 0x89abcdef, true) := by rfl
example : twoResults [1, 0, 0, 1] = .ok (0x11223344, 0x89abcdef, true) := by rfl
example : twoResults [1, 0, 1, 0] = .ok (0x11223344, 0x89abcdef, true) := by rfl
example : twoResults [1, 1, 0, 0] = .ok (0x11223344, 0x89abcdef, true) := by rfl

def lifecycle : Except Fault (List Bool × Word) := do
  let (initial, a, _) ← setup
  let (started, id) ← OS.Threads.spawn initial 0 a
  let early := failureIs (OS.Threads.join started 0 id) .notCompleted
  let loaded ← OS.Threads.dispatch started id
  let checks := [early,
    failureIs (OS.Threads.join loaded 0 id) .notCompleted,
    failureIs (OS.Threads.join loaded 9 id) .wrongParent,
    failureIs (OS.Threads.mutate loaded (.protect 0 a.codeTicket readOnly)) (.borrowing .borrowed),
    failureIs (OS.Threads.mutate loaded (.release 0 a.stackTicket)) (.borrowing .borrowed),
    failureIs (OS.Threads.mutate loaded (.store 0 a.dataTicket 65540 0)) (.borrowing .borrowed),
    failureIs (OS.Threads.mutate loaded (.transfer 0 a.dataTicket 9)) (.borrowing .borrowed)]
  let completed ← OS.Threads.dispatch loaded id
  let extra := failureIs (OS.Threads.dispatch completed id) .alreadyCompleted
  let (joined, value) ← OS.Threads.join completed 0 id
  let stale := failureIs (OS.Threads.join joined 0 id) .missingThread
  let (again, fresh) ← OS.Threads.spawn joined 0 a
  let oldSelection := failureIs (OS.Threads.dispatch again id) .missingThread
  let finished ← OS.Threads.schedule again [fresh, fresh]
  let (_, freshValue) ← OS.Threads.join finished 0 fresh
  return (checks ++ [extra, stale, oldSelection, decide (value = 0x11223344)], freshValue)

example : lifecycle = .ok
    ([true, true, true, true, true, true, true, true, true, true, true], 0x11223344) := by rfl

-- A managed mutation to unborrowed memory remains possible between instructions.
-- Failure after the first two loan issuances must not expose any partial state.
def failuresAndInterference : Except Fault (List Bool × Word × Except Error (BitVec 32)) := do
  let (initial, a, _) ← setup
  let rejected := { a with stackTicket := ⟨99, 0⟩ }
  let failed := failureIs (OS.Threads.spawn initial 0 rejected) (.borrowing (.ownership .missingAllocation))
  let unavailable := failureIs (OS.Threads.spawn initial 0 a false) .creationFailed
  let rootOnly := failureIs (OS.Threads.spawn initial 7 a) .wrongParent
  let (started, id) ← OS.Threads.spawn initial 0 a
  let loaded ← OS.Threads.dispatch started id
  let (allocated, allocation) ← OS.Threads.mutate loaded (.allocate 0 ⟨131072, 4⟩ readWrite)
  let ticket ← match allocation with
    | none => .error .missingThread
    | some ticket => .ok ticket
  let (changed, _) ← OS.Threads.mutate allocated (.store 0 ticket 131072 0x55667788)
  let returned ← OS.Threads.dispatch changed id
  let (joined, value) ← OS.Threads.join returned 0 id
  return ([failed, unavailable, rootOnly,
    failureIs (OS.Threads.dispatch initial 0) .missingThread], value,
    loadDWord (toMemory joined.shared.resources.space) 131072)

example : failuresAndInterference = .ok ([true, true, true, true], 0x11223344, .ok 0x55667788) := by rfl

def replacedCell (address : Word) (cell : Cell) : Space :=
  ⟨fun query => if query = address then some cell else seed.cells query⟩

def rejectedStart (space : Space) (expected : Fault) : Except Fault Bool := do
  let (initial, a, _) ← setupIn space
  return failureIs (OS.Threads.spawn initial 0 a) expected

-- Byte binding, execute permission, the last data byte and the return target
-- are checked independently; failure does not count as a security verdict.
example : rejectedStart (replacedCell 4096 ⟨0x90, readExecute⟩) .unsupportedCode = .ok true := by rfl
example : rejectedStart (replacedCell 4098 ⟨0xc3, readOnly⟩) .unsupportedCode = .ok true := by rfl
example : rejectedStart (replacedCell 65539 ⟨0x11, inaccessible⟩) (.machine (.inaccessibleData 65539)) =
    .ok true := by rfl
example : rejectedStart (replacedCell 32773 ⟨0x80, readWrite⟩)
    (.machine (.noncanonicalReturn 0x0000800000002000)) = .ok true := by rfl

-- Even a manually constructed state cannot route a memory-writing instruction
-- through this read-worker dispatcher. The raw instruction genuinely writes.
def storeSpace : Space := ⟨fun address =>
  if address = 4096 then some ⟨0x89, readExecute⟩
  else if address = 4097 then some ⟨0x37, readExecute⟩ else seed.cells address⟩

def outOfProfile : Bool :=
  let context := entry 65536 32768
  let worker : OS.Threads.Worker := ⟨0, context, 0, 8192, 0, 1, 2, .loading context⟩
  let state : TState := ⟨OS.Borrowing.empty (OS.Ownership.empty storeSpace), 1,
    fun identifier => if identifier = 0 then some worker else none⟩
  let actualWrite := match X86.step (context.snapshot storeSpace) with
    | .ok (.next actual) => wordIs (loadDWord actual.memory 65536) 0
    | _ => false
  actualWrite && failureIs (OS.Threads.dispatch state 0) .unexpectedStep

example : outOfProfile = true := by rfl

-- Symbolic nonvacuity through checked adoption, spawn, both actual instructions
-- and join. No selected data word is excluded by a fixture's constant value.
open Examples.Compiler.MemoryOps

def caller (value : BitVec 32) : Space where
  cells address := ((dataMemory 0x8b 0x07 value).read address).map fun byte =>
    ⟨byte, ⟨true, (dataMemory 0x8b 0x07 value).writable address,
      (dataMemory 0x8b 0x07 value).executable address⟩⟩

def dataWorld (value : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (OS.Ownership.empty (caller value)) (caller value) 0 ⟨65536, 4⟩

def codeWorld (value : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (dataWorld value) (caller value) 0 ⟨4096, 3⟩

def fullWorld (value : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (codeWorld value) (caller value) 0 ⟨32768, 8⟩

theorem data_adopted (value : BitVec 32) :
    OS.Ownership.adopt (OS.Ownership.empty (caller value)) 0 ⟨65536, 4⟩ = .ok (dataWorld value, ⟨0, 0⟩) := by
  exact OS.Ownership.adopt_success _ _ _ (OS.Ownership.empty_wellFormed _) (by decide) (by rfl) (by rfl)

theorem data_valid (value : BitVec 32) : OS.Ownership.WellFormed (dataWorld value) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (OS.Ownership.empty_wellFormed _) (data_adopted value)).1

theorem code_adopted (value : BitVec 32) :
    OS.Ownership.adopt (dataWorld value) 0 ⟨4096, 3⟩ = .ok (codeWorld value, ⟨1, 0⟩) := by
  exact OS.Ownership.adopt_success _ _ _ (data_valid value) (by decide) (by rfl) (by rfl)

theorem code_valid (value : BitVec 32) : OS.Ownership.WellFormed (codeWorld value) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (data_valid value) (code_adopted value)).1

theorem stack_adopted (value : BitVec 32) :
    OS.Ownership.adopt (codeWorld value) 0 ⟨32768, 8⟩ = .ok (fullWorld value, ⟨2, 0⟩) := by
  exact OS.Ownership.adopt_success _ _ _ (code_valid value) (by decide) (by rfl) (by rfl)

theorem full_valid (value : BitVec 32) : OS.Ownership.WellFormed (fullWorld value) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (code_valid value) (stack_adopted value)).1

def symbolicInitial (value : BitVec 32) : TState := OS.Threads.empty (OS.Borrowing.empty (fullWorld value))
def symbolicStart : Start := ⟨entry 65536 32768, ⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩⟩

def protectedData (value : BitVec 32) : OS.Borrowing.State :=
  OS.Borrowing.installLoan (symbolicInitial value).shared ⟨⟨0, 0⟩, 0, 1, ⟨65536, 4⟩⟩
def protectedCode (value : BitVec 32) : OS.Borrowing.State :=
  OS.Borrowing.installLoan (protectedData value) ⟨⟨1, 0⟩, 0, 1, ⟨4096, 3⟩⟩
def protectedStack (value : BitVec 32) : OS.Borrowing.State :=
  OS.Borrowing.installLoan (protectedCode value) ⟨⟨2, 0⟩, 0, 1, ⟨32768, 8⟩⟩
def symbolicWorker (value : BitVec 32) : OS.Threads.Worker :=
  ⟨0, symbolicStart.entry, value, 8192, 0, 1, 2, .loading symbolicStart.entry⟩
def born (value : BitVec 32) : TState :=
  OS.Threads.install (symbolicInitial value) (protectedStack value) (symbolicWorker value)

theorem caller_reads (value : BitVec 32) (address : Word) :
    (toMemory (caller value)).read address = (dataMemory 0x8b 0x07 value).read address := by
  simp only [toMemory, caller]
  cases (dataMemory 0x8b 0x07 value).read address <;> rfl

theorem symbolic_input (value : BitVec 32) :
    loadDWord (toMemory (fullWorld value).space) 65536 = .ok value :=
  (loadDWord_congr _ _ _ (fun _ _ => caller_reads value _)).trans (data_value _ _ _)

theorem symbolic_created (value : BitVec 32) :
    OS.Threads.spawn (symbolicInitial value) 0 symbolicStart = .ok (born value, 0) := by
  have code : OS.Threads.codeMatches (caller value) 4096 = true := by rfl
  have input := symbolic_input value
  have target : readWord (toMemory (caller value)) 32768 = .ok 8192 :=
    (readWord_congr _ _ _ (fun _ _ => caller_reads value _)).trans (data_stack _ _ _)
  have d : OS.Borrowing.readBorrow (symbolicInitial value).shared 0 ⟨0, 0⟩ 1 ⟨65536, 4⟩ =
      .ok (protectedData value, 0) := by rfl
  have c : OS.Borrowing.readBorrow (protectedData value) 0 ⟨1, 0⟩ 1 ⟨4096, 3⟩ =
      .ok (protectedCode value, 1) := by rfl
  have s : OS.Borrowing.readBorrow (protectedCode value) 0 ⟨2, 0⟩ 1 ⟨32768, 8⟩ =
      .ok (protectedStack value, 2) := by rfl
  change loadDWord (toMemory (caller value)) 65536 = .ok value at input
  change OS.Threads.spawn (symbolicInitial value) 0 symbolicStart true = .ok (born value, 0)
  simp only [OS.Threads.spawn]
  change (do
    if (0 : Nat) ≠ 0 then throw OS.Threads.Fault.wrongParent
    if !true then throw OS.Threads.Fault.creationFailed
    if false then throw OS.Threads.Fault.identityCollision
    if !OS.Threads.codeMatches (caller value) 4096 then throw OS.Threads.Fault.unsupportedCode
    let word ← (loadDWord (toMemory (caller value)) 65536).mapError OS.Threads.Fault.machine
    let ret ← (readWord (toMemory (caller value)) 32768).mapError OS.Threads.Fault.machine
    if !canonical ret then throw (OS.Threads.Fault.machine (.noncanonicalReturn ret))
    let data ← (OS.Borrowing.readBorrow (symbolicInitial value).shared 0 ⟨0, 0⟩ 1 ⟨65536, 4⟩).mapError OS.Threads.Fault.borrowing
    let code ← (OS.Borrowing.readBorrow data.1 0 ⟨1, 0⟩ 1 ⟨4096, 3⟩).mapError OS.Threads.Fault.borrowing
    let stack ← (OS.Borrowing.readBorrow code.1 0 ⟨2, 0⟩ 1 ⟨32768, 8⟩).mapError OS.Threads.Fault.borrowing
    pure (OS.Threads.install (symbolicInitial value) stack.1
      ⟨0, symbolicStart.entry, word, ret, data.2, code.2, stack.2, .loading symbolicStart.entry⟩, 0)) = _
  simp only [BitVec.ofNat_eq_ofNat] at code input target d c s
  simp [code, input, target, d, c, s, Except.mapError, canonical, born, symbolicWorker]

theorem symbolic_initial_valid (value : BitVec 32) : OS.Threads.WellFormed (symbolicInitial value) :=
  OS.Threads.empty_wellFormed _ (OS.Borrowing.empty_wellFormed _ (full_valid value))

theorem all_words_join (value : BitVec 32) :
    ∃ middle final joined,
      OS.Threads.dispatch (born value) 0 = .ok middle ∧ OS.Threads.dispatch middle 0 = .ok final ∧
      OS.Threads.join final 0 0 = .ok joined ∧ joined.2 = value.setWidth 64 := by
  have valid := OS.Threads.spawn_wellFormed _ _ _ _ _ (symbolic_initial_valid value) (symbolic_created value)
  obtain ⟨middle, final, _, first, second, _, _, _, _, joined, completed, result⟩ :=
    OS.Threads.two_dispatches_complete (born value) 0 (symbolicWorker value) symbolicStart.entry
      valid (by rfl) rfl
  exact ⟨middle, final, joined, first, second, completed, result⟩

theorem all_words_all_histories (value : BitVec 32) (beforeJoin : TState)
    (history : OS.Threads.History (born value) beforeJoin) (joined : TState × Word)
    (completed : OS.Threads.join beforeJoin 0 0 = .ok joined) : joined.2 = value.setWidth 64 :=
  OS.Threads.spawned_join_value (symbolicInitial value) 0 symbolicStart true (born value, 0)
    (symbolic_initial_valid value) (symbolic_created value) value (symbolic_input value) beforeJoin history joined completed

end EDSL.Tests.Threads

#audit_edsl
