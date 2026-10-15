/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads
import EDSL.Audit

namespace EDSL.Tests.AtomicWorkers
open X86 OS.AddressSpace
abbrev TState := OS.AtomicThreads.State
abbrev Fault := OS.AtomicThreads.Fault
abbrev Start := OS.AtomicThreads.Start

def seed (old : BitVec 32) : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0x89, readExecute⟩
    | 4097 => some ⟨0xf0, readExecute⟩
    | 4098 => some ⟨0x87, readExecute⟩
    | 4099 => some ⟨0x07, readExecute⟩
    | 4100 => some ⟨0xc3, readExecute⟩
    | 32769 => some ⟨0x20, readOnly⟩
    | 32785 => some ⟨0x30, readOnly⟩
    | 32768 | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 |
      32784 | 32786 | 32787 | 32788 | 32789 | 32790 | 32791 => some ⟨0, readOnly⟩
    | 65536 => some ⟨old.extractLsb' 0 8, readWrite⟩
    | 65537 => some ⟨old.extractLsb' 8 8, readWrite⟩
    | 65538 => some ⟨old.extractLsb' 16 8, readWrite⟩
    | 65539 => some ⟨old.extractLsb' 24 8, readWrite⟩
    | 65540 => some ⟨0xd8, readWrite⟩
    | 65541 => some ⟨0xc7, readWrite⟩
    | 65542 => some ⟨0xb6, readWrite⟩
    | 65543 => some ⟨0xa5, readWrite⟩
    | _ => none

def entry (stack argument flags : Word) : OS.AtomicThreads.Context where
  registers register := if register = .rdi then 65536 else if register = .rsp then stack
    else if register = .rsi then argument else 0xdeadbeefcafebabe
  rip := 4096
  flags := flags

def withTicket (state : TState) (operation : OS.Ownership.Mutation) :
    Except Fault (TState × OS.Ownership.Ticket) := do
  let (after, result) ← OS.AtomicThreads.mutate state operation
  match result with
  | some ticket => pure (after, ticket)
  | none => throw .missingThread

def setupIn (space : Space) (a b : Word) : Except Fault (TState × Start × Start) := do
  let initial := OS.AtomicThreads.empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty space)))
  let (data, dataTicket) ← withTicket initial (.adopt 0 ⟨65536, 8⟩)
  let (code, codeTicket) ← withTicket data (.adopt 0 ⟨4096, 5⟩)
  let (oneStack, stackA) ← withTicket code (.adopt 0 ⟨32768, 8⟩)
  let (both, stackB) ← withTicket oneStack (.adopt 0 ⟨32784, 8⟩)
  pure (both, ⟨entry 32768 a 0x8d7, dataTicket, codeTicket, stackA⟩,
    ⟨entry 32784 b 0x246, dataTicket, codeTicket, stackB⟩)

def setup : Except Fault (TState × Start × Start) :=
  setupIn (seed 0x11223344) 0xfeedface89abcdef 0xdeadbeef76543210

def failureIs {α : Type} (operation : Except Fault α) (expected : Fault) : Bool :=
  match operation with
  | .error actual => decide (actual = expected)
  | .ok _ => false

def completedContext (state : TState) (identifier : Nat) : Except Fault (Word × Word × Word) := do
  let some worker := state.workers identifier | throw .missingThread
  match worker.phase with
  | .completed _ context => pure (context.registers .rsp, context.rip, context.flags)
  | _ => throw .notCompleted

structure Observation where
  a : Word
  b : Word
  cell : Option (BitVec 32)
  guard : Option (BitVec 32)
  contexts : List (Word × Word × Word)
  events : List (Nat × AtomicEvent)
  pinnedAfterFirstJoin : Bool
  deriving DecidableEq, Repr

def twoWorkers (selections : List Nat) : Except Fault Observation := do
  let (initial, a, b) ← setup
  let (one, aId) ← OS.AtomicThreads.spawn initial 0 a
  let (both, bId) ← OS.AtomicThreads.spawn one 0 b
  let (done, events) ← OS.AtomicThreads.schedule both selections
  let aContext ← completedContext done aId
  let bContext ← completedContext done bId
  let (first, aValue) ← OS.AtomicThreads.join done 0 aId
  let pinned := failureIs (OS.AtomicThreads.mutate first (.store 0 a.dataTicket 65536 0)) (.atomic .reserved)
  let (joined, bValue) ← OS.AtomicThreads.join first 0 bId
  pure ⟨aValue, bValue, (loadDWord (toMemory joined.shared.shared.resources.space) 65536).toOption,
    (loadDWord (toMemory joined.shared.shared.resources.space) 65540).toOption,
    [aContext, bContext], events, pinned⟩

def aFirst : Observation := ⟨0x11223344, 0x89abcdef, some 0x76543210, some 0xa5b6c7d8,
  [(32776, 8192, 0x8d7), (32792, 12288, 0x246)],
  [(0, ⟨65536, 0x11223344, 0x89abcdef⟩), (1, ⟨65536, 0x89abcdef, 0x76543210⟩)], true⟩

def bFirst : Observation := ⟨0x76543210, 0x11223344, some 0x89abcdef, some 0xa5b6c7d8,
  [(32776, 8192, 0x8d7), (32792, 12288, 0x246)],
  [(1, ⟨65536, 0x11223344, 0x76543210⟩), (0, ⟨65536, 0x76543210, 0x89abcdef⟩)], true⟩

-- All twenty order-preserving interleavings of two real three-instruction
-- routines. Expected old words, events, guard bytes and return states are
-- independent fixed outcomes for the two possible XCHG orders.
def aFirstSchedules : List (List Nat) :=
  [[0,0,0,1,1,1], [0,0,1,0,1,1], [0,0,1,1,0,1], [0,0,1,1,1,0],
   [0,1,0,0,1,1], [0,1,0,1,0,1], [0,1,0,1,1,0],
   [1,0,0,0,1,1], [1,0,0,1,0,1], [1,0,0,1,1,0]]

def bFirstSchedules : List (List Nat) :=
  [[0,1,1,0,0,1], [0,1,1,0,1,0], [0,1,1,1,0,0],
   [1,0,1,0,0,1], [1,0,1,0,1,0], [1,0,1,1,0,0],
   [1,1,0,0,0,1], [1,1,0,0,1,0], [1,1,0,1,0,0], [1,1,1,0,0,0]]

example : aFirstSchedules.all (fun selections => decide ((twoWorkers selections).toOption = some aFirst)) = true := by decide
example : bFirstSchedules.all (fun selections => decide ((twoWorkers selections).toOption = some bFirst)) = true := by decide

-- Early/premature collection, extra selection, wrong parent and stale thread
-- IDs must not bypass the actual three-instruction lifecycle.
def lifecycle : Except Fault (List Bool × Word × Nat) := do
  let (initial, a, _) ← setup
  let (started, id) ← OS.AtomicThreads.spawn initial 0 a
  let firstEarly := failureIs (OS.AtomicThreads.join started 0 id) .notCompleted
  let (prepared, _) ← OS.AtomicThreads.dispatch started id
  let secondEarly := failureIs (OS.AtomicThreads.join prepared 0 id) .notCompleted
  let (exchanged, _) ← OS.AtomicThreads.dispatch prepared id
  let lastEarly := failureIs (OS.AtomicThreads.join exchanged 0 id) .notCompleted
  let wrongParent := failureIs (OS.AtomicThreads.join exchanged 9 id) .wrongParent
  let (done, _) ← OS.AtomicThreads.dispatch exchanged id
  let extra := failureIs (OS.AtomicThreads.dispatch done id) .alreadyCompleted
  let (joined, value) ← OS.AtomicThreads.join done 0 id
  let staleJoin := failureIs (OS.AtomicThreads.join joined 0 id) .missingThread
  let (again, fresh) ← OS.AtomicThreads.spawn joined 0 a
  let staleSelect := failureIs (OS.AtomicThreads.dispatch again id) .missingThread
  let (finished, _) ← OS.AtomicThreads.schedule again [fresh, fresh, fresh]
  let (_, next) ← OS.AtomicThreads.join finished 0 fresh
  if value ≠ 0x11223344 then throw .unexpectedStep
  pure ([firstEarly, secondEarly, lastEarly, wrongParent, extra, staleJoin, staleSelect], next, fresh)

example : lifecycle = .ok ([true, true, true, true, true, true, true], 0x89abcdef, 1) := by rfl

def failuresAndInterference : Except Fault (List Bool × Word × Option (BitVec 32)) := do
  let (initial, a, _) ← setup
  let invalid := { a with dataTicket := ⟨99, 0⟩ }
  let failed := failureIs (OS.AtomicThreads.spawn initial 0 invalid) (.atomic (.authority (.ownership .missingAllocation)))
  let unavailable := failureIs (OS.AtomicThreads.spawn initial 0 a false) .creationFailed
  let rootOnly := failureIs (OS.AtomicThreads.spawn initial 9 a) .wrongParent
  let (started, id) ← OS.AtomicThreads.spawn initial 0 a
  let (loaded, _) ← OS.AtomicThreads.dispatch started id
  let checks := [failed, unavailable, rootOnly,
    failureIs (OS.AtomicThreads.mutate loaded (.protect 0 a.codeTicket readOnly)) (.atomic (.authority .borrowed)),
    failureIs (OS.AtomicThreads.mutate loaded (.release 0 a.stackTicket)) (.atomic (.authority .borrowed)),
    failureIs (OS.AtomicThreads.mutate loaded (.store 0 a.dataTicket 65540 0)) (.atomic .reserved),
    failureIs (OS.AtomicThreads.mutate loaded (.transfer 0 a.dataTicket 9)) (.atomic .reserved)]
  let (other, ticket) ← withTicket loaded (.allocate 0 ⟨131072, 4⟩ readWrite)
  let (changed, _) ← OS.AtomicThreads.mutate other (.store 0 ticket 131072 0x76543210)
  let (done, _) ← OS.AtomicThreads.schedule changed [id, id]
  let (joined, value) ← OS.AtomicThreads.join done 0 id
  pure (checks, value, (loadDWord (toMemory joined.shared.shared.resources.space) 131072).toOption)

example : failuresAndInterference = .ok ([true, true, true, true, true, true, true], 0x11223344, some 0x76543210) := by rfl

def changedCell (address : Word) (cell : Cell) : Space :=
  ⟨fun query => if query = address then some cell else (seed 0x11223344).cells query⟩

def rejectedStart (space : Space) (expected : Fault) : Except Fault Bool := do
  let (initial, a, _) ← setupIn space 0 0
  pure (failureIs (OS.AtomicThreads.spawn initial 0 a) expected)

example : rejectedStart (changedCell 4098 ⟨0x8b, readExecute⟩) .unsupportedCode = .ok true := by rfl
example : rejectedStart (changedCell 65539 ⟨0x11, readOnly⟩) (.atomic (.machine (.writeDenied 65536))) = .ok true := by rfl

-- Symbolic nonvacuity: arbitrary old and replacement words pass checked
-- adoption and spawn before the actual three-instruction schedule and join.
-- In particular, no invariant requires a chosen initial shared data value.
def dataWorld (old : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (OS.Ownership.empty (seed old)) (seed old) 0 ⟨65536, 8⟩

def codeWorld (old : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (dataWorld old) (seed old) 0 ⟨4096, 5⟩

def fullWorld (old : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (codeWorld old) (seed old) 0 ⟨32768, 8⟩

theorem data_adopted (old : BitVec 32) :
    OS.Ownership.adopt (OS.Ownership.empty (seed old)) 0 ⟨65536, 8⟩ =
      .ok (dataWorld old, ⟨0, 0⟩) :=
  OS.Ownership.adopt_success _ _ _ (OS.Ownership.empty_wellFormed _) (by decide) (by rfl) (by rfl)

theorem data_valid (old : BitVec 32) : OS.Ownership.WellFormed (dataWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (OS.Ownership.empty_wellFormed _) (data_adopted old)).1

theorem code_adopted (old : BitVec 32) :
    OS.Ownership.adopt (dataWorld old) 0 ⟨4096, 5⟩ = .ok (codeWorld old, ⟨1, 0⟩) :=
  OS.Ownership.adopt_success _ _ _ (data_valid old) (by decide) (by rfl) (by rfl)

theorem code_valid (old : BitVec 32) : OS.Ownership.WellFormed (codeWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (data_valid old) (code_adopted old)).1

theorem stack_adopted (old : BitVec 32) :
    OS.Ownership.adopt (codeWorld old) 0 ⟨32768, 8⟩ = .ok (fullWorld old, ⟨2, 0⟩) :=
  OS.Ownership.adopt_success _ _ _ (code_valid old) (by decide) (by rfl) (by rfl)

theorem full_valid (old : BitVec 32) : OS.Ownership.WellFormed (fullWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (code_valid old) (stack_adopted old)).1

def symbolicInitial (old : BitVec 32) : TState :=
  OS.AtomicThreads.empty (OS.Atomics.empty (OS.Borrowing.empty (fullWorld old)))

def symbolicStart (replacement : BitVec 32) : Start :=
  ⟨entry 32768 (replacement.setWidth 64) 0x8d7, ⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩⟩

def protectedCode (old : BitVec 32) : OS.Atomics.State :=
  { (symbolicInitial old).shared with
    shared := OS.Borrowing.installLoan (symbolicInitial old).shared.shared ⟨⟨1, 0⟩, 0, 1, ⟨4096, 5⟩⟩ }

def protectedStack (old : BitVec 32) : OS.Atomics.State :=
  { (protectedCode old) with
    shared := OS.Borrowing.installLoan (protectedCode old).shared ⟨⟨2, 0⟩, 0, 1, ⟨32768, 8⟩⟩ }

def protectedData (old : BitVec 32) : OS.Atomics.State :=
  OS.Atomics.install (protectedStack old) ⟨0, ⟨0, 0⟩, 1, 65536⟩

def symbolicWorker (replacement : BitVec 32) : OS.AtomicThreads.Worker :=
  ⟨0, (symbolicStart replacement).entry, 8192, 0, 0, 1, .preparing (symbolicStart replacement).entry⟩

def born (old replacement : BitVec 32) : TState :=
  OS.AtomicThreads.install (symbolicInitial old) (protectedData old) (symbolicWorker replacement)

theorem symbolic_created (old replacement : BitVec 32) :
    OS.AtomicThreads.spawn (symbolicInitial old) 0 (symbolicStart replacement) = .ok (born old replacement, 0) := by
  have code : OS.AtomicThreads.codeMatches (seed old) 4096 = true := by rfl
  have target : readWord (toMemory (seed old)) 32768 = .ok 8192 := by rfl
  have c : OS.Atomics.readBorrow (symbolicInitial old).shared 0 ⟨1, 0⟩ 1 ⟨4096, 5⟩ =
      .ok (protectedCode old, 0) := by rfl
  have s : OS.Atomics.readBorrow (protectedCode old) 0 ⟨2, 0⟩ 1 ⟨32768, 8⟩ =
      .ok (protectedStack old, 1) := by rfl
  have d : OS.Atomics.issue (protectedStack old) 0 ⟨0, 0⟩ 1 65536 =
      .ok (protectedData old, 0) := by rfl
  change OS.AtomicThreads.spawn (symbolicInitial old) 0 (symbolicStart replacement) true = _
  simp only [OS.AtomicThreads.spawn]
  change (do
    if (0 : Nat) ≠ 0 then throw OS.AtomicThreads.Fault.wrongParent
    if !true then throw OS.AtomicThreads.Fault.creationFailed
    if false then throw OS.AtomicThreads.Fault.identityCollision
    if !OS.AtomicThreads.codeMatches (seed old) 4096 then throw OS.AtomicThreads.Fault.unsupportedCode
    let ret ← (readWord (toMemory (seed old)) 32768).mapError OS.AtomicThreads.Fault.machine
    if !canonical ret then throw (OS.AtomicThreads.Fault.machine (.noncanonicalReturn ret))
    let code ← (OS.Atomics.readBorrow (symbolicInitial old).shared 0 ⟨1, 0⟩ 1 ⟨4096, 5⟩).mapError OS.AtomicThreads.Fault.atomic
    let stack ← (OS.Atomics.readBorrow code.1 0 ⟨2, 0⟩ 1 ⟨32768, 8⟩).mapError OS.AtomicThreads.Fault.atomic
    let data ← (OS.Atomics.issue stack.1 0 ⟨0, 0⟩ 1 65536).mapError OS.AtomicThreads.Fault.atomic
    pure (OS.AtomicThreads.install (symbolicInitial old) data.1
      ⟨0, (symbolicStart replacement).entry, ret, data.2, code.2, stack.2,
        .preparing (symbolicStart replacement).entry⟩, 0)) = _
  simp only [BitVec.ofNat_eq_ofNat] at code target c s d
  simp [code, target, c, s, d, Except.mapError, canonical, born, symbolicWorker]

theorem symbolic_initial_valid (old : BitVec 32) : OS.AtomicThreads.WellFormed (symbolicInitial old) :=
  OS.AtomicThreads.empty_wellFormed _
    (OS.Atomics.empty_wellFormed _ (OS.Borrowing.empty_wellFormed _ (full_valid old)))

theorem symbolic_born_valid (old replacement : BitVec 32) : OS.AtomicThreads.WellFormed (born old replacement) :=
  OS.AtomicThreads.spawn_wellFormed _ _ _ _ _ (symbolic_initial_valid old) (symbolic_created old replacement)

theorem symbolic_input (old replacement : BitVec 32) :
    loadDWord (toMemory (born old replacement).shared.shared.resources.space) 65536 = .ok old := by
  change Except.ok (joinDWord (old.extractLsb' 0 8) (old.extractLsb' 8 8)
    (old.extractLsb' 16 8) (old.extractLsb' 24 8)) = .ok old
  rw [join_extracts]

theorem all_words_join (old replacement : BitVec 32) :
    ∃ final joined,
      OS.AtomicThreads.schedule (born old replacement) [0, 0, 0] =
        .ok (final, [(0, ⟨65536, old, replacement⟩)]) ∧
      OS.AtomicThreads.join final 0 0 = .ok joined ∧ joined.2 = old.setWidth 64 ∧
      loadDWord (toMemory joined.1.shared.shared.resources.space) 65536 = .ok replacement ∧
      OS.AtomicThreads.WellFormed joined.1 := by
  have result := OS.AtomicThreads.three_dispatches_spec (born old replacement) 0 (symbolicWorker replacement) old
    (symbolic_born_valid old replacement) (by rfl) ⟨_, rfl⟩ (symbolic_input old replacement)
  simpa [symbolicWorker, symbolicStart, entry] using result

end EDSL.Tests.AtomicWorkers

#audit_edsl
