/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads
import EDSL.Audit

namespace EDSL.Tests.CounterWorkersWitness
open X86 OS.AddressSpace
abbrev TState := OS.CounterThreads.State
abbrev Start := OS.CounterThreads.Start

-- This independent symbolic fixture deliberately leaves every data bit and
-- both full-width loop counts arbitrary. Admission may inspect permissions,
-- code and return stacks, but must not require a selected counter value.
def seed (old : BitVec 32) : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0xe3, readExecute⟩ | 4097 => some ⟨0x0b, readExecute⟩
    | 4098 | 4109 => some ⟨0xb8, readExecute⟩ | 4099 => some ⟨1, readExecute⟩
    | 4100 | 4101 | 4102 | 4110 | 4111 | 4112 | 4113 => some ⟨0, readExecute⟩
    | 4103 => some ⟨0xf0, readExecute⟩ | 4104 => some ⟨0x0f, readExecute⟩
    | 4105 => some ⟨0xc1, readExecute⟩ | 4106 => some ⟨0x07, readExecute⟩
    | 4107 => some ⟨0xe2, readExecute⟩ | 4108 => some ⟨0xf5, readExecute⟩
    | 4114 => some ⟨0xc3, readExecute⟩
    | 32769 => some ⟨0x20, readOnly⟩ | 32785 => some ⟨0x30, readOnly⟩
    | 32768 | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 |
      32784 | 32786 | 32787 | 32788 | 32789 | 32790 | 32791 => some ⟨0, readOnly⟩
    | 65536 => some ⟨old.extractLsb' 0 8, readWrite⟩ | 65537 => some ⟨old.extractLsb' 8 8, readWrite⟩
    | 65538 => some ⟨old.extractLsb' 16 8, readWrite⟩ | 65539 => some ⟨old.extractLsb' 24 8, readWrite⟩
    | _ => none

def entry (stack count : Word) : OS.CounterThreads.Context where
  registers register := if register = .rdi then 65536 else if register = .rsp then stack
    else if register = .rcx then count else 0xfeedface89abcdef
  rip := 4096
  flags := 0x8d7

def dataWorld (old : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (OS.Ownership.empty (seed old)) (seed old) 0 ⟨65536, 4⟩

def codeWorld (old : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (dataWorld old) (seed old) 0 ⟨4096, 19⟩

def stackWorld (old : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (codeWorld old) (seed old) 0 ⟨32768, 8⟩

def fullWorld (old : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (stackWorld old) (seed old) 0 ⟨32784, 8⟩

theorem data_adopted (old : BitVec 32) :
    OS.Ownership.adopt (OS.Ownership.empty (seed old)) 0 ⟨65536, 4⟩ =
      .ok (dataWorld old, ⟨0, 0⟩) :=
  OS.Ownership.adopt_success _ _ _ (OS.Ownership.empty_wellFormed _) (by decide) (by rfl) (by rfl)

theorem data_valid (old : BitVec 32) : OS.Ownership.WellFormed (dataWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (OS.Ownership.empty_wellFormed _) (data_adopted old)).1

theorem code_adopted (old : BitVec 32) :
    OS.Ownership.adopt (dataWorld old) 0 ⟨4096, 19⟩ = .ok (codeWorld old, ⟨1, 0⟩) :=
  OS.Ownership.adopt_success _ _ _ (data_valid old) (by decide) (by rfl) (by rfl)

theorem code_valid (old : BitVec 32) : OS.Ownership.WellFormed (codeWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (data_valid old) (code_adopted old)).1

theorem stack_adopted (old : BitVec 32) :
    OS.Ownership.adopt (codeWorld old) 0 ⟨32768, 8⟩ = .ok (stackWorld old, ⟨2, 0⟩) :=
  OS.Ownership.adopt_success _ _ _ (code_valid old) (by decide) (by rfl) (by rfl)

theorem stack_valid (old : BitVec 32) : OS.Ownership.WellFormed (stackWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (code_valid old) (stack_adopted old)).1

theorem full_adopted (old : BitVec 32) :
    OS.Ownership.adopt (stackWorld old) 0 ⟨32784, 8⟩ = .ok (fullWorld old, ⟨3, 0⟩) :=
  OS.Ownership.adopt_success _ _ _ (stack_valid old) (by decide) (by rfl) (by rfl)

theorem full_valid (old : BitVec 32) : OS.Ownership.WellFormed (fullWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (stack_valid old) (full_adopted old)).1

def initial (old : BitVec 32) : TState :=
  OS.CounterThreads.empty (OS.Atomics.empty (OS.Borrowing.empty (fullWorld old)))

def startA (count : Word) : Start :=
  ⟨entry 32768 count, ⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩⟩

def startB (count : Word) : Start :=
  ⟨entry 32784 count, ⟨0, 0⟩, ⟨1, 0⟩, ⟨3, 0⟩⟩

def codeA (old : BitVec 32) : OS.Atomics.State :=
  { (initial old).shared with
    shared := OS.Borrowing.installLoan (initial old).shared.shared ⟨⟨1, 0⟩, 0, 1, ⟨4096, 19⟩⟩ }

def stackA (old : BitVec 32) : OS.Atomics.State :=
  { (codeA old) with
    shared := OS.Borrowing.installLoan (codeA old).shared ⟨⟨2, 0⟩, 0, 1, ⟨32768, 8⟩⟩ }

def dataA (old : BitVec 32) : OS.Atomics.State :=
  OS.Atomics.install (stackA old) ⟨0, ⟨0, 0⟩, 1, 65536⟩

def workerA (count : Word) : OS.CounterThreads.Worker :=
  ⟨0, (startA count).entry, 8192, 0, 0, 1, .entry, (startA count).entry⟩

def bornA (old : BitVec 32) (count : Word) : TState :=
  OS.CounterThreads.install (initial old) (dataA old) (workerA count)

theorem createdA (old : BitVec 32) (count : Word) :
    OS.CounterThreads.spawn (initial old) 0 (startA count) = .ok (bornA old count, 0) := by
  have code : checkCode (toMemory (seed old)) 4096 OS.CounterThreads.bytes = true := by rfl
  have target : readWord (toMemory (seed old)) 32768 = .ok 8192 := by rfl
  have c : OS.Atomics.readBorrow (initial old).shared 0 ⟨1, 0⟩ 1 ⟨4096, 19⟩ =
      .ok (codeA old, 0) := by rfl
  have s : OS.Atomics.readBorrow (codeA old) 0 ⟨2, 0⟩ 1 ⟨32768, 8⟩ =
      .ok (stackA old, 1) := by rfl
  have d : OS.Atomics.issue (stackA old) 0 ⟨0, 0⟩ 1 65536 =
      .ok (dataA old, 0) := by rfl
  change OS.CounterThreads.spawn (initial old) 0 (startA count) true = _
  simp only [OS.CounterThreads.spawn]
  change (do
    if (0 : Nat) ≠ 0 then throw OS.CounterThreads.Fault.wrongParent
    if !true then throw OS.CounterThreads.Fault.creationFailed
    if false then throw OS.CounterThreads.Fault.identityCollision
    if !checkCode (toMemory (seed old)) 4096 OS.CounterThreads.bytes then throw OS.CounterThreads.Fault.unsupportedCode
    let ret ← (readWord (toMemory (seed old)) 32768).mapError OS.CounterThreads.Fault.machine
    if !canonical ret then throw (OS.CounterThreads.Fault.machine (.noncanonicalReturn ret))
    let code ← (OS.Atomics.readBorrow (initial old).shared 0 ⟨1, 0⟩ 1 ⟨4096, 19⟩).mapError OS.CounterThreads.Fault.atomic
    let stack ← (OS.Atomics.readBorrow code.1 0 ⟨2, 0⟩ 1 ⟨32768, 8⟩).mapError OS.CounterThreads.Fault.atomic
    let data ← (OS.Atomics.issue stack.1 0 ⟨0, 0⟩ 1 65536).mapError OS.CounterThreads.Fault.atomic
    pure (OS.CounterThreads.install (initial old) data.1
      ⟨0, (startA count).entry, ret, data.2, code.2, stack.2, .entry, (startA count).entry⟩, 0)) = _
  simp only [BitVec.ofNat_eq_ofNat] at code target c s d
  simp [code, target, c, s, d, Except.mapError, canonical, bornA, workerA]

theorem initial_valid (old : BitVec 32) : OS.CounterThreads.WellFormed (initial old) :=
  OS.CounterThreads.empty_wellFormed _
    (OS.Atomics.empty_wellFormed _ (OS.Borrowing.empty_wellFormed _ (full_valid old)))

theorem bornA_valid (old : BitVec 32) (count : Word) : OS.CounterThreads.WellFormed (bornA old count) :=
  OS.CounterThreads.spawn_wellFormed _ _ _ _ _ (initial_valid old) (createdA old count)

def codeB (old : BitVec 32) (a : Word) : OS.Atomics.State :=
  { (bornA old a).shared with
    shared := OS.Borrowing.installLoan (bornA old a).shared.shared ⟨⟨1, 0⟩, 0, 2, ⟨4096, 19⟩⟩ }

def stackB (old : BitVec 32) (a : Word) : OS.Atomics.State :=
  { (codeB old a) with
    shared := OS.Borrowing.installLoan (codeB old a).shared ⟨⟨3, 0⟩, 0, 2, ⟨32784, 8⟩⟩ }

def dataB (old : BitVec 32) (a : Word) : OS.Atomics.State :=
  OS.Atomics.install (stackB old a) ⟨0, ⟨0, 0⟩, 2, 65536⟩

def workerB (count : Word) : OS.CounterThreads.Worker :=
  ⟨0, (startB count).entry, 12288, 1, 2, 3, .entry, (startB count).entry⟩

def born (old : BitVec 32) (a b : Word) : TState :=
  OS.CounterThreads.install (bornA old a) (dataB old a) (workerB b)

theorem createdB (old : BitVec 32) (a b : Word) :
    OS.CounterThreads.spawn (bornA old a) 0 (startB b) = .ok (born old a b, 1) := by
  have code : checkCode (toMemory (seed old)) 4096 OS.CounterThreads.bytes = true := by rfl
  have target : readWord (toMemory (seed old)) 32784 = .ok 12288 := by rfl
  have c : OS.Atomics.readBorrow (bornA old a).shared 0 ⟨1, 0⟩ 2 ⟨4096, 19⟩ =
      .ok (codeB old a, 2) := by rfl
  have s : OS.Atomics.readBorrow (codeB old a) 0 ⟨3, 0⟩ 2 ⟨32784, 8⟩ =
      .ok (stackB old a, 3) := by rfl
  have d : OS.Atomics.issue (stackB old a) 0 ⟨0, 0⟩ 2 65536 =
      .ok (dataB old a, 1) := by rfl
  change OS.CounterThreads.spawn (bornA old a) 0 (startB b) true = _
  simp only [OS.CounterThreads.spawn]
  change (do
    if (0 : Nat) ≠ 0 then throw OS.CounterThreads.Fault.wrongParent
    if !true then throw OS.CounterThreads.Fault.creationFailed
    if false then throw OS.CounterThreads.Fault.identityCollision
    if !checkCode (toMemory (seed old)) 4096 OS.CounterThreads.bytes then throw OS.CounterThreads.Fault.unsupportedCode
    let ret ← (readWord (toMemory (seed old)) 32784).mapError OS.CounterThreads.Fault.machine
    if !canonical ret then throw (OS.CounterThreads.Fault.machine (.noncanonicalReturn ret))
    let code ← (OS.Atomics.readBorrow (bornA old a).shared 0 ⟨1, 0⟩ 2 ⟨4096, 19⟩).mapError OS.CounterThreads.Fault.atomic
    let stack ← (OS.Atomics.readBorrow code.1 0 ⟨3, 0⟩ 2 ⟨32784, 8⟩).mapError OS.CounterThreads.Fault.atomic
    let data ← (OS.Atomics.issue stack.1 0 ⟨0, 0⟩ 2 65536).mapError OS.CounterThreads.Fault.atomic
    pure (OS.CounterThreads.install (bornA old a) data.1
      ⟨0, (startB b).entry, ret, data.2, code.2, stack.2, .entry, (startB b).entry⟩, 1)) = _
  simp only [BitVec.ofNat_eq_ofNat] at code target c s d
  simp [code, target, c, s, d, Except.mapError, canonical, born, workerB]

theorem born_valid (old : BitVec 32) (a b : Word) : OS.CounterThreads.WellFormed (born old a b) :=
  OS.CounterThreads.spawn_wellFormed _ _ _ _ _ (bornA_valid old a) (createdB old a b)

theorem symbolic_input (old : BitVec 32) (a b : Word) :
    loadDWord (toMemory (born old a b).shared.shared.resources.space) 65536 = .ok old := by
  change Except.ok (joinDWord (old.extractLsb' 0 8) (old.extractLsb' 8 8)
    (old.extractLsb' 16 8) (old.extractLsb' 24 8)) = .ok old
  rw [join_extracts]

theorem born_workers (old : BitVec 32) (a b : Word) (identifier : Nat) (worker : OS.CounterThreads.Worker)
    (live : (born old a b).workers identifier = some worker) : worker = workerA a ∨ worker = workerB b := by
  change (if identifier = 1 then some (workerB b) else if identifier = 0 then some (workerA a) else none) = some worker at live
  by_cases second : identifier = 1
  · simp [second] at live
    exact Or.inr live.symm
  · by_cases first : identifier = 0
    · simp [first] at live
      exact Or.inl live.symm
    · simp [second, first] at live

-- Unlike a concrete bounded execution, this witnesses genuine completion and
-- checked collection for every pair of 64-bit counts, including zero and max.
-- The specification is the independently published natural-number sum,
-- reduced modulo the shared counter's 32-bit width.
theorem all_words_and_counts_finish (old : BitVec 32) (a b : Word) :
    ∃ finished events selections joined,
      OS.CounterThreads.finishWorkers (born old a b) (OS.CounterThreads.liveIds (born old a b)) = .ok (finished, events) ∧
      OS.CounterThreads.schedule (born old a b) selections = .ok (finished, events) ∧
      OS.CounterThreads.collect finished 0 (OS.CounterThreads.liveIds finished) = .ok joined ∧
      OS.CounterThreads.WellFormed joined.1 ∧ joined.2 = [0, 0] ∧
      (∀ identifier, joined.1.workers identifier = none) ∧
      events.length = a.toNat + b.toNat ∧
      selections.count 0 = 3 * a.toNat + 3 ∧ selections.count 1 = 3 * b.toNat + 3 ∧
      loadDWord (toMemory joined.1.shared.shared.resources.space) 65536 =
        .ok (old + BitVec.ofNat 32 (a.toNat + b.toNat)) := by
  have allAt : OS.CounterThreads.AllAt (born old a b) 65536 := by
    intro identifier worker live
    rcases born_workers old a b identifier worker live with equal | equal <;> subst worker <;> rfl
  have started : ∀ identifier worker, (born old a b).workers identifier = some worker → worker.phase = .entry := by
    intro identifier worker live
    rcases born_workers old a b identifier worker live with equal | equal <;> subst worker <;> rfl
  obtain ⟨finished, events, selections, joined, completed, scheduled, collected, valid, zeros, removed, result⟩ :=
    OS.CounterThreads.finish_collect_counter (born old a b) 65536 old (born_valid old a b) allAt
      (symbolic_input old a b) started
  have sameIds := OS.CounterThreads.schedule_liveIds _ _ _ (born_valid old a b) scheduled
  have initialIds : OS.CounterThreads.liveIds (born old a b) = [0, 1] := by rfl
  have requests : OS.CounterThreads.requested (born old a b) = a.toNat + b.toNat := by
    change a.toNat + (b.toNat + 0) = _
    omega
  have finalValid := OS.CounterThreads.schedule_wellFormed _ _ _ (born_valid old a b) scheduled
  have finalCompleted : ∀ identifier worker, finished.workers identifier = some worker → worker.phase = .completed := by
    intro identifier worker found
    have member := (OS.CounterThreads.liveIds_member finished finalValid identifier).mpr ⟨worker, found⟩
    rw [sameIds] at member
    obtain ⟨current, currentAt, phase⟩ :=
      OS.CounterThreads.finishWorkers_completed _ _ _ (born_valid old a b) completed identifier member
    have equal := Option.some.inj (currentAt.symm.trans found)
    subst current
    exact phase
  have eventCount := OS.CounterThreads.completed_total_events _ _ _ (born_valid old a b) started scheduled finalCompleted
  obtain ⟨currentA, currentAtA, selectedA⟩ := OS.CounterThreads.schedule_remaining _ _ 0 (workerA a) _
    (born_valid old a b) (by rfl) scheduled
  obtain ⟨currentB, currentAtB, selectedB⟩ := OS.CounterThreads.schedule_remaining _ _ 1 (workerB b) _
    (born_valid old a b) (by rfl) scheduled
  have zeroA := currentA.remaining_zero.mpr (finalCompleted _ _ currentAtA)
  have zeroB := currentB.remaining_zero.mpr (finalCompleted _ _ currentAtB)
  rw [zeroA, Nat.zero_add] at selectedA
  rw [zeroB, Nat.zero_add] at selectedB
  refine ⟨finished, events, selections, joined, completed, scheduled, collected, valid, ?_, removed, ?_, ?_, ?_, ?_⟩
  · simpa [sameIds, initialIds] using zeros
  · simpa only [requests] using eventCount
  · simpa [OS.CounterThreads.Worker.remaining, workerA, startA, entry] using selectedA
  · simpa [OS.CounterThreads.Worker.remaining, workerB, startB, entry] using selectedB
  · simpa only [requests] using result

end EDSL.Tests.CounterWorkersWitness

#audit_edsl
