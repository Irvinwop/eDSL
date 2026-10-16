/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Pair32.Correctness
import EDSL.X86.CodeCheck
import EDSL.Audit

namespace EDSL.Tests.Pair32Resources
open X86 OS.AddressSpace OS.ArrayResources
set_option maxRecDepth 100000

-- Code and the complete return slot are the only initial allocations. Input
-- values below enter current RAM through checked allocation/store operations.
def caller : Space where
  cells address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4096 + EDSL.Pair32.bytes.length then
      (EDSL.Pair32.bytes[address.toNat - 4096]?).map fun byte => ⟨byte, readExecute⟩
    else if (⟨65544, 8⟩ : Region).Contains address then
      some ⟨if address = 65545 then 0x20 else 0, readOnly⟩
    else none

def codeOwned : OS.Ownership.World :=
  OS.Ownership.install (OS.Ownership.empty caller) caller 7 ⟨4096, 35⟩

def stackOwned : OS.Ownership.World :=
  OS.Ownership.install codeOwned caller 7 ⟨65544, 8⟩

theorem codeOwned_valid : OS.Ownership.WellFormed codeOwned :=
  (OS.Ownership.adopt_wellFormed _ 7 ⟨4096, 35⟩ (codeOwned, ⟨0, 0⟩)
    (OS.Ownership.empty_wellFormed caller) (by rfl)).1

theorem stackOwned_valid : OS.Ownership.WellFormed stackOwned :=
  (OS.Ownership.adopt_wellFormed _ 7 ⟨65544, 8⟩ (stackOwned, ⟨1, 0⟩)
    codeOwned_valid (by rfl)).1

def codeHeld : OS.Borrowing.State := OS.Borrowing.installLoan
  (OS.Borrowing.empty stackOwned) ⟨⟨0, 0⟩, 7, 11, ⟨4096, 35⟩⟩

def emptyHeld : OS.Borrowing.State := OS.Borrowing.installLoan
  codeHeld ⟨⟨1, 0⟩, 7, 11, ⟨65544, 8⟩⟩

theorem codeHeld_valid : OS.Borrowing.WellFormed codeHeld :=
  (OS.Borrowing.readBorrow_wellFormed _ 7 ⟨0, 0⟩ 11 ⟨4096, 35⟩ (codeHeld, 0)
    (OS.Borrowing.empty_wellFormed _ stackOwned_valid) (by rfl)).1

theorem emptyHeld_valid : OS.Borrowing.WellFormed emptyHeld :=
  (OS.Borrowing.readBorrow_wellFormed _ 7 ⟨1, 0⟩ 11 ⟨65544, 8⟩ (emptyHeld, 1)
    codeHeld_valid (by rfl)).1

def emptyCall (base : Word) (unusedLoan : Nat) : Call :=
  ⟨10, ⟨0, 1, unusedLoan⟩, 4096, EDSL.Pair32.bytes, 65544, base, [], 8192⟩

theorem empty_contract (base : Word) (unusedLoan : Nat) :
    Contract emptyHeld (emptyCall base unusedLoan) := by
  refine ⟨emptyHeld_valid, ?_, ?_, ?_, currentArrayAt_nil _ _, arrayBound_nil _,
    ?_, ?_, ?_⟩
  · refine ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · intro nonempty; exact False.elim (nonempty rfl)
    · change OS.Ownership.Disjoint ⟨4096, 35⟩ ⟨65544, 8⟩
      decide
    all_goals intro nonempty; exact False.elim (nonempty rfl)
  · exact checkCode_sound (toMemory caller) 4096 EDSL.Pair32.bytes (by decide)
  · change readWord (toMemory caller) 65544 = .ok 8192
    rfl
  · change canonical 8192 = true
    decide
  · change (65544 : Word).toNat + 8 < 2^64
    decide
  · change canonical ((65544 : Word) + 8) = true
    decide

def aAllocated : OS.Borrowing.State :=
  { emptyHeld with resources :=
      OS.Ownership.install emptyHeld.resources (mapUnchecked caller ⟨131072, 8⟩ readWrite) 7 ⟨131072, 8⟩ }

def aFirst : OS.Borrowing.State :=
  { aAllocated with resources := { aAllocated.resources with
      space := writeWordCells aAllocated.resources.space 131072 0xffffffff } }

def aFilled : OS.Borrowing.State :=
  { aFirst with resources := { aFirst.resources with
      space := writeWordCells aFirst.resources.space 131076 2 } }

-- B owns twelve readable bytes, but lends only its first eight. The third
-- word is deliberately readable so authority checks must enforce the loan.
def bAllocated : OS.Borrowing.State :=
  { aFilled with resources :=
      OS.Ownership.install aFilled.resources (mapUnchecked aFilled.resources.space ⟨196608, 12⟩ readWrite) 7 ⟨196608, 12⟩ }

def bFirst : OS.Borrowing.State :=
  { bAllocated with resources := { bAllocated.resources with
      space := writeWordCells bAllocated.resources.space 196608 3 } }

def bSecond : OS.Borrowing.State :=
  { bFirst with resources := { bFirst.resources with
      space := writeWordCells bFirst.resources.space 196612 5 } }

def bFilled : OS.Borrowing.State :=
  { bSecond with resources := { bSecond.resources with
      space := writeWordCells bSecond.resources.space 196616 6 } }

def aHeld : OS.Borrowing.State :=
  OS.Borrowing.installLoan bFilled ⟨⟨2, 0⟩, 7, 11, ⟨131072, 8⟩⟩

def pairHeld : OS.Borrowing.State :=
  OS.Borrowing.installLoan aHeld ⟨⟨3, 0⟩, 7, 11, ⟨196608, 8⟩⟩

theorem input_history : OS.Borrowing.History emptyHeld pairHeld :=
  .next (.mutate (show OS.Borrowing.mutate emptyHeld (.allocate 7 ⟨131072, 8⟩ readWrite) =
    .ok (aAllocated, some ⟨2, 0⟩) from rfl))
  (.next (.mutate (show OS.Borrowing.mutate aAllocated (.store 7 ⟨2, 0⟩ 131072 0xffffffff) =
    .ok (aFirst, none) from rfl))
  (.next (.mutate (show OS.Borrowing.mutate aFirst (.store 7 ⟨2, 0⟩ 131076 2) =
    .ok (aFilled, none) from rfl))
  (.next (.mutate (show OS.Borrowing.mutate aFilled (.allocate 7 ⟨196608, 12⟩ readWrite) =
    .ok (bAllocated, some ⟨3, 0⟩) from rfl))
  (.next (.mutate (show OS.Borrowing.mutate bAllocated (.store 7 ⟨3, 0⟩ 196608 3) =
    .ok (bFirst, none) from rfl))
  (.next (.mutate (show OS.Borrowing.mutate bFirst (.store 7 ⟨3, 0⟩ 196612 5) =
    .ok (bSecond, none) from rfl))
  (.next (.mutate (show OS.Borrowing.mutate bSecond (.store 7 ⟨3, 0⟩ 196616 6) =
    .ok (bFilled, none) from rfl))
  (.next (.readBorrow (show OS.Borrowing.readBorrow bFilled 7 ⟨2, 0⟩ 11 ⟨131072, 8⟩ =
    .ok (aHeld, 2) from rfl))
  (.next (.readBorrow (show OS.Borrowing.readBorrow aHeld 7 ⟨3, 0⟩ 11 ⟨196608, 8⟩ =
    .ok (pairHeld, 3) from rfl)) .refl))))))))

theorem current_empty_contract (base : Word) (unusedLoan : Nat) :
    Contract pairHeld (emptyCall base unusedLoan) :=
  (empty_contract base unusedLoan).frame input_history
    ⟨rfl, rfl, fun nonempty => False.elim (nonempty rfl)⟩

def callA : Call := { emptyCall 131072 2 with values := [0xffffffff, 2] }
def callB : Call := { emptyCall 196608 3 with values := [3, 5] }

theorem current_a_contract : Contract pairHeld callA := by
  have prior := current_empty_contract 131072 2
  refine ⟨prior.wellFormed, ?_, prior.code, prior.stack, ?_,
    show (131072 : Word).toNat + 4 * 2 ≤ 2^64 by decide,
    prior.returnCanonical, prior.stackBound, prior.postStackCanonical⟩
  · exact ⟨prior.held.code, prior.held.stack, fun _ => ⟨_, rfl, rfl, rfl⟩,
      prior.held.code_stack, fun _ => by decide, fun _ => by decide⟩
  · intro index value present
    match index with
    | 0 | 1 => simp [callA, emptyCall] at present; subst value; rfl
    | index + 2 => simp [callA, emptyCall] at present

theorem current_b_contract : Contract pairHeld callB := by
  have prior := current_empty_contract 196608 3
  refine ⟨prior.wellFormed, ?_, prior.code, prior.stack, ?_,
    show (196608 : Word).toNat + 4 * 2 ≤ 2^64 by decide,
    prior.returnCanonical, prior.stackBound, prior.postStackCanonical⟩
  · exact ⟨prior.held.code, prior.held.stack, fun _ => ⟨_, rfl, rfl, rfl⟩,
      prior.held.code_stack, fun _ => by decide, fun _ => by decide⟩
  · intro index value present
    match index with
    | 0 | 1 => simp [callB, emptyCall] at present; subst value; rfl
    | index + 2 => simp [callB, emptyCall] at present

def initial (shared : OS.Borrowing.State) (a b : Call) : State where
  registers register := match register with
    | .rdi => a.base
    | .rsi => BitVec.ofNat 64 a.values.length
    | .rdx => b.base
    | .rcx => BitVec.ofNat 64 b.values.length
    | .rsp => a.stack
    | _ => 0xfedcba9876543210
  rip := a.code
  flags := 0x602
  memory := toMemory shared.resources.space

-- These are actual satisfiable two-input admissions, not implications whose
-- premises might be contradictory. A and B require separate live input IDs.
theorem two_current_admitted :
    EDSL.Pair32.PairAdmission pairHeld callA callB (initial pairHeld callA callB) :=
  ⟨⟨current_a_contract, rfl⟩, ⟨current_b_contract, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem two_current_pre :
    EDSL.Pair32.Pre EDSL.Pair32.bytes (initial pairHeld callA callB)
      [0xffffffff, 2] [3, 5] 8192 :=
  EDSL.Pair32.pre_of_admission two_current_admitted rfl rfl rfl rfl rfl rfl

-- Universal pointers and loan IDs include absent, code/stack-aliasing IDs,
-- unmapped pointers, and noncanonical pointers in either empty phase.
theorem both_empty_admitted (baseA baseB : Word) (loanA loanB : Nat) :
    EDSL.Pair32.PairAdmission emptyHeld (emptyCall baseA loanA) (emptyCall baseB loanB)
      (initial emptyHeld (emptyCall baseA loanA) (emptyCall baseB loanB)) :=
  ⟨⟨empty_contract baseA loanA, rfl⟩, ⟨empty_contract baseB loanB, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem first_empty_admitted (base : Word) (unusedLoan : Nat) :
    EDSL.Pair32.PairAdmission pairHeld (emptyCall base unusedLoan) callB
      (initial pairHeld (emptyCall base unusedLoan) callB) :=
  ⟨⟨current_empty_contract base unusedLoan, rfl⟩, ⟨current_b_contract, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem second_empty_admitted (base : Word) (unusedLoan : Nat) :
    EDSL.Pair32.PairAdmission pairHeld callA (emptyCall base unusedLoan)
      (initial pairHeld callA (emptyCall base unusedLoan)) :=
  ⟨⟨current_a_contract, rfl⟩, ⟨current_empty_contract base unusedLoan, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

-- Identical readonly arrays can share BOTH their address and input loan ID.
-- Adding input/input separation or distinct-ID premises breaks this witness.
theorem identical_alias_admitted :
    EDSL.Pair32.PairAdmission pairHeld callA callA (initial pairHeld callA callA) :=
  ⟨⟨current_a_contract, rfl⟩, ⟨current_a_contract, rfl⟩, .refl _⟩

-- A second current loan can also cover a proper overlapping subarray. The
-- original A loan remains live while B independently borrows A's last word.
def aliasHeld : OS.Borrowing.State :=
  OS.Borrowing.installLoan pairHeld ⟨⟨2, 0⟩, 7, 11, ⟨131076, 4⟩⟩

theorem alias_history : OS.Borrowing.History pairHeld aliasHeld :=
  .next (.readBorrow (show OS.Borrowing.readBorrow pairHeld 7 ⟨2, 0⟩ 11 ⟨131076, 4⟩ =
    .ok (aliasHeld, 4) from rfl)) .refl

def aliasCallB : Call :=
  { callA with loans := ⟨0, 1, 4⟩, base := 131076, values := [2] }

theorem partial_alias_contract : Contract aliasHeld aliasCallB := by
  have prior := (current_empty_contract 131076 4).frame alias_history
    ⟨rfl, rfl, fun nonempty => False.elim (nonempty rfl)⟩
  refine ⟨prior.wellFormed, ?_, prior.code, prior.stack, ?_,
    show (131076 : Word).toNat + 4 * 1 ≤ 2^64 by decide,
    prior.returnCanonical, prior.stackBound, prior.postStackCanonical⟩
  · exact ⟨prior.held.code, prior.held.stack, fun _ => ⟨_, rfl, rfl, rfl⟩,
      prior.held.code_stack, fun _ => by decide, fun _ => by decide⟩
  · intro index value present
    cases index with
    | zero => simp [aliasCallB] at present; subst value; rfl
    | succ index => simp [aliasCallB] at present

theorem partial_alias_admitted :
    EDSL.Pair32.PairAdmission aliasHeld callA aliasCallB (initial aliasHeld callA aliasCallB) :=
  ⟨⟨current_a_contract.frame alias_history ⟨rfl, rfl, fun _ => rfl⟩, rfl⟩,
    ⟨partial_alias_contract, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

-- B's final actual operand is admitted through B's current loan. A's loan
-- cannot authorize that same readable address.
example : OS.ArrayResources.ReadPermission pairHeld 10 ⟨.data, 196612, 4⟩ := by
  apply EDSL.Pair32.operandReads_permission two_current_admitted rfl rfl rfl
  exact EDSL.Pair32.data_read_memberB (index := 1) (by decide)

example : OS.Borrowing.loadWord pairHeld 11 2 196612 = .error .outsideLoan := by rfl
example : OS.Borrowing.loadWord pairHeld 12 3 196612 = .error (.authority .wrongBorrower) := by rfl

def wrongBLoan : Call := { callB with loans := ⟨0, 1, 2⟩ }

-- Readable B memory and the correct worker do not make A's loan a valid B
-- admission. The supplied input handle must name the actual B region.
example : ¬Contract pairHeld wrongBLoan := by
  intro admitted
  obtain ⟨loan, live, _, region⟩ := admitted.held.input (by decide)
  change some (⟨⟨2, 0⟩, 7, 11, ⟨131072, 8⟩⟩ : OS.Borrowing.Loan) = some loan at live
  have same := Option.some.inj live
  rw [← same] at region
  have base : (131072 : Word) = 196608 := congrArg Region.base region
  exact (by decide : (131072 : Word) ≠ 196608) base

-- RAM can satisfy this unaligned read, but it crosses the exact eight-byte
-- B loan. Checking only the start byte would incorrectly authorize it.
example : loadDWord (toMemory pairHeld.resources.space) 196613 = .ok 0x06000000 := by rfl
example : OS.Borrowing.loadWord pairHeld 11 3 196613 = .error .outsideLoan := by rfl

def missingB : State :=
  { initial pairHeld callA callB with memory := toMemory aFilled.resources.space }

example : ¬EDSL.Pair32.PairAdmission pairHeld callA callB missingB := by
  intro admitted
  have current := admitted.admittedB.current.2.2 0 3 rfl
  change (.error (.inaccessibleData 196608) : Except Error (BitVec 32)) = .ok 3 at current
  cases current

def staleB : Call := { callB with values := [0, 5] }

example : ¬EDSL.Pair32.PairAdmission pairHeld callA staleB (initial pairHeld callA staleB) := by
  intro admitted
  have current := admitted.admittedB.current.2.2 0 0 rfl
  change (.ok 3 : Except Error (BitVec 32)) = .ok 0 at current
  have unequal : (3 : BitVec 32) ≠ 0 := by decide
  exact unequal (Except.ok.inj current)

def missingLastB : OS.Borrowing.State :=
  { pairHeld with resources := { pairHeld.resources with space :=
    ⟨fun address => if address = 196615 then none else pairHeld.resources.space.cells address⟩ } }

-- Removing only the fourth byte of B's final word invalidates admission;
-- retaining its first byte and the entire A array is insufficient.
example : ¬Contract missingLastB callB := by
  intro admitted
  have current := admitted.array 1 5 rfl
  change (.error (.inaccessibleData 196615) : Except Error (BitVec 32)) = .ok 5 at current
  cases current

-- Independent expectations: the first sum wraps to 1, the second is 8.
-- Both current admissions and permission for every actual operand survive
-- the run for EVERY stream of choices for the undefined arithmetic flag.
theorem separate_all_choices (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices 30 (initial pairHeld callA callB) = .ok result ∧
      result.state.registers .rax = 9 ∧ result.state.rip = 8192 ∧
      result.state.registers .rsp = 65552 ∧
      result.state.memory = toMemory pairHeld.resources.space ∧
      result.instructions = 30 ∧
      result.reads = [⟨.data, 131072, 4⟩, ⟨.data, 131076, 4⟩,
        ⟨.data, 196608, 4⟩, ⟨.data, 196612, 4⟩, ⟨.stack, 65544, 8⟩] ∧
      EDSL.Pair32.PairAdmission pairHeld callA callB result.state ∧
      ∀ read ∈ result.reads, ReadPermission pairHeld 10 read := by
  obtain ⟨result, run, post, cost, reads, retained, allowed⟩ :=
    EDSL.Pair32.resource_sound rfl two_current_admitted rfl rfl rfl rfl rfl rfl choices
  exact ⟨result, run, post.value, post.returnAddress, post.stackPointer, post.memory,
    cost, reads, retained, allowed⟩

theorem shared_loan_alias_all_choices (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices 30 (initial pairHeld callA callA) = .ok result ∧
      result.state.registers .rax = 2 ∧ result.instructions = 30 ∧
      result.reads = [⟨.data, 131072, 4⟩, ⟨.data, 131076, 4⟩,
        ⟨.data, 131072, 4⟩, ⟨.data, 131076, 4⟩, ⟨.stack, 65544, 8⟩] ∧
      EDSL.Pair32.PairAdmission pairHeld callA callA result.state ∧
      ∀ read ∈ result.reads, ReadPermission pairHeld 10 read := by
  obtain ⟨result, run, post, cost, reads, retained, allowed⟩ :=
    EDSL.Pair32.resource_sound rfl identical_alias_admitted rfl rfl rfl rfl rfl rfl choices
  exact ⟨result, run, post.value, cost, reads, retained, allowed⟩

theorem partial_alias_all_choices (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices 24 (initial aliasHeld callA aliasCallB) = .ok result ∧
      result.state.registers .rax = 3 ∧ result.instructions = 24 ∧
      result.reads = [⟨.data, 131072, 4⟩, ⟨.data, 131076, 4⟩,
        ⟨.data, 131076, 4⟩, ⟨.stack, 65544, 8⟩] ∧
      EDSL.Pair32.PairAdmission aliasHeld callA aliasCallB result.state ∧
      ∀ read ∈ result.reads, ReadPermission aliasHeld 10 read := by
  obtain ⟨result, run, post, cost, reads, retained, allowed⟩ :=
    EDSL.Pair32.resource_sound rfl partial_alias_admitted rfl rfl rfl rfl rfl rfl choices
  exact ⟨result, run, post.value, cost, reads, retained, allowed⟩

theorem first_empty_all_choices (base : Word) (unusedLoan : Nat) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices 18
        (initial pairHeld (emptyCall base unusedLoan) callB) = .ok result ∧
      result.state.registers .rax = 8 ∧ result.instructions = 18 ∧
      result.reads = [⟨.data, 196608, 4⟩, ⟨.data, 196612, 4⟩, ⟨.stack, 65544, 8⟩] ∧
      EDSL.Pair32.PairAdmission pairHeld (emptyCall base unusedLoan) callB result.state ∧
      ∀ read ∈ result.reads, ReadPermission pairHeld 10 read := by
  obtain ⟨result, run, post, cost, reads, retained, allowed⟩ :=
    EDSL.Pair32.resource_sound rfl (first_empty_admitted base unusedLoan)
      rfl rfl rfl rfl rfl rfl choices
  exact ⟨result, run, post.value, cost, reads, retained, allowed⟩

theorem second_empty_all_choices (base : Word) (unusedLoan : Nat) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices 18
        (initial pairHeld callA (emptyCall base unusedLoan)) = .ok result ∧
      result.state.registers .rax = 1 ∧ result.instructions = 18 ∧
      result.reads = [⟨.data, 131072, 4⟩, ⟨.data, 131076, 4⟩, ⟨.stack, 65544, 8⟩] ∧
      EDSL.Pair32.PairAdmission pairHeld callA (emptyCall base unusedLoan) result.state ∧
      ∀ read ∈ result.reads, ReadPermission pairHeld 10 read := by
  obtain ⟨result, run, post, cost, reads, retained, allowed⟩ :=
    EDSL.Pair32.resource_sound rfl (second_empty_admitted base unusedLoan)
      rfl rfl rfl rfl rfl rfl choices
  have expected : (EDSL.Pair32.pairSum callA.values (emptyCall base unusedLoan).values).setWidth 64 =
      (1 : Word) := by
    change (EDSL.Pair32.pairSum [0xffffffff, 2] []).setWidth 64 = (1 : Word)
    decide
  exact ⟨result, run, post.value.trans expected, cost, reads, retained, allowed⟩

theorem both_empty_all_choices (baseA baseB : Word) (loanA loanB : Nat)
    (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices 6
        (initial emptyHeld (emptyCall baseA loanA) (emptyCall baseB loanB)) = .ok result ∧
      result.state.registers .rax = 0 ∧ result.instructions = 6 ∧
      result.reads = [⟨.stack, 65544, 8⟩] ∧
      EDSL.Pair32.PairAdmission emptyHeld (emptyCall baseA loanA) (emptyCall baseB loanB) result.state ∧
      ∀ read ∈ result.reads, ReadPermission emptyHeld 10 read := by
  obtain ⟨result, run, post, cost, reads, retained, allowed⟩ :=
    EDSL.Pair32.resource_sound rfl (both_empty_admitted baseA baseB loanA loanB)
      rfl rfl rfl rfl rfl rfl choices
  exact ⟨result, run, post.value, cost, reads, retained, allowed⟩

-- The final B operand is actually observed before return, with current RAM
-- value 5 and the specific B loan 3 still usable in its real machine state.
theorem separate_b_read_origin (choices : Sequential.Choices) :
    ∃ result index before priorReads observation node,
      Sequential.run choices 30 (initial pairHeld callA callB) = .ok result ∧ index < 30 ∧
      Sequential.Block choices (initial pairHeld callA callB) before index priorReads ∧
      Sequential.step (choices index) before = .ok observation ∧
      (⟨.data, 196612, 4⟩ : Sequential.Read) ∈ observation.reads ∧
      Sequential.CFG.At EDSL.Pair32.bytes EDSL.Pair32.graph 4096 node before ∧
      EDSL.Pair32.PairAdmission pairHeld callA callB before ∧
      ReadPermission pairHeld 10 ⟨.data, 196612, 4⟩ ∧
      OS.Borrowing.loadWord pairHeld 11 3 196612 = .ok 5 ∧
      loadDWord before.memory 196612 = .ok 5 := by
  obtain ⟨result, run, _, cost, reads, _, _⟩ :=
    EDSL.Pair32.resource_sound rfl two_current_admitted rfl rfl rfl rfl rfl rfl choices
  have member : (⟨.data, 196612, 4⟩ : Sequential.Read) ∈ result.reads := by rw [reads]; decide
  obtain ⟨index, before, priorReads, observation, node, bound, block, step, present,
    binding, current, permission, _⟩ :=
    EDSL.Pair32.resource_read_origin rfl two_current_admitted rfl rfl rfl rfl rfl rfl
      (Sequential.run_sound run) member
  refine ⟨result, index, before, priorReads, observation, node, run, ?_, block, step,
    present, binding, current, permission, ?_, current.admittedB.current.2.2 1 5 rfl⟩
  · have exactCost : result.instructions = 30 := cost
    simpa only [exactCost] using bound
  · exact element_loadWord current.admittedB.resources (index := 1) (value := 5) rfl

-- The overlapping operand has a real checked origin and current value 2.
-- Both independent input handles authorize all four bytes there, retaining
-- both admissions rather than replacing them with a read snapshot.
theorem partial_alias_read_origin (choices : Sequential.Choices) :
    ∃ result index before priorReads observation node,
      Sequential.run choices 24 (initial aliasHeld callA aliasCallB) = .ok result ∧ index < 24 ∧
      Sequential.Block choices (initial aliasHeld callA aliasCallB) before index priorReads ∧
      Sequential.step (choices index) before = .ok observation ∧
      (⟨.data, 131076, 4⟩ : Sequential.Read) ∈ observation.reads ∧
      Sequential.CFG.At EDSL.Pair32.bytes EDSL.Pair32.graph 4096 node before ∧
      EDSL.Pair32.PairAdmission aliasHeld callA aliasCallB before ∧
      ReadPermission aliasHeld 10 ⟨.data, 131076, 4⟩ ∧
      OS.Borrowing.loadWord aliasHeld 11 2 131076 = .ok 2 ∧
      OS.Borrowing.loadWord aliasHeld 11 4 131076 = .ok 2 ∧
      loadDWord before.memory 131076 = .ok 2 := by
  obtain ⟨result, run, _, cost, reads, _, _⟩ :=
    EDSL.Pair32.resource_sound rfl partial_alias_admitted rfl rfl rfl rfl rfl rfl choices
  have member : (⟨.data, 131076, 4⟩ : Sequential.Read) ∈ result.reads := by rw [reads]; decide
  obtain ⟨index, before, priorReads, observation, node, bound, block, step, present,
    binding, current, permission, _⟩ :=
    EDSL.Pair32.resource_read_origin rfl partial_alias_admitted rfl rfl rfl rfl rfl rfl
      (Sequential.run_sound run) member
  refine ⟨result, index, before, priorReads, observation, node, run, ?_, block, step,
    present, binding, current, permission, ?_, ?_, current.admittedB.current.2.2 0 2 rfl⟩
  · have exactCost : result.instructions = 24 := cost
    simpa only [exactCost] using bound
  · exact element_loadWord current.admittedA.resources (index := 1) (value := 2) rfl
  · exact element_loadWord current.admittedB.resources (index := 0) (value := 2) rfl

end EDSL.Tests.Pair32Resources

#audit_edsl
