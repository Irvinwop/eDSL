/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.ModuloCounter

namespace EDSL.Tests.ModuloCounter

open EDSL.Concurrency
open EDSL.Concurrency.ModuloCounter

-- Expected new words are independent numeric answers, not produced by eval.
-- These check carry across bit 31, high input bits, and full-width wraparound.
example : Step (0x00000000ffffffff : BitVec 64) 1 0x00000000ffffffff 0x0000000100000000 := by
  unfold Step
  decide

example : Step (0x1234567800000005 : BitVec 64) 0x8000000200000003
    0x1234567800000005 0x9234567a00000008 := by
  unfold Step
  decide

example : Step (0xffffffffffffffff : BitVec 64) 1 0xffffffffffffffff 0 := by
  unfold Step
  decide

def carry64 : List (Event 64 Nat Nat) :=
  [.invoke 10 0 1, .point ⟨10, 0, 1, 0x00000000ffffffff⟩,
    .respond 10 0 0x00000000ffffffff]

example : checkComplete (0x00000000ffffffff : BitVec 64) carry64 =
    some 0x0000000100000000 := by rfl

def highDelta64 : List (Event 64 Nat Nat) :=
  [.invoke 10 0 0x8000000200000003,
    .point ⟨10, 0, 0x8000000200000003, 0x1234567800000005⟩,
    .respond 10 0 0x1234567800000005]

example : checkComplete (0x1234567800000005 : BitVec 64) highDelta64 =
    some 0x9234567a00000008 := by rfl

def wrap64 : List (Event 64 Nat Nat) :=
  [.invoke 10 0 1, .point ⟨10, 0, 1, 0xffffffffffffffff⟩,
    .respond 10 0 0xffffffffffffffff]

example : checkComplete (0xffffffffffffffff : BitVec 64) wrap64 = some 0 := by rfl

-- Both actors invoke before either point. Actor 1 takes the first point;
-- actor 0 responds first and later makes another call after both responses.
-- Each returned word must be the current prior value, not the initial value.
def overlap64 : List (Event 64 Nat Nat) :=
  [.invoke 10 0 1,
    .invoke 20 1 0x8000000200000003,
    .point ⟨20, 1, 0x8000000200000003, 0x00000000ffffffff⟩,
    .point ⟨10, 0, 1, 0x8000000300000002⟩,
    .respond 10 0 0x8000000300000002,
    .respond 20 1 0x00000000ffffffff,
    .invoke 30 0 0x7ffffffcfffffffe,
    .point ⟨30, 0, 0x7ffffffcfffffffe, 0x8000000300000003⟩,
    .respond 30 0 0x8000000300000003]

theorem overlap64_checked : checkComplete (0x00000000ffffffff : BitVec 64) overlap64 = some 1 := by
  rfl

theorem overlap64_linearization :
    Linearizability.Linearization overlap64
      (fun calls => Sequential (0x00000000ffffffff : BitVec 64) calls 1) :=
  checked_linearization overlap64_checked

-- The computed serial order follows points, not invocation or response order.
example : (Linearizability.calls overlap64).map Linearizability.Call.id = [20, 10, 30] := by
  rfl

example : 1 = ((0x00000000ffffffff : BitVec 64).toNat +
    inputSum (Linearizability.calls overlap64)) % 2^64 :=
  checked_total overlap64_checked

-- The third call is after both earlier responses, so real time forces it last.
example : (Linearizability.intervals overlap64).Pairwise
    (fun earlier later => ¬ later.response < earlier.invocation) :=
  overlap64_linearization.extendsRealTime

example (id : Nat) : ¬ Linearizability.Pending overlap64 id :=
  (checkComplete_sound overlap64_checked).1.no_pending id

def serial64 : List (Event 64 Nat Nat) :=
  [.invoke 10 0 1, .point ⟨10, 0, 1, 0x0000000100000000⟩,
    .respond 10 0 0x0000000100000000,
    .invoke 20 1 0xffffffff, .point ⟨20, 1, 0xffffffff, 0x0000000100000001⟩,
    .respond 20 1 0x0000000100000001]

theorem serial64_checked : checkComplete (0x0000000100000000 : BitVec 64) serial64 =
    some 0x0000000200000000 := by rfl

-- Exercise the existing interval theorem through the new logical checker.
example (left right : Linearizability.Interval Nat Nat (BitVec 64) (BitVec 64))
    (leftMem : left ∈ Linearizability.intervals serial64)
    (rightMem : right ∈ Linearizability.intervals serial64)
    (nonoverlap : left.response < right.invocation) : left.point < right.point :=
  (checked_linearization serial64_checked).realTime left leftMem right rightMem nonoverlap

-- Width three: 6 + 5 wraps to 3, then 3 + 6 wraps to 1.
def small3 : List (Event 3 Nat Nat) :=
  [.invoke 1 0 5, .point ⟨1, 0, 5, 6⟩, .respond 1 0 6,
    .invoke 2 1 6, .point ⟨2, 1, 6, 3⟩, .respond 2 1 3]

example : checkComplete (6 : BitVec 3) small3 = some 1 := by rfl
example : Step (6 : BitVec 3) 5 6 3 ∧ Step (3 : BitVec 3) 6 3 1 := by
  unfold Step
  decide

-- No positive-width premise is hidden in the reusable definitions.
example : checkComplete (0 : BitVec 0)
    ([.invoke 1 0 0, .point ⟨1, 0, 0, 0⟩, .respond 1 0 0] : List (Event 0 Nat Nat)) =
    some 0 := by rfl

-- Matching point and response with wrong high bits satisfy the label protocol
-- but violate the full prior-state result. A low-32-bit equality would miss it.
def truncatedReturn64 : List (Event 64 Nat Nat) :=
  [.invoke 10 0 1, .point ⟨10, 0, 1, 0xffffffff⟩, .respond 10 0 0xffffffff]

example : Linearizability.check truncatedReturn64 = true ∧
    checkComplete (0x12345678ffffffff : BitVec 64) truncatedReturn64 = none := by
  exact ⟨rfl, rfl⟩

-- A correct second result is the current state. Returning the original word
-- again must fail even when the first update changed only the high half.
example : checkComplete (0x0000000100000000 : BitVec 64)
    ([.invoke 1 0 0x100000000, .point ⟨1, 0, 0x100000000, 0x100000000⟩,
      .respond 1 0 0x100000000,
      .invoke 2 1 1, .point ⟨2, 1, 1, 0x100000000⟩,
      .respond 2 1 0x100000000] : List (Event 64 Nat Nat)) = none := by rfl

-- The response boundary must preserve high bits too.
example : checkComplete (0x12345678ffffffff : BitVec 64)
    ([.invoke 10 0 1, .point ⟨10, 0, 1, 0x12345678ffffffff⟩,
      .respond 10 0 0xffffffff] : List (Event 64 Nat Nat)) = none := by rfl

-- The point has the same low input bits as the invocation. Arithmetic alone
-- accepts the point's 3; complete admission must notice the different high bits.
def wrongInput64 : List (Event 64 Nat Nat) :=
  [.invoke 10 0 0x8000000200000003,
    .point ⟨10, 0, 3, 0x1234567800000005⟩, .respond 10 0 0x1234567800000005]

example : eval (0x1234567800000005 : BitVec 64) (Linearizability.calls wrongInput64) =
    some 0x1234567800000008 ∧
    checkComplete (0x1234567800000005 : BitVec 64) wrongInput64 = none := by
  exact ⟨rfl, rfl⟩

-- Actor and identity mismatches at either point or response are rejected.
example : checkComplete (7 : BitVec 64)
    ([.invoke 10 0 1, .point ⟨10, 1, 1, 7⟩, .respond 10 0 7] :
      List (Event 64 Nat Nat)) = none := by rfl

example : checkComplete (7 : BitVec 64)
    ([.invoke 10 0 1, .point ⟨10, 0, 1, 7⟩, .respond 10 1 7] :
      List (Event 64 Nat Nat)) = none := by rfl

example : checkComplete (7 : BitVec 64)
    ([.invoke 10 0 1, .point ⟨11, 0, 1, 7⟩, .respond 10 0 7] :
      List (Event 64 Nat Nat)) = none := by rfl

example : checkComplete (7 : BitVec 64)
    ([.invoke 10 0 1, .point ⟨10, 0, 1, 7⟩, .respond 11 0 7] :
      List (Event 64 Nat Nat)) = none := by rfl

-- No point, no response, no invocation, or a repeated boundary is incomplete
-- or ambiguous. All cases below have harmless arithmetic where points exist.
example : checkComplete (7 : BitVec 64)
    ([.invoke 10 0 1, .respond 10 0 7] : List (Event 64 Nat Nat)) = none := by rfl

example : checkComplete (7 : BitVec 64)
    ([.invoke 10 0 1, .point ⟨10, 0, 1, 7⟩] : List (Event 64 Nat Nat)) = none := by rfl

example : checkComplete (7 : BitVec 64)
    ([.point ⟨10, 0, 1, 7⟩, .respond 10 0 7] : List (Event 64 Nat Nat)) = none := by rfl

example : checkComplete (7 : BitVec 64)
    ([.invoke 10 0 1, .invoke 10 0 1, .point ⟨10, 0, 1, 7⟩, .respond 10 0 7] :
      List (Event 64 Nat Nat)) = none := by rfl

example : checkComplete (7 : BitVec 64)
    ([.invoke 10 0 1, .point ⟨10, 0, 1, 7⟩, .respond 10 0 7, .respond 10 0 7] :
      List (Event 64 Nat Nat)) = none := by rfl

-- Two zero-update points leave the word unchanged and pass eval, so the
-- protocol's exactly-once check is essential rather than redundant arithmetic.
def duplicateZero64 : List (Event 64 Nat Nat) :=
  [.invoke 10 0 0, .point ⟨10, 0, 0, 0xabcdef0100000007⟩,
    .point ⟨10, 0, 0, 0xabcdef0100000007⟩, .respond 10 0 0xabcdef0100000007]

example : eval (0xabcdef0100000007 : BitVec 64) (Linearizability.calls duplicateZero64) =
    some 0xabcdef0100000007 ∧
    checkComplete (0xabcdef0100000007 : BitVec 64) duplicateZero64 = none := by
  exact ⟨rfl, rfl⟩

-- Reusing a completed identity also fails, even with two zero updates.
example : checkComplete (7 : BitVec 64)
    ([.invoke 10 0 0, .point ⟨10, 0, 0, 7⟩, .respond 10 0 7,
      .invoke 10 0 0, .point ⟨10, 0, 0, 7⟩, .respond 10 0 7] :
      List (Event 64 Nat Nat)) = none := by rfl

-- A single actor cannot have two outstanding calls, even with distinct ids.
example : checkComplete (7 : BitVec 64)
    ([.invoke 10 0 0, .invoke 20 0 0,
      .point ⟨10, 0, 0, 7⟩, .point ⟨20, 0, 0, 7⟩,
      .respond 10 0 7, .respond 20 0 7] : List (Event 64 Nat Nat)) = none := by rfl

-- Mathematical point order here is legal, but call 10 returns before call 20
-- is invoked. Serializing 20 first would reverse real time and must reject.
def reversedRealTime64 : List (Event 64 Nat Nat) :=
  [.invoke 10 0 1,
    .point ⟨20, 1, 1, 1⟩,
    .point ⟨10, 0, 1, 2⟩,
    .respond 10 0 2,
    .invoke 20 1 1,
    .respond 20 1 1]

example : eval (1 : BitVec 64) (Linearizability.calls reversedRealTime64) = some 3 ∧
    checkComplete (1 : BitVec 64) reversedRealTime64 = none := by exact ⟨rfl, rfl⟩

example : checkComplete (7 : BitVec 64)
    ([.invoke 10 0 1, .respond 10 0 7, .point ⟨10, 0, 1, 7⟩] :
      List (Event 64 Nat Nat)) = none := by rfl

-- Arbitrary initial state, not just a selected fixture word.
example (initial : BitVec 64) :
    Sequential initial ([⟨1, 0, 0, initial⟩] : List (Call 64 Nat Nat)) initial := by
  apply Sequential.cons ?_ (.nil _)
  exact step_iff.mpr ⟨rfl, by simp⟩

end EDSL.Tests.ModuloCounter

#print axioms EDSL.Concurrency.ModuloCounter.step_iff
#print axioms EDSL.Concurrency.ModuloCounter.Sequential.final_fold
#print axioms EDSL.Concurrency.ModuloCounter.Sequential.total
#print axioms EDSL.Concurrency.ModuloCounter.eval_sound
#print axioms EDSL.Concurrency.ModuloCounter.eval_complete
#print axioms EDSL.Concurrency.ModuloCounter.eval_eq_some_iff
#print axioms EDSL.Concurrency.ModuloCounter.Sequential.deterministic
#print axioms EDSL.Concurrency.ModuloCounter.checkComplete_sound
#print axioms EDSL.Concurrency.ModuloCounter.checkComplete_complete
#print axioms EDSL.Concurrency.ModuloCounter.checkComplete_eq_some_iff
#print axioms EDSL.Concurrency.ModuloCounter.LegalHistory.linearization
#print axioms EDSL.Concurrency.ModuloCounter.checked_linearization
#print axioms EDSL.Concurrency.ModuloCounter.checked_total
#audit_edsl
