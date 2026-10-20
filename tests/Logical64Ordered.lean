/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.OrderedHistory
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.Logical64Ordered
open X86 Logical64 OS.Atomics64

local instance (operation : Operation) (left right result : Word) :
    Decidable (MathematicalResult operation left right result) := by
  cases operation <;> unfold MathematicalResult HasBit <;> infer_instance

/-- Independently specified literal full64 words distinguish schedules that
differ only in the relative positions of AND and OR. No machine evaluator is
used as the expected-result oracle. -/
theorem high_bit_order :
    OrderedMathematicalResult 0x8000000000000001
      [(.intersection, 0x7fffffffffffffff), (.union, 0x8000000000000000),
        (.symmetricDifference, 1)] 0x8000000000000000 ∧
    OrderedMathematicalResult 0x8000000000000001
      [(.union, 0x8000000000000000), (.intersection, 0x7fffffffffffffff),
        (.symmetricDifference, 1)] 0 := by
  constructor
  · exact .cons (intermediate := 1) (by decide)
      (.cons (intermediate := 0x8000000000000001) (by decide)
        (.cons (by decide) .nil))
  · exact .cons (intermediate := 0x8000000000000001) (by decide)
      (.cons (intermediate := 1) (by decide) (.cons (by decide) .nil))

theorem high_bit_orders_differ :
    ¬OrderedMathematicalResult 0x8000000000000001
      [(.union, 0x8000000000000000), (.intersection, 0x7fffffffffffffff),
        (.symmetricDifference, 1)] 0x8000000000000000 := by
  intro same
  have impossible := same.unique high_bit_order.2
  exact (by decide : (0x8000000000000000 : Word) ≠ 0) impossible

/-- This owned synthetic mathematical history retains all four occurrences.
It demonstrates the compound-call boundary; it is not a managed scheduler or
physical execution witness. A's standalone OR/XOR/XOR solves union, whereas
the peer OR inserted between its XORs leaves zero. -/
theorem peer_between_xors :
    OrderedMathematicalResult 0
      [(.union, 1), (.symmetricDifference, 1), (.union, 1), (.symmetricDifference, 1)] 0 := by
  exact .cons (intermediate := 1) (by decide)
    (.cons (intermediate := 0) (by decide)
      (.cons (intermediate := 1) (by decide) (.cons (by decide) .nil)))

theorem standalone_body_is_union :
    OrderedMathematicalResult 0
      [(.union, 1), (.symmetricDifference, 1), (.symmetricDifference, 1)] 1 := by
  exact .cons (intermediate := 1) (by decide)
    (.cons (intermediate := 0) (by decide) (.cons (by decide) .nil))

/-- Neither serial order of two identical abstract union requests produces
the interleaved result. There is only one literal list because both requests
have the same operation and mask. -/
theorem no_two_union_serialization :
    ¬OrderedMathematicalResult 0 [(.union, 1), (.union, 1)] 0 := by
  intro claimed
  have serial : OrderedMathematicalResult 0 [(.union, 1), (.union, 1)] 1 :=
    .cons (intermediate := 1) (by decide) (.cons (by decide) .nil)
  have impossible := claimed.unique serial
  exact (by decide : (0 : Word) ≠ 1) impossible

/-- No-change requests are still part of the mathematical history. A zero
XOR and an all-ones AND preserve the high bit and both occurrence positions. -/
theorem no_change_occurrences :
    OrderedMathematicalResult 0x8000000000000001
      [(.symmetricDifference, 0), (.intersection, 0xffffffffffffffff), (.union, 0)]
      0x8000000000000001 := by
  exact .cons (intermediate := 0x8000000000000001) (by decide)
    (.cons (intermediate := 0x8000000000000001) (by decide) (.cons (by decide) .nil))

end EDSL.Tests.Logical64Ordered

#print axioms EDSL.Logical64.OrderedMathematicalResult.unique
#print axioms EDSL.Logical64.OrderedMathematicalResult.append_iff
#print axioms EDSL.Logical64.OrderedMathematicalResult.union_xor_xor
#print axioms EDSL.OS.Atomics64.LogicalChain.orderedMathematicalResult
#print axioms EDSL.OS.Atomics64.LogicalTrace.orderedMathematicalResult
#print axioms EDSL.Tests.Logical64Ordered.high_bit_orders_differ
#print axioms EDSL.Tests.Logical64Ordered.no_two_union_serialization
#audit_edsl
