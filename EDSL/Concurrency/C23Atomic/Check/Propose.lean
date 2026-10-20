/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Check.Soundness

set_option autoImplicit false

namespace EDSL.Concurrency.C23Atomic.Check
variable {Location Value : Type}

/-- A finite closure proposal for convenience. Its algorithm is not a trusted
admission rule: `certify` checks the entire resulting certificate independently. -/
def proposeMatrix [DecidableEq Location] [DecidableEq Value]
    (table : Table Location Value) : Matrix :=
  (List.range table.events.length).foldl (fun current middle =>
    List.ofFn fun first : table.Index =>
      List.ofFn fun last : table.Index =>
        edge current first.val last.val ||
          (edge current first.val middle && edge current middle last.val))
    (List.ofFn fun first : table.Index =>
      List.ofFn fun last : table.Index => decide (seq table first last ∨ sync table first last))

/-- Propose a finite relation and admit it only through the proved checker. -/
def certify [DecidableEq Location] [DecidableEq Value]
    (table : Table Location Value) : Bool := check table (proposeMatrix table)

/-- No correctness or completeness assumption about the proposal is needed. -/
theorem certify_sound [DecidableEq Location] [DecidableEq Value]
    (table : Table Location Value) (checked : certify table = true) : Legal table.toCandidate :=
  check_sound table (proposeMatrix table) checked

end EDSL.Concurrency.C23Atomic.Check
