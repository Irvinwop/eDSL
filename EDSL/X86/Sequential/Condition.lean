/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Machine

set_option warningAsError true

namespace EDSL.X86.Sequential

/-- The sixteen canonical x86 status conditions, in encoding-nibble order.
Aliases such as carry/zero use below/equal respectively. AF is never tested. -/
inductive Condition where
  | overflow | notOverflow | below | aboveEqual | equal | notEqual | belowEqual | above
  | sign | notSign | parity | notParity | less | greaterEqual | lessEqual | greater
  deriving DecidableEq, BEq, Repr

/-- Conditions inspect the actual current status bits. Signed conditions
compare SF with OF, rather than interpreting SF alone as signed order. -/
def Condition.holds : Condition → Word → Bool
  | .overflow, flags => flags.getLsbD 11
  | .notOverflow, flags => !flags.getLsbD 11
  | .below, flags => flags.getLsbD 0
  | .aboveEqual, flags => !flags.getLsbD 0
  | .equal, flags => flags.getLsbD 6
  | .notEqual, flags => !flags.getLsbD 6
  | .belowEqual, flags => flags.getLsbD 0 || flags.getLsbD 6
  | .above, flags => !flags.getLsbD 0 && !flags.getLsbD 6
  | .sign, flags => flags.getLsbD 7
  | .notSign, flags => !flags.getLsbD 7
  | .parity, flags => flags.getLsbD 2
  | .notParity, flags => !flags.getLsbD 2
  | .less, flags => flags.getLsbD 7 ^^ flags.getLsbD 11
  | .greaterEqual, flags => flags.getLsbD 7 == flags.getLsbD 11
  | .lessEqual, flags => flags.getLsbD 6 || (flags.getLsbD 7 ^^ flags.getLsbD 11)
  | .greater, flags => !flags.getLsbD 6 && (flags.getLsbD 7 == flags.getLsbD 11)

def Condition.ofNibble (code : Fin 16) : Condition :=
  match code.val with
  | 0 => .overflow | 1 => .notOverflow | 2 => .below | 3 => .aboveEqual
  | 4 => .equal | 5 => .notEqual | 6 => .belowEqual | 7 => .above
  | 8 => .sign | 9 => .notSign | 10 => .parity | 11 => .notParity
  | 12 => .less | 13 => .greaterEqual | 14 => .lessEqual | _ => .greater

def Condition.nibble : Condition → Fin 16
  | .overflow => 0 | .notOverflow => 1 | .below => 2 | .aboveEqual => 3
  | .equal => 4 | .notEqual => 5 | .belowEqual => 6 | .above => 7
  | .sign => 8 | .notSign => 9 | .parity => 10 | .notParity => 11
  | .less => 12 | .greaterEqual => 13 | .lessEqual => 14 | .greater => 15

theorem Condition.ofNibble_nibble (condition : Condition) :
    ofNibble condition.nibble = condition := by cases condition <;> rfl

theorem Condition.nibble_ofNibble : ∀ code : Fin 16, (ofNibble code).nibble = code := by decide

theorem Condition.holds_greaterEqual (flags : Word) :
    holds .greaterEqual flags = !holds .less flags := by
  simp only [holds]
  cases flags.getLsbD 7 <;> cases flags.getLsbD 11 <;> rfl

end EDSL.X86.Sequential
