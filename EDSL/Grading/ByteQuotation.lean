/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.State
import Lean.ToExpr

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSLGrader
open Lean EDSL

/-- Balanced quotation is a controller optimization, not a trusted conversion
axiom. Its exact value is checked by the kernel in the expected statement. -/
private def balancedBytes : Nat → List X86.Byte → Expr
  | 0, bytes => toExpr bytes
  | fuel + 1, bytes =>
    if bytes.length ≤ 16 then toExpr bytes
    else
      let half := bytes.length / 2
      mkApp3 (mkConst ``List.append [Level.zero]) (toTypeExpr X86.Byte)
        (balancedBytes fuel (bytes.take half)) (balancedBytes fuel (bytes.drop half))

def byteExpr (bytes : List X86.Byte) : Expr := balancedBytes 16 bytes

end EDSLGrader
