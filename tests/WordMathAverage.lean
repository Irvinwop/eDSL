/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.WordMath.Average

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.WordMathAverage

open EDSL.WordMath

-- The input sum exceeds 255 and is odd: catch wrapping before division or
-- rounding up instead of down, while retaining the high output bit.
example : unsignedAverage (225 : BitVec 8) 164 = 194 := by decide

-- Differing top bits require an unsigned shift; a signed shift gives 255.
example : unsignedAverage (255 : BitVec 8) 0 = 127 := by decide

-- Two odd inputs carry from the low bit: averaging separately truncated halves
-- gives 3, while discarding the differing bits gives 1.
example : unsignedAverage (3 : BitVec 8) 5 = 4 := by decide

-- A nonstandard width, with shared high bits and an overflowing input sum.
example : unsignedAverage (31 : BitVec 5) 18 = 24 := by decide

-- Width one keeps the shared bit, even though the full-width sum wraps to zero.
example : unsignedAverage (1 : BitVec 1) 1 = 1 := by decide

-- The 65th input bit participates: catch accidental restriction to a host word.
example : unsignedAverage (0x10000000000000000 : BitVec 65) 2 =
    0x8000000000000001 := by decide

end EDSL.Tests.WordMathAverage
