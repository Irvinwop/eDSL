/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Scalar32.Signum
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

open EDSL

/-!
These negative controls compare plausible instruction-algebra mistakes with the
independent integer-order contract. They do not assert a fixture's assigned
value: replacing the arithmetic shift with a logical shift, shifting by 30, or
using XOR instead of OR must each fail on the stated input.
-/

/-- INT32_MIN is admitted without an absolute-value-style domain exclusion. -/
example : Scalar32.signumSigned.domain (BitVec.intMin 32) :=
  Scalar32.signum_domain _

/-- Logical sign-mask replacement loses the negative result. -/
example : ¬ WordMath.Signum (BitVec.intMin 32).toInt
    ((1 : BitVec 32) ||| ((BitVec.intMin 32) >>> 31)).toInt := by
  unfold WordMath.Signum
  decide

/-- A one-bit count error in the Boolean-difference expression returns -2. -/
example : ¬ WordMath.Signum (BitVec.intMin 32).toInt
    ((0 : BitVec 32) - ((BitVec.intMin 32) >>> 30)).toInt := by
  unfold WordMath.Signum
  decide

/-- XOR clears bit zero of the negative sign mask and returns -2. -/
example : ¬ WordMath.Signum (-1)
    ((1 : BitVec 32) ^^^ ((-1 : BitVec 32).sshiftRight 31)).toInt := by
  unfold WordMath.Signum
  decide

/-- Reversing the zero test returns one at zero. -/
example : ¬ WordMath.Signum 0
    ((1 : BitVec 32) ||| ((0 : BitVec 32).sshiftRight 31)).toInt := by
  unfold WordMath.Signum
  decide

/-- A low32 -1 return is zero-extended by 32-bit machine writes, so the pure
low32 contract must accept 0xffffffff instead of demanding full64 -1. -/
example : Scalar32.signumSigned.result (BitVec.intMin 32) (4294967295 : BitVec 64) :=
  by
    change WordMath.Signum _ _
    unfold WordMath.Signum
    decide

/-- The same contract intentionally ignores all upper-half return bits. -/
example : Scalar32.signumSigned.result (BitVec.intMin 32) (18446744073709551615 : BitVec 64) :=
  by
    change WordMath.Signum _ _
    unfold WordMath.Signum
    decide

#audit_edsl
