/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Progress

/-!
Reusable checked padding/MOV64/RET method proofs for managed shared cells.
See `docs/managed-plain-methods.md` for admission, access origins, queue/caller
frames, exact own-issue counts and the separate call/order/artifact obligations.
-/
