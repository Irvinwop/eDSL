/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Progress
import EDSL.X86.VCGen.PlainMethods.Calls
import EDSL.X86.VCGen.PlainMethods.AtomicEvents
import EDSL.X86.VCGen.PlainMethods.Batch

/-!
Reusable checked padding/MOV64/RET method proofs for managed shared cells.
See `docs/managed-plain-methods.md` for admission, access origins, queue/caller
frames, indexed call/response origins, complete finite cohorts and the separate
graph/order/artifact obligations.
-/
