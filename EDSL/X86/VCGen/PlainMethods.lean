/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Progress
import EDSL.X86.VCGen.PlainMethods.Calls
import EDSL.X86.VCGen.PlainMethods.AtomicEvents
import EDSL.X86.VCGen.PlainMethods.Batch
import EDSL.X86.VCGen.PlainMethods.Correspondence
import EDSL.X86.VCGen.PlainMethods.History
import EDSL.X86.VCGen.PlainMethods.ABI
import EDSL.X86.VCGen.PlainMethods.Completion
import EDSL.X86.VCGen.PlainMethods.Prefix
import EDSL.X86.VCGen.PlainMethods.Positions
import EDSL.X86.VCGen.PlainMethods.Footprint

/-!
Reusable checked padding/MOV64/RET method proofs for managed shared cells.
See `docs/managed-plain-methods.md` for admission, access origins, queue/caller
frames, indexed call/response origins, complete finite cohorts, whole scanner
correspondence, constructed finite atomic histories and represented scalar ABI
return frames, completion of mixed cohorts from actual prefixes, and full-cell
memory frames. Exact artifact contracts and source-order justification are
separate obligations.
-/
