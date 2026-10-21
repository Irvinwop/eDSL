/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.PlainCallAdmission64
import EDSL.OS.PlainCallFrames64
import EDSL.OS.PlainCallSafety64
import EDSL.OS.PlainCallProgress64
import EDSL.OS.PlainCallBehavior64
import EDSL.OS.PlainCallHistory64

/-!
Reusable managed acquire-load/release-store call adapters. Import this module
to connect a catalog of complete checked byte windows to independent present
resources, prefix safety, progress and closed histories. Each actual worker
selects its own site and input; the shared proofs handle the whole finite cohort.

`PlainCallAdmission64.StaticShapes` is separate from independent `Plain64.Pre`.
`PlainCallSafety64.safe_prefix` and `PlainCallProgress64.enabled/bounded` need
only those facts and the actual successful prefix. `PlainCallBehavior64.post`
derives independent completed behavior. `PlainCallHistory64` derives
initialized capture and the actual history at explicit empty queue endpoints.
These pieces do not yet constitute the full independent Plain64 Claim or an
inhabited exact-final-ELF certificate. Model boundaries remain in the imported
contracts, including declared interface orders and long-mode/CET-off execution.
-/
