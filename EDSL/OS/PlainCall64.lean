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
import EDSL.OS.PlainCallCompletion64
import EDSL.OS.PlainCallClosed64
import EDSL.OS.PlainCallClaim64

/-!
Reusable managed acquire-load/release-store call adapters. Import this module
to connect a catalog of complete checked byte windows to the full independent
`Plain64.Claim`. Each actual worker selects its own site and input; the shared
proof handles present resources, all successful prefixes and completed runs,
chosen finite completion, actual drain closure and closed atomic histories.

`PlainCallAdmission64.StaticShapes` is separate from independent `Plain64.Pre`.
`PlainCallSafety64.safe_prefix` and `PlainCallProgress64.enabled/bounded` need
only those facts and the actual successful prefix. `PlainCallBehavior64.post`
derives independent completed behavior. `PlainCallCompletion64` proves chosen AF
indices and constructs completion and separate publication closure.
`PlainCallClosed64.post` derives the full `ClosedPost` at empty queue endpoints,
retaining exact machine events, initialized objects and the same calls' History.
`PlainCallClaim64.claim` composes all independent contract obligations once for
every static catalog. Useful exact-final-ELF populations and executions remain
separate certification gates. Model boundaries remain in the imported contracts,
including declared interface orders and long-mode/CET-off execution.
-/
