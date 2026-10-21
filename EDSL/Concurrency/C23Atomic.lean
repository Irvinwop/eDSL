/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Coherence
import EDSL.Concurrency.C23Atomic.Check
import EDSL.Concurrency.C23Atomic.Weakening

/-!
Finite atomic-only C23 event-graph constraints for relaxed/acquire/release
operations. These source-level constraints are separate from the checked
machine scheduler and its uniform-word TSO trace refinement. See
`docs/c23-atomic-events.md` for the precise subset and mapping obligations.
-/
