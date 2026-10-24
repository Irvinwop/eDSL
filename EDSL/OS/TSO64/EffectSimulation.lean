/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects.Head
import EDSL.OS.TSO64.EffectSimulation.Ordinary
import EDSL.OS.TSO64.EffectSimulation.Lifting
import EDSL.OS.TSO64.EffectSimulation.CheckedLifting
import EDSL.OS.TSO64.EffectSimulation.Resources
import EDSL.OS.TSO64.EffectSimulation.Resumable.Simulation
import EDSL.OS.TSO64.EffectSimulation.Mixed.Simulation
import EDSL.OS.TSO64.EffectSimulation.Mixed.Local
import EDSL.OS.TSO64.EffectSimulation.Mixed.Authority
import EDSL.OS.TSO64.EffectSimulation.Mixed.Counts
import EDSL.OS.TSO64.EffectSimulation.Mixed.CallerOnly
import EDSL.OS.TSO64.EffectSimulation.Mixed.CallerContinuation
import EDSL.OS.TSO64.EffectSimulation.Mixed.Completion
import EDSL.OS.TSO64.EffectSimulation.Mixed.IssuePreservation
import EDSL.OS.TSO64.EffectSimulation.Mixed.EventCounts
import EDSL.OS.TSO64.EffectSimulation.Mixed.Cohort
import EDSL.OS.TSO64.EffectSimulation.Mixed.LocalInvariant
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedLocal
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedPotential
import EDSL.OS.TSO64.EffectSimulation.Mixed.ChoiceTrace
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedCohort
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedPrefix
import EDSL.OS.TSO64.EffectSimulation.Mixed.CohortFrame

/-!
Checked ordinary effects and current-state admission for the TSO64 scheduler,
with generated ordinary-block obligations and a sparse-cutpoint adapter to the
existing simulation fold. Current resource frames and passive-origin closure
regenerate each head after interference; return postconditions remain historical.
Clients supply independent entry/cutpoint contracts and their generated block
proofs. Successful-run transport alone establishes no progress theorem.

Mixed blocks additionally retain current locked effects, exact blocked positions
and historical returns through the checked-step fold. Authority transport
preserves metadata, permissions and selector order while shared RAM may change.
Shared RMW accounting retains full logs. Caller-only ordinary nodes reuse current
protected reads under the mixed graph caps. Explicit idle-stable postconditions
extend to the complete final history when the actual worker has returned.

Every-node invariants and local rank laws support finite caller-only cohorts.
From present invariants, exhaustive slot coverage and empty queues, the ranked
engine constructs one actual returned suffix for arbitrary per-thread AF
choices, with an issue upper bound and full histories. This is an existence
result, not a fairness or hardware-cost guarantee. A separate schedule frame
preserves published bytes outside an independently registered common RMW cell.
-/
