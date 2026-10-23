/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects.Head
import EDSL.OS.TSO64.EffectSimulation.Ordinary
import EDSL.OS.TSO64.EffectSimulation.Lifting

/-!
Checked ordinary effects and current-state admission for the TSO64 scheduler,
with a generic simulation fold over actual successful schedules. Clients supply
the simulation law for every production origin; successful-run transport alone
does not establish fault freedom, fairness or termination.
-/
