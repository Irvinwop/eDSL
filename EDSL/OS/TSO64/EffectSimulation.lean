/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects.Head
import EDSL.OS.TSO64.EffectSimulation.Ordinary
import EDSL.OS.TSO64.EffectSimulation.Lifting
import EDSL.OS.TSO64.EffectSimulation.Resources
import EDSL.OS.TSO64.EffectSimulation.Resumable.Simulation

/-!
Checked ordinary effects and current-state admission for the TSO64 scheduler,
with generated ordinary-block obligations and a sparse-cutpoint adapter to the
existing simulation fold. Current resource frames and passive-origin closure
regenerate each head after interference; return postconditions remain historical.
Clients supply independent entry/cutpoint contracts and their generated block
proofs. Successful-run transport establishes no fairness or termination.
-/
