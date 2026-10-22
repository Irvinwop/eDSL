/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Tactics
import EDSL.X86.VCGen.Choices

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen
open Sequential
open Lean Meta Elab Tactic

/-- Unfold only the head of the bounded production vector WP by checked
definitional equality. Graph data and the remaining continuation stay as
references, as in `vcgen_unfold_wp`. -/
elab "vcgen_unfold_wpWith" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOfArity ``wpWith 7 do
    throwError "vcgen_unfold_wpWith: expected a bounded production vector WP"
  replaceMainGoal [← goal.change (← whnf target)]

/-- Reduce only the selected instruction using `executeWith`. Each step
introduces a complete `FlagChoices` valuation. IMUL uses its production state
transformer; existing instructions use their production `selectedChoice`.
The context-preserving callback is factored by the existing checked helper,
and successor bounds and RIP equality still require kernel proofs. -/
macro "vcgen_stepWith" graph:ident entry:ident simplify:tactic : tactic => `(tactic|
  (
    vcgen_unfold_wpWith
    intro choices
    conv in (CFG.Graph.node _ _).instruction =>
      simp [$graph:ident, $entry:ident, CFG.Graph.node]
    dsimp only [executeWith, imulReg64State, Instruction.selectedChoice,
      Instruction.choiceFlag, Instruction.choosesAF, FlagChoices.get,
      execute, Instruction.operandReads, Instruction.length, NopEncoding.length,
      Address.eval, executeInstruction, executeJnz, executeShortBranch,
      executeRet, State.writeRegister, pure_ok]
    (vcgen_factor => $simplify:tactic)
    first | vcgen_next | skip))

/-- Compose finite production vector WPs without a client interpreter or
supplied instruction-step equations. The caller supplies only the graph and
entry definition names and a context-preserving simplification callback.
Stop at return or any unresolved obligation; no choice vector is specialized.
Graph checking, contracts and the existing admission limits remain separate. -/
macro "vcgen_runWith" graph:ident entry:ident simplify:tactic : tactic => `(tactic|
  (vcgen_stepWith $graph:ident $entry:ident $simplify:tactic
   repeat' (vcgen_stepWith $graph:ident $entry:ident $simplify:tactic)))

end EDSL.X86.VCGen
