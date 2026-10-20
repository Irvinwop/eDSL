/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Lean
import EDSL.X86.VCGen.Core
import EDSL.X86.VCGen.Cutpoints

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen
open Sequential

/-- Normalize the existing CFG discovery result into finite graph data for
proof reduction. This term elaborator is only a proposer: clients must still
prove CFG.Valid against the original bytes with the production checker. -/
elab "vcgen_graph " bytes:term : term => do
  let proposed ← Lean.Elab.Term.elabTerm (← `(CFG.discover $bytes:term)) none
  let normalized ← Lean.Meta.reduce proposed
  unless normalized.isAppOfArity ``Option.some 2 do
    throwError "vcgen_graph: CFG discovery failed; inspect CFG.analyze for the unsupported input"
  return normalized.appArg!

/-- Propose a successor index and prove its bound and actual generated RIP
in the kernel. This tactic supplies no instruction semantics or invariant. -/
macro "vcgen_next_at" index:num : tactic => `(tactic|
  (refine ⟨⟨$index:num, ?_⟩, ?_, ?_⟩
   · exact of_decide_eq_true rfl
   · rfl))

/-- Find a successor within the existing checked CFG profile's 32-node bound.
Every candidate still needs a kernel proof of both its bound and RIP equality;
unsupported goals fail rather than becoming an assumed transition. -/
macro "vcgen_next" : tactic => `(tactic|
  first
  | vcgen_next_at 0 | vcgen_next_at 1 | vcgen_next_at 2 | vcgen_next_at 3
  | vcgen_next_at 4 | vcgen_next_at 5 | vcgen_next_at 6 | vcgen_next_at 7
  | vcgen_next_at 8 | vcgen_next_at 9 | vcgen_next_at 10 | vcgen_next_at 11
  | vcgen_next_at 12 | vcgen_next_at 13 | vcgen_next_at 14 | vcgen_next_at 15
  | vcgen_next_at 16 | vcgen_next_at 17 | vcgen_next_at 18 | vcgen_next_at 19
  | vcgen_next_at 20 | vcgen_next_at 21 | vcgen_next_at 22 | vcgen_next_at 23
  | vcgen_next_at 24 | vcgen_next_at 25 | vcgen_next_at 26 | vcgen_next_at 27
  | vcgen_next_at 28 | vcgen_next_at 29 | vcgen_next_at 30 | vcgen_next_at 31
  | fail "vcgen_next: no kernel-checked successor among CFG indices 0..31; simplify the RIP or inspect the graph")

open Lean Meta Elab Tactic

/-- Unfold the head WP by checked definitional equality. Rewriting the whole
remaining proposition would add a growing equality transport at every step. -/
elab "vcgen_unfold_wp" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOfArity ``wp 7 do
    throwError "vcgen_unfold_wp: expected a bounded production WP"
  replaceMainGoal [← goal.change (← whnf target)]

/-- The ten-argument cutpoint WP has the same checked head-only reduction.
Its invariant, rank, dynamic budget and remaining graph stay as references. -/
elab "vcgen_unfold_block" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOfArity ``Cutpoints.wp 10 do
    throwError "vcgen_unfold_block: expected a bounded cutpoint-block WP"
  replaceMainGoal [← goal.change (← whnf target)]

private def sameLocalDecl (before after : LocalDecl) : Bool :=
  before.index == after.index && before.fvarId == after.fvarId &&
  before.userName == after.userName && before.type == after.type &&
  before.binderInfo == after.binderInfo && before.kind == after.kind &&
  before.isLet true == after.isLet true && before.isNondep == after.isNondep &&
  before.value? true == after.value? true

/-- Factor a context-preserving simplifier into a checked continuation lemma.
Unsolved obligations become explicit proof parameters and remain goals for the
caller. This adds no admission hypotheses, axioms or trusted evaluation path. -/
elab "vcgen_factor" " => " steps:tacticSeq : tactic => withMainContext do
  let goal ← getMainGoal
  let context ← getLCtx
  let variables := context.getFVarIds
  let remaining ← Tactic.run goal (evalTactic steps)
  for next in remaining do
    let nextContext := (← next.getDecl).lctx
    unless nextContext.getFVarIds == variables && variables.all (fun id =>
        sameLocalDecl (context.get! id) (nextContext.get! id)) do
      throwError "vcgen_factor: callback must preserve the local context"
  -- A no-op leaves this very goal pending. Factoring it would assign the
  -- goal to a continuation applied to itself, creating a cyclic metavariable.
  unless (← goal.isAssigned) do
    replaceMainGoal remaining
    return
  let value ← instantiateMVars (mkMVar goal)
  let abstracted ← abstractMVars value (levels := false)
  let factored ← mkAuxTheorem (← inferType abstracted.expr) abstracted.expr
    (zetaDelta := true) (kind? := `vcgenStep) (cache := false)
  goal.assign (mkAppN factored abstracted.mvars)
  replaceMainGoal remaining

/-- Select a concrete successor's cutpoint branch by checked definitional
equality. Reducing the flag alone leaves the graph, invariant, rank and budget
in either branch intact, including in the next auxiliary theorem's type. -/
elab "vcgen_cutpoint" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOfArity ``ite 5 do
    throwError "vcgen_cutpoint: expected a successor cutpoint test"
  let condition := target.getArg! 1
  unless condition.isAppOfArity ``Eq 3 &&
      (condition.getArg! 1).isAppOfArity ``CFG.Graph.cutpoint 2 &&
      (condition.getArg! 2).isConstOf ``Bool.true do
    throwError "vcgen_cutpoint: expected a successor cutpoint test"
  let flag ← reduce (condition.getArg! 1)
  let branch ← if flag.isConstOf ``Bool.true then pure (target.getArg! 3)
    else if flag.isConstOf ``Bool.false then pure (target.getArg! 4)
    else throwError "vcgen_cutpoint: successor cutpoint is not concrete"
  replaceMainGoal [← goal.change branch]

/-- Reduce one generated block step, factoring the context-preserving callback
through a checked continuation. Only the selected instruction and successor's
cutpoint test are normalized; no graph is expanded in the remaining WP. -/
macro "vcgen_block_step" graph:ident cut:ident simplify:tactic : tactic => `(tactic|
  (
    vcgen_unfold_block
    intro af
    conv in (CFG.Graph.node _ _).instruction =>
      simp [$graph:ident, $cut:ident, CFG.Graph.node]
    dsimp only [List.length, execute, Instruction.operandReads,
      Instruction.length, NopEncoding.length, Address.eval, executeInstruction, executeJnz, executeShortBranch,
      executeLoop, executeRet, State.writeRegister, pure_ok]
    (vcgen_factor =>
      $simplify:tactic
      all_goals try dsimp only [List.length])
    first | vcgen_next | skip
    try vcgen_cutpoint))

/-- Reduce finite cutpoint-block WPs using only the production executor.
`graph` and `cut` are client definition names; the context-preserving callback
supplies present-state facts, arithmetic and read permissions. Stop at a return,
cutpoint assertion or unresolved obligation. Cutpoint identity, invariants,
decreasing ranks and dynamic budgets remain explicit proof obligations. -/
macro "vcgen_block" graph:ident cut:ident simplify:tactic : tactic => `(tactic|
  repeat' (vcgen_block_step $graph:ident $cut:ident $simplify:tactic))

/-- Normalize only the selected instruction. Keeping the graph as a reference
avoids copying all of its nodes into every remaining WP and auxiliary type. -/
macro "vcgen_step" graph:ident entry:ident simplify:tactic : tactic => `(tactic|
  (
    vcgen_unfold_wp
    intro af
    conv in (CFG.Graph.node _ _).instruction =>
      simp [$graph:ident, $entry:ident, CFG.Graph.node]
    dsimp only [execute, Instruction.operandReads,
      Instruction.length, Address.eval, executeInstruction, executeJnz, executeShortBranch,
      executeRet, State.writeRegister, pure_ok]
    (vcgen_factor => $simplify:tactic)
    first | vcgen_next | skip))

/-- The bounded-WP counterpart of `vcgen_block`, for finite routines without
client cutpoint assertions. The callback must preserve the local context.
Every generated continuation is kernel checked, including when serialized for
grading. Actual packet admission remains subject to the fixed runtime limits. -/
macro "vcgen_run" graph:ident entry:ident simplify:tactic : tactic => `(tactic|
  (vcgen_step $graph:ident $entry:ident $simplify:tactic
   repeat' (vcgen_step $graph:ident $entry:ident $simplify:tactic)))

end EDSL.X86.VCGen
