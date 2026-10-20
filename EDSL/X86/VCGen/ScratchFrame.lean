/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Frame
import EDSL.X86.VCGen.Tactics

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen
open Lean Meta Elab Tactic

/-- Solve a proposed proof without assigning the caller's goal. Every obligation
must close; the final expression is still checked by Lean's kernel. -/
private def scratchProof (type : Expr) (steps : Syntax) : TacticM Expr := do
  let proof ← mkFreshExprMVar type
  let remaining ← Tactic.run proof.mvarId! (evalTactic steps)
  unless remaining.isEmpty do
    throwError "vcgen_scratch_frame: unresolved obligation{indentExpr type}"
  let proof ← instantiateMVars proof
  if proof.hasExprMVar then
    throwError "vcgen_scratch_frame: proof contains unresolved metavariables"
  return proof

/-- Recognize only ordinary register-function updates. Values are opaque; no
instruction, arithmetic or permission semantics are reproduced here. The list
is oldest write first, so each write can use the same compositional theorem. -/
private partial def scratchWrites (register base value : Expr) :
    MetaM (Array (Expr × Expr)) := do
  if ← isDefEq value base then return #[]
  -- Ordinary whnf also unfolds ite into Bool.rec. Keep the update boundary
  -- visible while reducing projections, lambdas, lets and writeRegister.
  let value ← withCanUnfoldPred (fun _ info => pure (info.name != ``ite && info.name != ``dite))
    (whnf value)
  unless value.isAppOfArity ``ite 5 do
    throwError "vcgen_scratch_frame: unsupported register function{indentExpr value}"
  let condition := value.getArg! 1
  unless condition.isAppOfArity ``Eq 3 do
    throwError "vcgen_scratch_frame: expected a register equality{indentExpr condition}"
  let left := condition.getArg! 1
  let right := condition.getArg! 2
  let destination ← if left == register then pure right
    else if right == register then pure left
    else throwError "vcgen_scratch_frame: expected an update at the queried register"
  let written := value.getArg! 3
  if destination.containsFVar register.fvarId! || written.containsFVar register.fvarId! then
    throwError "vcgen_scratch_frame: destination/value depends on the queried register"
  let previous ← scratchWrites register base (value.getArg! 4)
  return previous.push (destination, written)

/-- Frame concrete production-generated register writes and record updates
from an existing frame. Scratch and initial state must agree definitionally:
use `frame.weaken subset` explicitly for a wider frame (including RET's RSP).

Membership is proved by assumptions or kernel reduction. Register functions
are reconstructed as writes, without enumerating GPRs. RAM/permission equality
uses only reduction and the supplied frame; flags also use the listed full-mask lemmas.
`with tactic` replaces the flag proof for additional proved flag operations.

The tactic either closes the entire frame or reports its failed obligation.
It supplies no ABI disjointness, result, read, invariant, rank or execution fact.
It can be used inside `vcgen_factor` to keep continuation proofs shallow. -/
syntax (name := vcgenScratchFrame) "vcgen_scratch_frame " term (" with " tactic)? : tactic

elab_rules : tactic
  | `(tactic| vcgen_scratch_frame $frame:term $[with $flags:tactic]?) => withMainContext do
    let goal ← getMainGoal
    let target ← whnf (← getMainTarget)
    unless target.isAppOfArity ``PureCall.ScratchFrame 3 do
      throwError "vcgen_scratch_frame: expected a ScratchFrame goal"
    let proof ← Term.elabTerm frame none
    let source ← whnf (← inferType proof)
    unless source.isAppOfArity ``PureCall.ScratchFrame 3 do
      throwError "vcgen_scratch_frame: supplied term is not a ScratchFrame"
    unless (← isDefEq (source.getArg! 0) (target.getArg! 0)) &&
        (← isDefEq (source.getArg! 1) (target.getArg! 1)) do
      throwError "vcgen_scratch_frame: scratch/initial mismatch; use an explicit ScratchFrame.weaken subset proof to widen scratch"
    let current := source.getArg! 2
    let final := target.getArg! 2
    let currentRegisters ← mkAppM ``State.registers #[current]
    let finalRegisters ← mkAppM ``State.registers #[final]
    let writes ← withLocalDeclD `register (mkConst ``Register) fun register =>
      scratchWrites register (mkApp currentRegisters register) (mkApp finalRegisters register)
    let mut composed := proof
    for (destination, value) in writes do
      let membership ← mkAppM ``Membership.mem #[target.getArg! 0, destination]
      let member ← scratchProof membership (← `(tactic| first | assumption | decide +kernel))
      composed ← mkAppM ``PureCall.ScratchFrame.writeRegister
        #[composed, destination, value, member]
    let transport ← mkAppM ``PureCall.ScratchFrame.of_fields #[composed, final]
    let result ← mkFreshExprMVar target
    let obligations ← result.mvarId!.apply transport
    unless obligations.length == 3 do
      throwError "vcgen_scratch_frame: unexpected frame transport obligations"
    let registers := obligations[0]!
    registers.assign (← scratchProof (← registers.getType) (← `(tactic| rfl)))
    let memory := obligations[1]!
    memory.assign (← scratchProof (← memory.getType)
      (← `(tactic| solve | simp only [State.writeRegister, Sequential.Result.prepend,
        ($frame:term).memory])))
    let flagSteps ← match flags with
      | some steps => pure steps.raw
      | none => `(tactic| solve | simp only [State.writeRegister, Sequential.Result.prepend,
          ($frame:term).flags,
          Sequential.statusFlags_preserves, Sequential.logicalFlags32_preserves,
          Sequential.logicalFlags64_preserves, Sequential.shrOneFlags64_preserves,
          Sequential.cmpFlags32_preserves, Sequential.cmpFlags64_preserves,
          Sequential.incFlags32_preserves, Sequential.incFlags64_preserves,
          Sequential.decFlags64_preserves, Sequential.addFlags64_preserves,
          cmpZeroFlags32_preserves, addFlags32_preserves, Sequential.cmpFlags8_preserves])
    let flagGoal := obligations[2]!
    let checked ← scratchProof (← flagGoal.getType) flagSteps
    flagGoal.assign checked
    let result ← instantiateMVars result
    if result.hasExprMVar then
      throwError "vcgen_scratch_frame: frame contains unresolved metavariables"
    goal.assign result
    replaceMainGoal []

end EDSL.X86.VCGen
