/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Runtime.Codec
import EDSL.Grading.Runtime.Audit

/-! Proof-packet admission/checking, using only the options-independent checked
kernel declaration API. Candidate code is never compiled or evaluated. Each call
starts from its caller's immutable trusted snapshot; no candidate state is global.
Heartbeat quotas are apportioned across all kernel additions in a packet. These
limits are admission policy, not a service sandbox or an allocation/latency proof.

Safe opaque bodies are audited logically. Source `partial def` may lower to a safe
opaque logical default body: metadata cannot reconstruct source provenance or a
compiled runtime implementation. Actual unsafe/partial metadata is rejected.
Simple nonnested inductive groups are supported; nested inductives and mutual
definition payloads are outside this protocol version. -/
namespace EDSLGrader.Runtime

open Lean

def kernelFailure : Kernel.Exception → Failure
  | .unknownConstant .. => ⟨.rejected, "kernel unknownConstant"⟩
  | .alreadyDeclared .. => ⟨.rejected, "kernel alreadyDeclared"⟩
  | .declTypeMismatch .. => ⟨.rejected, "kernel declTypeMismatch"⟩
  | .declHasMVars .. => ⟨.rejected, "kernel declHasMVars"⟩
  | .declHasFVars .. => ⟨.rejected, "kernel declHasFVars"⟩
  | .funExpected .. => ⟨.rejected, "kernel funExpected"⟩
  | .typeExpected .. => ⟨.rejected, "kernel typeExpected"⟩
  | .letTypeMismatch .. => ⟨.rejected, "kernel letTypeMismatch"⟩
  | .exprTypeMismatch .. => ⟨.rejected, "kernel exprTypeMismatch"⟩
  | .appTypeMismatch .. => ⟨.rejected, "kernel appTypeMismatch"⟩
  | .invalidProj .. => ⟨.rejected, "kernel invalidProj"⟩
  | .thmTypeIsNotProp .. => ⟨.rejected, "kernel thmTypeIsNotProp"⟩
  | .other _ => ⟨.rejected, "kernel declaration rejected"⟩
  | .deterministicTimeout => ⟨.resource, "kernel heartbeat limit"⟩
  | .excessiveMemory => ⟨.resource, "kernel memory limit"⟩
  | .deepRecursion => ⟨.resource, "kernel recursion limit"⟩
  | .interrupted => ⟨.resource, "kernel interrupted"⟩

/-- No Options or compiler/evaluator APIs occur at the trust boundary. Zero is
disallowed because kernel APIs can interpret zero budgets as unbounded. -/
def forceDeclaration (env : Kernel.Environment) (heartbeats recDepth : USize)
    (decl : Declaration) : Except Failure Kernel.Environment := do
  if heartbeats == 0 || recDepth == 0 then return ← fail .resource "zero kernel budget"
  (Kernel.Environment.addDeclCore env heartbeats recDepth decl none).mapError kernelFailure

def checkFinal (env : Kernel.Environment) (lim : Limits) (heartbeats : USize)
    (state : AuditState) (expected value : Expr) (freshName : Name) :
    Except Failure AuditState := do
  closed expected
  closed value
  if freshName.isAnonymous || (env.find? freshName).isSome then
    return ← fail .internal "certification name collision"
  let state ← auditExprs env state expected value
  let _ ← forceDeclaration env heartbeats lim.kernelRecDepth (.thmDecl {
    name := freshName, levelParams := [], type := expected, value })
  return state

/-- Root-only wrapper/test API. The supplied name is trusted, not a packet field.
The returned environment discards the scratch theorem used for checking. -/
def checkExpr (env : Kernel.Environment) (lim : Limits) (expected value : Expr)
    (freshName : Name) : Except Failure Checked := do
  let state ← checkFinal env lim lim.kernelHeartbeats
    { remaining := lim.maxAuditSteps } expected value freshName
  return {
    env, value
    declarations := 0
    constants := state.seen.size
    decoderSteps := 0
    auditSteps := lim.maxAuditSteps - state.remaining
    kernelChecks := 1 }

/-- For this protocol every inductive group is required to have no kernel-generated
nested types. The checked insertion is temporary until this check and the audit
both succeed; failed extensions are never returned or reused. -/
def checkInductiveShape (env : Kernel.Environment) (decl : Declaration) : Except Failure Unit := do
  if let .inductDecl _ _ types _ := decl then
    for type in types do
      let some (.inductInfo info) := env.find? type.name
        | return ← fail .internal "checked inductive information missing"
      if info.numNested != 0 then return ← fail .unsupported "nested inductive group"

/-- One packet-wide budget: decoding state, audit state, name count, and kernel
heartbeat quota are carried through every auxiliary declaration and the proof. -/
def checkPacket (env : Kernel.Environment) (lim : Limits) (expected : Expr)
    (input : String) : Except Failure Checked := do
  closed expected
  let (entries, proof) ← packetFields lim input
  let checks := entries.size + 1
  let quota := lim.kernelHeartbeats.toNat / checks
  if quota == 0 || lim.kernelRecDepth == 0 then return ← fail .resource "kernel budget per check"
  let mut checkedEnv := env
  let mut remaining := lim.maxNodes
  let mut names := 0
  let mut audit : AuditState := { remaining := lim.maxAuditSteps }
  for entry in entries do
    let (decl, left) ← (declarationField checkedEnv lim entry).run remaining
    remaining := left
    let declared := decl.getNames
    names := names + declared.length
    if names > lim.maxDeclarations then return ← fail .resource "declared constant names"
    let next ← forceDeclaration checkedEnv (USize.ofNat quota) lim.kernelRecDepth decl
    checkInductiveShape next decl
    audit ← auditNames next audit declared
    checkedEnv := next
  let (value, left) ← (exprField checkedEnv lim [] [] lim.maxExprDepth 0 proof).run remaining
  let finalAudit ← checkFinal checkedEnv lim (USize.ofNat quota) audit expected value
    (certificationPrefix.appendCore `proof)
  return {
    env := checkedEnv
    value
    declarations := entries.size
    constants := finalAudit.seen.size
    decoderSteps := lim.maxNodes - left
    auditSteps := lim.maxAuditSteps - finalAudit.remaining
    kernelChecks := checks }

end EDSLGrader.Runtime
