/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Runtime.Types
import Lean.Util.FoldConsts

/-! Audit the actual checked constant map, including theorem/opaque bodies and
kernel-generated inductive/recursor structure. Imported collectAxioms summaries
are not the acceptance policy. The audit budget counts every queue pop, including
duplicates, and the visited set and remaining budget span the whole packet. -/
namespace EDSLGrader.Runtime

open Lean

structure AuditState where
  remaining : Nat
  seen : NameSet := {}

def closed (e : Expr) : Except Failure Unit := do
  if e.hasFVar then return ← fail .malformed "free variable"
  if e.hasExprMVar then return ← fail .malformed "expression metavariable"
  if e.hasLevelMVar then return ← fail .malformed "universe metavariable"
  if e.hasLevelParam then return ← fail .malformed "final universe parameter"
  if e.hasLooseBVars then return ← fail .malformed "loose bound variable"

def directDependencies (info : ConstantInfo) : NameSet := Id.run do
  let mut deps := info.getUsedConstantsAsSet
  match info with
  | .inductInfo v =>
    for n in v.all do deps := deps.insert n
    for n in v.ctors do deps := deps.insert n
  | .ctorInfo v => deps := deps.insert v.induct
  | .recInfo v =>
    for n in v.all do deps := deps.insert n
    for rule in v.rules do
      deps := deps.insert rule.ctor
      deps := deps ++ rule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return deps

def auditLoop (env : Kernel.Environment) : Nat → List Name → NameSet → Except Failure AuditState
  | remaining, [], seen => pure { remaining, seen }
  | 0, _ :: _, _ => fail .resource "audit steps"
  | fuel+1, name :: rest, seen => do
    if seen.contains name then return ← auditLoop env fuel rest seen
    let some info := env.find? name | return ← fail .audit "missing dependency"
    if info.isUnsafe then return ← fail .audit "unsafe dependency"
    if info.isPartial then return ← fail .audit "partial dependency metadata"
    if info.isAxiom && !([``propext, ``Quot.sound, ``Classical.choice].contains name) then
      return ← fail .audit "unapproved axiom"
    auditLoop env fuel ((directDependencies info).toList ++ rest) (seen.insert name)

def auditNames (env : Kernel.Environment) (state : AuditState) (names : List Name) :
    Except Failure AuditState :=
  auditLoop env state.remaining names state.seen

def auditExprs (env : Kernel.Environment) (state : AuditState) (expected value : Expr) :
    Except Failure AuditState :=
  auditNames env state (expected.getUsedConstants.toList ++ value.getUsedConstants.toList)

end EDSLGrader.Runtime
