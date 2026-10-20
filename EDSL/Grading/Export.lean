/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL
import EDSL.Grading.Runtime.Checker
import Lean.Util.Path

/-! Client-side reconstruction of proof packets from compiled modules. This is
not a submission loader: only the client imports the requested module. The
grader separately supplies its fixed environment, task and artifact contract.

Names already present in the trusted snapshot remain references. Fresh safe
definitions, theorems, opaque declarations and simple nonnested inductive groups
are emitted in dependency order. Generated constructors and `.rec` constants
belong to their inductive group; other generated definitions are ordinary
dependencies. Mutual definitions, fresh axioms and nested inductives fail
explicitly. Source `partial` syntax can have safe opaque logical metadata; this
exporter, like the runtime, checks logical metadata rather than source history.
-/
namespace EDSLGrader.Export

open Lean EDSLGrader.Runtime

inductive Mode where
  | reference
  | body
  deriving BEq, Repr, Inhabited

/-- Client closure limits. The independent runtime applies its own packet,
expression, audit and kernel budgets when the exported data is submitted. -/
structure Limits where
  maxSteps : Nat := 100000
  maxDeclarations : Nat := 256
  maxOutputBytes : Nat := 4194304

structure Packet where
  declarations : List Declaration
  value : Expr
  text : String
  /-- Includes constructors and generated recursors, not just packet entries. -/
  declaredNames : Nat
  discoverySteps : Nat

private def lookup (client : Kernel.Environment) (name : Name) : Except Failure ConstantInfo :=
  match client.find? name with
  | some info => pure info
  | none => fail .unsupported s!"client constant unavailable: {name}"

private def safeInfo (info : ConstantInfo) : Except Failure Unit := do
  if info.isUnsafe then return ← fail .audit s!"unsafe client constant: {info.name}"
  if info.isPartial then return ← fail .audit s!"partial client constant: {info.name}"

/-- Recover the entire kernel inductive group, including its original order,
universe parameters and parameter count. Constructor types supply the original
headers; no client constant is inserted into the trusted environment. -/
private def inductiveDeclaration (client : Kernel.Environment) (lim : Limits)
    (name : Name) : Except Failure Declaration := do
  let .inductInfo first ← lookup client name
    | fail .unsupported s!"inductive owner unavailable: {name}"
  if first.all.isEmpty then return ← fail .unsupported "empty inductive owner group"
  if first.all.length > lim.maxDeclarations then
    return ← fail .resource "client inductive group names"
  let mut types := []
  let mut names := 0
  for typeName in first.all do
    let info ← lookup client typeName
    safeInfo info
    let .inductInfo member := info
      | fail .unsupported s!"invalid inductive group member: {typeName}"
    if member.numNested != 0 then return ← fail .unsupported "nested client inductive group"
    if member.all != first.all || member.levelParams != first.levelParams ||
        member.numParams != first.numParams then
      return ← fail .unsupported "inconsistent client inductive group metadata"
    names := names + 2 + member.ctors.length
    if names > lim.maxDeclarations then return ← fail .resource "client inductive group names"
    let mut ctors := []
    for ctorName in member.ctors do
      let ctorInfo ← lookup client ctorName
      safeInfo ctorInfo
      let .ctorInfo ctor := ctorInfo
        | fail .unsupported s!"constructor unavailable: {ctorName}"
      if ctor.induct != member.name then return ← fail .unsupported "constructor owner mismatch"
      ctors := { name := ctor.name, type := ctor.type : Constructor } :: ctors
    types := ({ name := member.name, type := member.type, ctors := ctors.reverse } : InductiveType) :: types
  return .inductDecl first.levelParams first.numParams types.reverse false

private def reconstruct (client : Kernel.Environment) (lim : Limits)
    (info : ConstantInfo) : Except Failure Declaration := do
  safeInfo info
  match info with
  | .defnInfo value =>
    if value.all != [value.name] then return ← fail .unsupported "mutual client definitions"
    return .defnDecl value
  | .thmInfo value =>
    if value.all != [value.name] then return ← fail .unsupported "mutual client theorems"
    return .thmDecl value
  | .opaqueInfo value =>
    if value.all != [value.name] then return ← fail .unsupported "mutual client opaque declarations"
    return .opaqueDecl value
  | .inductInfo value => inductiveDeclaration client lim value.name
  | .ctorInfo value => inductiveDeclaration client lim value.induct
  | .recInfo value =>
    let some owner := value.all.head?
      | fail .unsupported s!"recursor owner unavailable: {value.name}"
    let decl ← inductiveDeclaration client lim owner
    unless decl.getNames.contains value.name do
      return ← fail .unsupported s!"noncanonical client recursor: {value.name}"
    return decl
  | .axiomInfo _ => fail .audit s!"fresh client axiom: {info.name}"
  | .quotInfo _ => fail .unsupported "fresh quotient primitives"

private inductive Work where
  | visit (name : Name)
  | emit (owner : Name) (decl : Declaration)

private structure Closure where
  completed : NameSet := {}
  /-- Each generated name is claimed by exactly one scheduled declaration. -/
  owners : NameMap Name := {}
  active : NameSet := {}
  declarations : Array Declaration := #[]
  declaredNames : Nat := 0
  steps : Nat := 0

/-- Include bodies, recursor rules and constructor/inductive owner edges. The
runtime audits these independently after checked reconstruction. -/
private def dependencies (client : Kernel.Environment) (decl : Declaration) :
    Except Failure (List Name) := do
  let mut deps : NameSet := {}
  for name in decl.getNames do
    let info ← lookup client name
    safeInfo info
    deps := deps ++ directDependencies info
  -- Group self-references are legal in inductive headers and recursor rules.
  let own : NameSet := .ofList decl.getNames
  return deps.toList.filter fun name => !own.contains name

/-- A bounded iterative DFS: groups are claimed before visiting dependencies,
and emitted afterwards. Completed names are never reconstructed twice. -/
private def discover (trusted client : Kernel.Environment) (lim : Limits) :
    Nat → List Work → Closure → Except Failure Closure
  | _, [], state => pure state
  | 0, _ :: _, _ => fail .resource "client dependency discovery steps"
  | fuel + 1, work :: rest, state => do
    let state := { state with steps := state.steps + 1 }
    match work with
    | .emit owner decl =>
      let completed := decl.getNames.foldl (fun seen name => seen.insert name) state.completed
      discover trusted client lim fuel rest { state with
        completed := completed
        active := state.active.erase owner
        declarations := state.declarations.push decl }
    | .visit name =>
      if (trusted.find? name).isSome || state.completed.contains name then
        return ← discover trusted client lim fuel rest state
      if let some owner := state.owners.find? name then
        if state.active.contains owner then
          return ← fail .unsupported s!"cyclic client declaration dependency: {name}"
        return ← fail .internal "incomplete client group traversal"
      let info ← lookup client name
      let decl ← reconstruct client lim info
      let declared := decl.getNames
      let some owner := declared.head? | fail .internal "empty reconstructed declaration"
      let count := state.declaredNames + declared.length
      if count > lim.maxDeclarations then return ← fail .resource "client declared constant names"
      let mut owners := state.owners
      for generated in declared do
        if generated.isAnonymous || certificationPrefix.isPrefixOf generated then
          return ← fail .unsupported s!"reserved client declaration name: {generated}"
        if (trusted.find? generated).isSome then
          return ← fail .unsupported s!"client group overlaps trusted names: {generated}"
        if owners.contains generated then return ← fail .unsupported "overlapping client groups"
        owners := owners.insert generated owner
      let deps ← dependencies client decl
      if deps.length > fuel then return ← fail .resource "client dependency discovery steps"
      discover trusted client lim fuel
        (deps.map Work.visit ++ .emit owner decl :: rest)
        { state with owners, active := state.active.insert owner, declaredNames := count }

/-- Export a closed monomorphic theorem reference, or its actual proof body.
The theorem's type is used only to discover auxiliary type dependencies. It is
never selected as a grading contract or advertised as successful grading.
Trusted names are identified by name; the grader replays all data against its
own installed snapshot and independently selected expected proposition. -/
def exportTheorem (trusted client : Kernel.Environment) (theoremName : Name)
    (mode : Mode := .reference) (lim : Limits := {}) : Except Failure Packet := do
  let .thmInfo target ← lookup client theoremName
    | fail .unsupported s!"export target is not a theorem: {theoremName}"
  if !target.levelParams.isEmpty then return ← fail .unsupported "polymorphic export theorem"
  if target.all != [target.name] then return ← fail .unsupported "mutual export theorem"
  let value := match mode with
    | .reference => mkConst theoremName
    | .body => target.value
  closed target.type
  closed value
  let roots := target.type.getUsedConstants.toList ++ value.getUsedConstants.toList
  let state ← discover trusted client lim lim.maxSteps (roots.map Work.visit) {}
  let declarations := state.declarations.toList
  let text ← encodePacket declarations value
  if text.utf8ByteSize > lim.maxOutputBytes then return ← fail .resource "client packet output bytes"
  return {
    declarations
    value
    text
    declaredNames := state.declaredNames
    discoverySteps := state.steps }

/-- Client executable setup: respect the configured Lean search path, import the
fixed snapshot first, then separately read the locally compiled client module.
No plugins, environment extensions or user source compilation are requested.
This configured client snapshot does not replace the grader's pinned snapshot. -/
def loadEnvironments (moduleName : Name) : IO (Environment × Environment) := do
  initSearchPath (← findSysroot)
  let trusted ← importModules
    #[{ module := `EDSL },
      { module := `EDSL.Grading.Known }, { module := `EDSL.Grading.Artifact },
      { module := `EDSL.Grading.CallStack.Artifact },
      { module := `EDSL.Grading.CallMemory64.Artifact },
      { module := `EDSL.Grading.CallMemoryLoop64.Artifact },
      { module := `EDSL.Grading.AtomicLogical64.Artifact },
      { module := `EDSL.Grading.AtomicSet64.Artifact }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let client ← importModules #[{ module := moduleName }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  return (trusted, client)

end EDSLGrader.Export
