/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Lean.Declaration
import Lean.Data.NameMap
import Std.Data.HashMap.Basic

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Pure, untrusted client-side expression preparation; no environment mutation,
inference, reduction, evaluation, encoder, or assertion of preservation.
The iterative walk memoizes ExprStructEq, not Expr's alpha-equivalent BEq.
A completed summary contains rewritten syntax and its minimum surrounding-binder
requirement; each use checks that requirement against its own context. Subtrees
with input binder/let/metadata labels replay those constructors from the current
input use, reusing other completed children. Metadata payloads are uninterpreted.
Only Expr.const and Expr.proj owner names are dependency references.
Declaration universe parameters are explicitly scoped; inserted RHSs remain
monomorphic even when the caller permits universe parameters.
Native Expr.equal/hash, closedness flags, name comparison, hash-table housekeeping and allocation/GC
are NOT primitive-fuel-bounded. They require the unchanged external process bounds.
Dispatcher counts do not establish a time, instruction, or memory theorem. -/
namespace EDSLGrader.Export.Prepare
open Lean

/-- Producer traversal caps; the independent checker retains its own policy. -/
structure Limits where
  maxSteps : Nat := 500000
  maxNameWork : Nat := 500000
  maxUnique : Nat := 100000
  maxPending : Nat := 100000
  maxNames : Nat := 4096
  maxRewrites : Nat := 10000
  maxKeys : Nat := 1024
  maxLevelParams : Nat := 64
  maxNameParts : Nat := 64
  maxComponentBytes : Nat := 4096

/-- Arrays retain duplicate requests so validation can reject them. -/
structure Preparation where
  definitionValues : Array (Name × Expr) := #[]
  inlineConstants : Array (Name × Expr) := #[]

/-- Validated transformation data; these tables are not proof certificates.
Validation metrics sum independent per-RHS walks, including repeated keys. -/
structure Tables where
  definitionValues : NameMap Expr := {}
  inlineConstants : NameMap Expr := {}
  validationSteps : Nat := 0
  validationNameWork : Nat := 0
  validationUnique : Nat := 0
  validationCacheHits : Nat := 0
  validationRebuilt : Nat := 0
  validationLabelReplays : Nat := 0

structure Summary where
  rewritten : Expr
  need : Nat := 0
  -- Labels in this INPUT subtree, excluding labels introduced by a fixed RHS.
  -- Replay on a hit avoids relying on native equality to distinguish every
  -- BinderInfo/name/let-nondep/metadata detail, including below cached parents.
  inputLabels : Bool := false

inductive Work where
  | visit (e : Expr) (binders : Nat)
  | finish (e : Expr) (binders : Nat)
  | rhsDone (key : Expr) (binders : Nat)
  | level (u : Level)
  | levels (us : List Level)

structure State where
  -- Absent = undiscovered; none = active; some summary = postorder complete.
  -- Local to exactly one rewrite invocation and its fixed substitution table.
  memo : Std.HashMap ExprStructEq (Option Summary) := {}
  todo : Array Work := #[]
  values : Array Summary := #[]
  seen : NameSet := {}
  references : Array Name := #[]
  steps : Nat := 0
  nameWork : Nat := 0
  completed : Nat := 0
  cacheHits : Nat := 0
  labelReplays : Nat := 0
  rebuilt : Nat := 0
  rewrites : Nat := 0
  metadataVisits : Nat := 0
  levelVisits : Nat := 0
  levelListLinks : Nat := 0
  peakPending : Nat := 1
  -- Discovered structural keys, including replaced constants/inserted RHSs.
  -- Neither expanded occurrence counts nor an output DAG histogram.
  kinds : Array Nat := Array.replicate 13 0

structure Outcome where
  output : Option Expr := none
  reason : String := ""
  state : State := {}

def Outcome.complete (o : Outcome) : Bool := o.output.isSome

private abbrev WalkM := ExceptT String (StateM State)
private def pending (s : State) : Nat := s.todo.size + s.values.size

private def pushWork (lim : Limits) (w : Work) : WalkM Unit := do
  let s ← get
  if pending s >= lim.maxPending then throw "pending work/result bound"
  set { s with todo := s.todo.push w, peakPending := max s.peakPending (pending s + 1) }

private def pushValue (lim : Limits) (v : Summary) : WalkM Unit := do
  let s ← get
  if pending s >= lim.maxPending then throw "pending work/result bound"
  set { s with values := s.values.push v, peakPending := max s.peakPending (pending s + 1) }

private def popValue : WalkM Summary := do
  let s ← get
  let some v := s.values.back? | throw "internal result underflow"
  set { s with values := s.values.pop }
  return v

private def checkScope (v : Summary) (depth : Nat) : WalkM Unit := do
  if v.need > depth then throw "loose bound variable (summary exceeds use context)"

private def complete (lim : Limits) (e : Expr) (depth : Nat) (v : Summary) : WalkM Unit := do
  checkScope v depth
  modify fun s => { s with
    memo := s.memo.insert (ExprStructEq.mk e) (some v)
    completed := s.completed + 1 }
  pushValue lim v

private def checkName (lim : Limits) (n : Name) : WalkM Unit := do
  let mut rest := n
  for _ in [:lim.maxNameParts] do
    let s ← get
    if s.nameWork >= lim.maxNameWork then throw "name-component work bound"
    set { s with nameWork := s.nameWork + 1 }
    match rest with
    | .anonymous => return
    | .str p v =>
      if v.utf8ByteSize > lim.maxComponentBytes then throw "name component byte bound"
      rest := p
    | .num p _ => rest := p
  throw "name part bound"

/-- A bounded declaration-universe context. Names are not global dependencies. -/
private def levelContext (lim : Limits) (params : List Name) : WalkM NameSet := do
  let mut rest := params
  let mut seen : NameSet := {}
  for _ in [:lim.maxLevelParams + 1] do
    match rest with
    | [] => return seen
    | n :: tail =>
      if seen.size >= lim.maxLevelParams then throw "universe parameter count bound"
      checkName lim n
      if n.isAnonymous || seen.contains n then throw "invalid or duplicate universe parameter"
      seen := seen.insert n
      rest := tail
  throw "universe parameter count bound"

private def recordReference (lim : Limits) (n : Name) : WalkM Unit := do
  let s ← get
  if !s.seen.contains n then
    if s.references.size >= lim.maxNames then throw "distinct reference bound"
    set { s with seen := s.seen.insert n, references := s.references.push n }

private def kind : Expr → Nat
  | .bvar _ => 0 | .fvar _ => 1 | .mvar _ => 2 | .sort _ => 3
  | .const _ _ => 4 | .app _ _ => 5 | .lam _ _ _ _ => 6
  | .forallE _ _ _ _ => 7 | .letE _ _ _ _ _ => 8
  | .lit (.natVal _) => 9 | .lit (.strVal _) => 10
  | .mdata _ _ => 11 | .proj _ _ _ => 12

/-- Schedule children after marking the key active, on discovery or label replay.
This helper never calls itself or step; children require later dispatches. -/
private def enter (lim : Limits) (inline : NameMap Expr) (e : Expr) (depth : Nat) : WalkM Unit := do
  match e with
  | .bvar i => complete lim e depth { rewritten := e, need := i + 1 }
  | .fvar _ | .mvar _ => throw "unsupported free variable or expression metavariable"
  | .lit _ => complete lim e depth { rewritten := e }
  | .sort u =>
    pushWork lim (.finish e depth)
    pushWork lim (.level u)
  | .const n us =>
    checkName lim n
    if let some rhs := inline.find? n then
      if !us.isEmpty then throw "replacement key with universe arguments"
      -- Raw tables cannot inherit declaration universes through an inserted RHS.
      -- This native closedness flag is subject to the external process envelope.
      if rhs.hasLevelParam then throw "replacement RHS must be monomorphic"
      let s ← get
      if s.rewrites >= lim.maxRewrites then throw "constant substitution bound"
      set { s with rewrites := s.rewrites + 1 }
      -- Do not cache this mapped constant or record its original reference.
      -- Raw tables need this independent depth0 RHS walk AND completion
      -- check, even if rhs is already memoized under an enclosing binder.
      pushWork lim (.rhsDone e depth)
      pushWork lim (.visit rhs 0)
    else
      recordReference lim n
      pushWork lim (.finish e depth)
      pushWork lim (.levels us)
  | .app f a =>
    pushWork lim (.finish e depth)
    pushWork lim (.visit a depth)
    pushWork lim (.visit f depth)
  | .lam _ t b _ | .forallE _ t b _ =>
    pushWork lim (.finish e depth)
    pushWork lim (.visit b (depth + 1))
    pushWork lim (.visit t depth)
  | .letE _ t v b _ =>
    pushWork lim (.finish e depth)
    pushWork lim (.visit b (depth + 1))
    pushWork lim (.visit v depth)
    pushWork lim (.visit t depth)
  | .mdata _ b =>
    pushWork lim (.finish e depth)
    pushWork lim (.visit b depth)
  | .proj n _ b =>
    checkName lim n
    if inline.contains n then throw "replacement in projection owner unsupported"
    recordReference lim n
    pushWork lim (.finish e depth)
    pushWork lim (.visit b depth)

/-- One dispatcher action. Native key comparison/housekeeping is not separately
fuelled. A universe list link/constructor always schedules a later action; no
input Expr/Level/list fold, equality walk, binder opening or recursive traversal. -/
private def step (lim : Limits) (inline : NameMap Expr) (params : NameSet) : Work → WalkM Unit
  | .visit e depth => do
    let s ← get
    match s.memo[ExprStructEq.mk e]? with
    | some (some v) =>
      checkScope v depth
      if v.inputLabels then
        -- Rebuild labels from THIS input, even below an application parent.
        -- Its other children can still use completed memo summaries.
        set { s with
          memo := s.memo.insert (ExprStructEq.mk e) none
          completed := s.completed - 1
          labelReplays := s.labelReplays + 1 }
        enter lim inline e depth
      else
        modify fun s => { s with cacheHits := s.cacheHits + 1 }
        -- Same fixed per-walk table: references of this completed rewritten
        -- result were already recorded. Never replay original references.
        pushValue lim v
    | some none => throw "active structural key (cyclic raw substitution or input)"
    | none =>
      if s.memo.size >= lim.maxUnique then throw "unique expression bound"
      let k := kind e
      set { s with
        memo := s.memo.insert (ExprStructEq.mk e) none
        kinds := s.kinds.set! k (s.kinds[k]! + 1)
        metadataVisits := s.metadataVisits + (if k == 11 then 1 else 0) }
      enter lim inline e depth
  | .finish e depth => do
    let v : Summary ← match e with
      | .sort _ | .const _ _ => pure { rewritten := e }
      | .app _ _ => do
        let a ← popValue
        let f ← popValue
        pure {
          rewritten := .app f.rewritten a.rewritten
          need := max f.need a.need
          inputLabels := f.inputLabels || a.inputLabels }
      | .lam n _ _ bi => do
        let b ← popValue
        let t ← popValue
        pure {
          rewritten := .lam n t.rewritten b.rewritten bi
          need := max t.need (b.need - 1)
          inputLabels := true }
      | .forallE n _ _ bi => do
        let b ← popValue
        let t ← popValue
        pure {
          rewritten := .forallE n t.rewritten b.rewritten bi
          need := max t.need (b.need - 1)
          inputLabels := true }
      | .letE n _ _ _ nondep => do
        let b ← popValue
        let v ← popValue
        let t ← popValue
        pure {
          rewritten := .letE n t.rewritten v.rewritten b.rewritten nondep
          need := max (max t.need v.need) (b.need - 1)
          inputLabels := true }
      | .mdata md _ => do
        let b ← popValue
        pure { rewritten := .mdata md b.rewritten, need := b.need, inputLabels := true }
      | .proj n i _ => do
        let b ← popValue
        pure { rewritten := .proj n i b.rewritten, need := b.need, inputLabels := b.inputLabels }
      | _ => throw "internal completion constructor"
    match e with
    | .sort _ | .const _ _ => pure ()
    | _ => modify fun s => { s with rebuilt := s.rebuilt + 1 }
    complete lim e depth v
  | .rhsDone e depth => do
    let rhs ← popValue
    if rhs.need != 0 then throw "replacement RHS is not independently closed"
    -- Only completion path for a mapped constant, after its actual RHS. The
    -- input constant has no context labels; introduced RHS labels belong to
    -- this fixed table and may be reused at later occurrences of the key.
    complete lim e depth { rhs with inputLabels := false }
  | .level u => do
    modify fun s => { s with levelVisits := s.levelVisits + 1 }
    match u with
    | .zero => pure ()
    | .param n =>
      checkName lim n
      if !params.contains n then throw "undeclared universe parameter"
    | .mvar _ => throw "universe metavariable"
    | .succ u => pushWork lim (.level u)
    | .max u v | .imax u v => do
      pushWork lim (.level v)
      pushWork lim (.level u)
  | .levels us =>
    match us with
    | [] => pure ()
    | u :: rest => do
      modify fun s => { s with levelListLinks := s.levelListLinks + 1 }
      pushWork lim (.levels rest)
      pushWork lim (.level u)

/-- Bounded sharing-aware syntactic traversal. Every cached/rebuilt result checks
its use context; root and raw substitution RHSs require need0. Declared universe names apply
only to normal input syntax; raw RHSs are independently monomorphic. On ANY failure,
output stays none. Partial state is diagnostic scratch, never a usable result.
The memo is not shared across rewrite calls, roots, or different tables. -/
def rewrite (lim : Limits) (inline : NameMap Expr) (e : Expr)
    (levelParams : List Name := []) : Outcome := Id.run do
  if lim.maxPending == 0 then return { reason := "zero pending bound" }
  let (context, initial) := (levelContext lim levelParams).run.run {}
  if let .error reason := context then return { reason, state := initial }
  let params := match context with
    | .ok names => names
    | .error _ => {}
  let mut s : State := { initial with todo := #[.visit e 0] }
  for _ in [:lim.maxSteps] do
    let some w := s.todo.back? | break
    s := { s with todo := s.todo.pop, steps := s.steps + 1 }
    let (status, next) := (step lim inline params w).run.run s
    s := next
    if let .error reason := status then return { reason, state := s }
  if !s.todo.isEmpty then return { reason := "expression work bound", state := s }
  if s.values.size != 1 then return { reason := "internal result count", state := s }
  let some root := s.values.back? | return { reason := "internal root missing", state := s }
  if root.need != 0 then return { reason := "root is not closed", state := s }
  return { output := some root.rewritten, state := s }

/-- Eligibility is supplied by the caller: exact fresh safe singleton definitions
in its snapshots, excluding trusted/reserved keys. Both kinds of map use it.
Validation shares aggregate walk/name fuel across all RHSs. The conservative
acyclic form permits inline -> definition-value keys, but forbids every inline
key in every RHS and every definition-value key in definition-value RHSs.
No RHS is accepted merely because a compiled candidate declared it well typed. -/
def validate (lim : Limits) (eligible : Name → Bool) (p : Preparation) : Except String Tables := do
  if p.definitionValues.size + p.inlineConstants.size > lim.maxKeys then throw "replacement key bound"
  let mut tables : Tables := {}
  let mut keys : NameSet := {}
  let mut steps := lim.maxSteps
  let mut nameWork := lim.maxNameWork
  for entries in #[p.definitionValues, p.inlineConstants] do
    for (n, _) in entries do
      let (status, state) := (checkName { lim with maxNameWork := nameWork } n).run.run {}
      if let .error reason := status then throw reason
      nameWork := nameWork - state.nameWork
      if n.isAnonymous || !eligible n then throw "ineligible replacement key"
      if keys.contains n then
        throw "duplicate or overlapping replacement key"
      keys := keys.insert n
  for (n, rhs) in p.definitionValues do
    tables := { tables with definitionValues := tables.definitionValues.insert n rhs }
  for (n, rhs) in p.inlineConstants do
    tables := { tables with inlineConstants := tables.inlineConstants.insert n rhs }
  for (isDefinition, entries) in #[(true, p.definitionValues), (false, p.inlineConstants)] do
    for (_, rhs) in entries do
      let result := rewrite { lim with maxSteps := steps, maxNameWork := nameWork } {} rhs
      if !result.complete then throw ("replacement RHS incomplete: " ++ result.reason)
      steps := steps - result.state.steps
      nameWork := nameWork - result.state.nameWork
      tables := { tables with
        validationUnique := tables.validationUnique + result.state.memo.size
        validationCacheHits := tables.validationCacheHits + result.state.cacheHits
        validationRebuilt := tables.validationRebuilt + result.state.rebuilt
        validationLabelReplays := tables.validationLabelReplays + result.state.labelReplays }
      for n in result.state.references do
        if tables.inlineConstants.contains n || (isDefinition && tables.definitionValues.contains n) then
          throw "unsupported replacement dependency (self/cross cycle or chained substitution)"
  return { tables with
    validationSteps := lim.maxSteps - steps
    validationNameWork := lim.maxNameWork - nameWork }

/-- Prepare a safe singleton definition value, retaining non-expression metadata.
Normal values use their declared universes. Value overrides require monomorphic
definitions; callers prepare the type separately using the same substitution. -/
def prepareDefinitionValue (lim : Limits) (tables : Tables) (original : DefinitionVal) : Outcome :=
  let singleton := match original.all with
    | [n] => n == original.name
    | _ => false
  if original.safety != .safe || !singleton then
    { reason := "unsupported unsafe/mutual definition" }
  else
    match tables.definitionValues.find? original.name with
    | some rhs =>
      if !original.levelParams.isEmpty then
        { reason := "polymorphic definition-value override" }
      else rewrite lim tables.inlineConstants rhs
    | none => rewrite lim tables.inlineConstants original.value original.levelParams

end EDSLGrader.Export.Prepare
