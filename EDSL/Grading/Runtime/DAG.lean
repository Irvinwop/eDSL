/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Runtime.Codec
import Std.Data.HashMap

/-! A data-only, per-expression DAG codec. Child references are strictly backward;
no declaration, inferred type, substitution or universe context is cached in a
node. Decoding preserves the kernel expression syntax, with v1's irrelevant binder
names, metadata and let.nondep canonicalization. -/
namespace EDSLGrader.Runtime.DAG
open Lean

private structure Node where
  expr : Expr
  /-- Exact expanded syntax height, including universe constructors as in v1. -/
  height : Nat
  /-- Minimum number of enclosing binders required by this node. -/
  need : Nat
  children : Array Nat := #[]
  deriving Inhabited

private def levelHeight : Level → Nat
  | .zero | .param _ | .mvar _ => 1
  | .succ u => 1 + levelHeight u
  | .max u v | .imax u v => 1 + max (levelHeight u) (levelHeight v)

private def refField (lim : Limits) (nodes : Array Node) (j : Json) : DecodeM (Nat × Node) := do
  spend
  let i ← decimal lim j
  let some node := nodes[i]?
    | throw { kind := .malformed, message := "DAG forward, cyclic, or missing reference" }
  return (i, node)

private def rowField (env : Kernel.Environment) (lim : Limits) (params : List Name)
    (pending : List (Name × Nat)) (nodes : Array Node) (j : Json) : DecodeM Node := do
  spend
  let node ← match j with
    | .arr #[.str "bvar", i] => do
      let i ← decimal lim i
      -- This bound follows from the height cap for any reachable closed root.
      if i ≥ lim.maxExprDepth then
        throw { kind := .resource, message := "DAG bound variable range" }
      pure { expr := .bvar i, height := 1, need := i+1 }
    | .arr #[.str "sort", u] => do
      let u ← levelField lim params (lim.maxExprDepth - 1) u
      pure { expr := .sort u, height := 1 + levelHeight u, need := 0 }
    | .arr #[.str "const", n, us] => do
      let n ← nameField lim n
      let arity ← constantArity env pending n
      let us ← shape us.getArr?
      if us.size != arity then
        throw { kind := .malformed, message := "constant universe arity" }
      let us ← us.toList.mapM (levelField lim params (lim.maxExprDepth - 1))
      let h := 1 + us.foldl (fun h u => max h (levelHeight u)) 0
      pure { expr := .const n us, height := h, need := 0 }
    | .arr #[.str "app", f, a] => do
      let (fi, f) ← refField lim nodes f
      let (ai, a) ← refField lim nodes a
      pure {
        expr := .app f.expr a.expr
        height := 1 + max f.height a.height
        need := max f.need a.need
        children := #[fi, ai] }
    | .arr #[.str "let", t, v, b] => do
      let (ti, t) ← refField lim nodes t
      let (vi, v) ← refField lim nodes v
      let (bi, b) ← refField lim nodes b
      pure {
        expr := .letE .anonymous t.expr v.expr b.expr false
        height := 1 + max (max t.height v.height) b.height
        need := max (max t.need v.need) (b.need - 1)
        children := #[ti, vi, bi] }
    | .arr #[.str "nat", n] => do
      pure { expr := .lit (.natVal (← decimal lim n)), height := 1, need := 0 }
    | .arr #[.str "str", s] => do
      pure { expr := .lit (.strVal (← textField lim s)), height := 1, need := 0 }
    | .arr #[.str "proj", n, i, e] => do
      let n ← nameField lim n
      let _ ← constantArity env pending n
      let i ← decimal lim i
      if i ≥ lim.maxNodes then
        throw { kind := .resource, message := "DAG projection index" }
      let (ei, e) ← refField lim nodes e
      pure { expr := .proj n i e.expr, height := 1 + e.height, need := e.need, children := #[ei] }
    | .arr #[.str tag, bi, t, b] => do
      unless tag == "lam" || tag == "forall" do
        throw { kind := .malformed, message := "DAG expression constructor" }
      let bi ← binderField bi
      let (ti, t) ← refField lim nodes t
      let (bi', b) ← refField lim nodes b
      let expr := if tag == "lam" then Expr.lam .anonymous t.expr b.expr bi
        else Expr.forallE .anonymous t.expr b.expr bi
      pure {
        expr
        height := 1 + max t.height b.height
        need := max t.need (b.need - 1)
        children := #[ti, bi'] }
    | _ => throw { kind := .malformed, message := "DAG expression shape" }
  if node.height > lim.maxExprDepth then
    throw { kind := .resource, message := "expanded DAG expression depth" }
  return node

/-- Every pool is new, binds its own universe context, and contains only reachable
nodes. References preserve syntax: no substitution, shifting, or inferred types. -/
private def decodeDagSummary (env : Kernel.Environment) (lim : Limits) (params : List Name := [])
    (pending : List (Name × Nat) := []) (j : Json) : DecodeM Node := do
  let .arr #[.str "dag", .arr rows, root] := j
    | throw { kind := .malformed, message := "DAG expression envelope" }
  if rows.size > lim.maxNodes then
    throw { kind := .resource, message := "DAG node count" }
  let mut nodes : Array Node := #[]
  for row in rows do
    nodes := nodes.push (← rowField env lim params pending nodes row)
  let (rootId, node) ← refField lim nodes root
  if node.need != 0 then
    throw { kind := .malformed, message := "loose bound variable at DAG root" }
  -- Reverse topological reachability needs bounded work and no recursive DFS.
  let mut live := (Array.replicate nodes.size false).set! rootId true
  for offset in [:nodes.size] do
    spend
    let i := nodes.size - 1 - offset
    if live[i]! then
      for child in nodes[i]!.children do
        spend
        live := live.set! child true
  if !live.all id then
    throw { kind := .malformed, message := "unreachable DAG node" }
  return node

/-- Each field owns its pool; the caller carries DecodeM fuel across the packet. -/
def decodeDag (env : Kernel.Environment) (lim : Limits) (params : List Name := [])
    (pending : List (Name × Nat) := []) (j : Json) : DecodeM Expr := do
  return (← decodeDagSummary env lim params pending j).expr

private structure EncodeState where
  -- Expr's ordinary equality ignores BinderInfo. Structural keys retain those
  -- annotations so interning preserves the tree codec's canonical syntax.
  ids : Std.HashMap ExprStructEq Nat := {}
  rows : Array Json := #[]
  remaining : Nat := ({} : Limits).maxNodes

private abbrev EncodeM := StateT EncodeState (Except Failure)

private def encodeNode : Nat → Expr → EncodeM Nat
  | 0, _ => throw { kind := .resource, message := "client DAG depth" }
  | fuel+1, e => do
    let budget ← get
    if budget.remaining == 0 then
      throw { kind := .resource, message := "client DAG encoding steps" }
    set { budget with remaining := budget.remaining - 1 }
    if let some i := (← get).ids[ExprStructEq.mk e]? then return i
    let s (n : Nat) := Json.str (toString n)
    if let .mdata _ v := e then return ← encodeNode fuel v
    let row : Json ← match e with
      | .bvar n => pure <| Json.arr #[.str "bvar", s n]
      | .sort u => do pure <| Json.arr #[.str "sort", ← liftM (levelJson u)]
      | .const n us => do
        pure <| Json.arr #[.str "const", nameJson n,
          .arr (← us.toArray.mapM (fun u => liftM (levelJson u)))]
      | .app f a => do
        pure <| Json.arr #[.str "app", s (← encodeNode fuel f), s (← encodeNode fuel a)]
      | .lam _ t b bi => do
        pure <| Json.arr #[.str "lam", binderJson bi,
          s (← encodeNode fuel t), s (← encodeNode fuel b)]
      | .forallE _ t b bi => do
        pure <| Json.arr #[.str "forall", binderJson bi,
          s (← encodeNode fuel t), s (← encodeNode fuel b)]
      | .letE _ t v b _ => do
        pure <| Json.arr #[.str "let", s (← encodeNode fuel t),
          s (← encodeNode fuel v), s (← encodeNode fuel b)]
      | .lit (.natVal n) => pure <| .arr #[.str "nat", s n]
      | .lit (.strVal v) => pure <| .arr #[.str "str", .str v]
      | .proj n i v => do
        pure <| Json.arr #[.str "proj", nameJson n, s i, s (← encodeNode fuel v)]
      | _ => throw { kind := .malformed, message := "cannot encode free variable or metavariable" }
    let state ← get
    let i := state.rows.size
    set { state with ids := state.ids.insert (ExprStructEq.mk e) i, rows := state.rows.push row }
    return i

/-- Bounded client encoder. Runtime packet limits are still checked independently. -/
def encodeDag (e : Expr) : Except Failure Json := do
  let (root, state) ← (encodeNode ({} : Limits).maxExprDepth e).run {}
  return .arr #[.str "dag", .arr state.rows, .str (toString root)]

end EDSLGrader.Runtime.DAG
