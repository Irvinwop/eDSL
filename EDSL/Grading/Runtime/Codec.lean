/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Runtime.Types

/-! The packet language is arrays and strings only. It carries no task, expected
type, imports, options, attributes, execution instructions, or environment settings.
Auxiliary declarations are checked sequentially; a group may mention its own type
names at the declared universe arity. Definitional hints and safety are fixed here. -/
namespace EDSLGrader.Runtime

open Lean

abbrev DecodeM := StateT Nat (Except Failure)

def spend : DecodeM Unit := do
  match ← get with
  | 0 => throw { kind := .resource, message := "decoder steps" }
  | n+1 => set n

def shape (x : Except String α) : DecodeM α :=
  match x with
  | .ok a => pure a
  | .error _ => throw { kind := .malformed, message := "field shape" }

def textField (lim : Limits) (j : Json) : DecodeM String := do
  let s ← shape j.getStr?
  if s.utf8ByteSize > lim.maxStringBytes then
    throw { kind := .resource, message := "string bytes" }
  return s

def decimal (lim : Limits) (j : Json) : DecodeM Nat := do
  let s ← textField lim j
  if s.utf8ByteSize > lim.maxDecimalChars then
    throw { kind := .resource, message := "decimal digits" }
  if s.isEmpty || !s.toList.all (fun c => '0' ≤ c && c ≤ '9') then
    throw { kind := .malformed, message := "decimal string" }
  let some n := s.toNat? | throw { kind := .malformed, message := "decimal string" }
  return n

def nameField (lim : Limits) (j : Json) : DecodeM Name := do
  let parts ← shape j.getArr?
  if parts.size > lim.maxNameParts then
    throw { kind := .resource, message := "name components" }
  let mut n := Name.anonymous
  for p in parts do
    spend
    match p with
    | .str _ => n := .str n (← textField lim p)
    | .arr #[.str "n", d] => n := .num n (← decimal lim d)
    | _ => throw { kind := .malformed, message := "name component" }
  return n

def paramsField (lim : Limits) (j : Json) : DecodeM (List Name) := do
  let fields ← shape j.getArr?
  if fields.size > lim.maxNameParts then
    throw { kind := .resource, message := "universe parameters" }
  let mut seen : NameSet := {}
  let mut names := #[]
  for p in fields do
    spend
    let n ← nameField lim p
    if n.isAnonymous || seen.contains n then
      throw { kind := .malformed, message := "duplicate or anonymous universe parameter" }
    seen := seen.insert n
    names := names.push n
  return names.toList

def levelField (lim : Limits) (params : List Name) : Nat → Json → DecodeM Level
  | 0, _ => throw { kind := .resource, message := "expression depth" }
  | fuel+1, j => do
    spend
    match j with
    | .str "zero" => return .zero
    | .arr #[.str "succ", u] => return .succ (← levelField lim params fuel u)
    | .arr #[.str "max", u, v] =>
      return .max (← levelField lim params fuel u) (← levelField lim params fuel v)
    | .arr #[.str "imax", u, v] =>
      return .imax (← levelField lim params fuel u) (← levelField lim params fuel v)
    | .arr #[.str "param", n] =>
      let n ← nameField lim n
      unless params.contains n do
        throw { kind := .malformed, message := "undeclared universe parameter" }
      return .param n
    | .arr #[.str "mvar", _] =>
      throw { kind := .malformed, message := "universe metavariable" }
    | _ => throw { kind := .malformed, message := "universe expression" }

def binderField : Json → DecodeM BinderInfo
  | .str "default" => pure .default
  | .str "implicit" => pure .implicit
  | .str "strictImplicit" => pure .strictImplicit
  | .str "instImplicit" => pure .instImplicit
  | _ => throw { kind := .malformed, message := "binder" }

def constantArity (env : Kernel.Environment) (pending : List (Name × Nat))
    (n : Name) : DecodeM Nat := do
  if let some info := env.find? n then return info.levelParams.length
  if let some (_, arity) := pending.find? (fun p => p.1 == n) then return arity
  throw { kind := .malformed, message := "unknown constant" }

def exprField (env : Kernel.Environment) (lim : Limits) (params : List Name := [])
    (pending : List (Name × Nat) := []) : Nat → Nat → Json → DecodeM Expr
  | 0, _, _ => throw { kind := .resource, message := "expression depth" }
  | fuel+1, binders, j => do
    spend
    match j with
    | .arr #[.str "bvar", i] =>
      let i ← decimal lim i
      if i ≥ binders then throw { kind := .malformed, message := "loose bound variable" }
      return .bvar i
    | .arr #[.str "sort", u] => return .sort (← levelField lim params fuel u)
    | .arr #[.str "const", n, us] =>
      let n ← nameField lim n
      let arity ← constantArity env pending n
      let us ← shape us.getArr?
      if us.size != arity then
        throw { kind := .malformed, message := "constant universe arity" }
      return .const n (← us.toList.mapM (levelField lim params fuel))
    | .arr #[.str "app", f, a] =>
      return .app (← exprField env lim params pending fuel binders f)
        (← exprField env lim params pending fuel binders a)
    | .arr #[.str "lam", bi, t, b] =>
      return .lam .anonymous (← exprField env lim params pending fuel binders t)
        (← exprField env lim params pending fuel (binders+1) b) (← binderField bi)
    | .arr #[.str "forall", bi, t, b] =>
      return .forallE .anonymous (← exprField env lim params pending fuel binders t)
        (← exprField env lim params pending fuel (binders+1) b) (← binderField bi)
    | .arr #[.str "let", t, v, b] =>
      return .letE .anonymous (← exprField env lim params pending fuel binders t)
        (← exprField env lim params pending fuel binders v)
        (← exprField env lim params pending fuel (binders+1) b) false
    | .arr #[.str "nat", n] => return .lit (.natVal (← decimal lim n))
    | .arr #[.str "str", s] => return .lit (.strVal (← textField lim s))
    | .arr #[.str "proj", n, i, e] =>
      let n ← nameField lim n
      let _ ← constantArity env pending n
      return .proj n (← decimal lim i) (← exprField env lim params pending fuel binders e)
    | .arr #[.str "fvar", _] => throw { kind := .malformed, message := "free variable" }
    | .arr #[.str "mvar", _] => throw { kind := .malformed, message := "expression metavariable" }
    | _ => throw { kind := .malformed, message := "expression shape" }

/-- Runs before Json.parse. Raw strings allow worst-case JSON escaping, then decoded
strings receive the tighter UTF-8 bound. Numeric/object/bool/null tokens never reach
the JSON parser. Input is already allocated; bounded file IO belongs to the caller. -/
def preflight (lim : Limits) (input : String) : Except Failure Unit := do
  if input.utf8ByteSize > lim.maxInputBytes then return ← fail .resource "input bytes"
  let mut depth := 0
  let mut quoted := false
  let mut escaped := false
  let mut rawBytes := 0
  let mut tokens := 0
  for c in input do
    if quoted then
      rawBytes := rawBytes + c.utf8Size
      if rawBytes > 6 * lim.maxStringBytes + 2 then return ← fail .resource "raw string bytes"
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then quoted := false
    else if c == '"' then
      quoted := true
      rawBytes := 0
      tokens := tokens + 1
    else if c == '[' then
      depth := depth + 1
      tokens := tokens + 1
      if depth > lim.maxJsonDepth then return ← fail .resource "JSON depth"
    else if c == ']' then
      if depth == 0 then return ← fail .malformed "JSON brackets"
      depth := depth - 1
    else if c != ',' && c != ' ' && c != '\n' && c != '\r' && c != '\t' then
      return ← fail .malformed "JSON token"
    if tokens > lim.maxNodes * 8 + lim.maxDeclarations * 16 + 32 then
      return ← fail .resource "JSON tokens"
  if quoted || depth != 0 then return ← fail .malformed "JSON termination"

def packetFields (lim : Limits) (input : String) : Except Failure (Array Json × Json) := do
  preflight lim input
  let j ← (Json.parse input).mapError fun _ => { kind := .malformed, message := "JSON syntax" }
  match j with
  | .arr #[.str "edsl-proof-v1", .arr decls, value] =>
    if decls.size > lim.maxDeclarations then return ← fail .resource "declaration entries"
    return (decls, value)
  | _ => fail .malformed "packet shape or version"

def freshNames (env : Kernel.Environment) (names : List Name) : DecodeM Unit := do
  let mut seen : NameSet := {}
  for n in names do
    spend
    if n.isAnonymous then throw { kind := .malformed, message := "anonymous declaration name" }
    if certificationPrefix.isPrefixOf n then
      throw { kind := .rejected, message := "reserved certification name" }
    if seen.contains n || (env.find? n).isSome then
      throw { kind := .rejected, message := "declaration name collision" }
    seen := seen.insert n

/-- Only the inductive group's type names are pending, never its constructors or
recursors. All declarations still go through forced kernel typing/positivity checks. -/
def declarationField (env : Kernel.Environment) (lim : Limits) (j : Json) : DecodeM Declaration := do
  spend
  match j with
  | .arr #[.str tag, n, ps, t, v] =>
    unless tag == "theorem" || tag == "def" || tag == "opaque" do
      if tag == "inductive" then
        throw { kind := .malformed, message := "declaration shape" }
      throw { kind := .unsupported, message := "declaration kind" }
    let n ← nameField lim n
    freshNames env [n]
    let ps ← paramsField lim ps
    let t ← exprField env lim ps [] lim.maxExprDepth 0 t
    let v ← exprField env lim ps [] lim.maxExprDepth 0 v
    if tag == "theorem" then return .thmDecl { name := n, levelParams := ps, type := t, value := v }
    if tag == "def" then
      return .defnDecl {
        name := n
        levelParams := ps
        type := t
        value := v
        hints := .regular 0
        safety := .safe }
    return .opaqueDecl { name := n, levelParams := ps, type := t, value := v, isUnsafe := false }
  | .arr #[.str "inductive", ps, np, .arr entries] =>
    if entries.isEmpty then throw { kind := .malformed, message := "empty inductive group" }
    if entries.size > lim.maxDeclarations then
      throw { kind := .resource, message := "inductive types" }
    let ps ← paramsField lim ps
    let np ← decimal lim np
    let mut headers : Array (Name × Json × Array Json) := #[]
    let mut names := []
    for entry in entries do
      spend
      let .arr #[n, t, .arr ctors] := entry
        | throw { kind := .malformed, message := "inductive type entry" }
      let n ← nameField lim n
      names := n :: (n.appendCore `rec) :: names
      if ctors.size > lim.maxDeclarations then
        throw { kind := .resource, message := "inductive constructors" }
      for ctor in ctors do
        spend
        let .arr #[cn, _] := ctor
          | throw { kind := .malformed, message := "constructor entry" }
        names := (← nameField lim cn) :: names
      headers := headers.push (n, t, ctors)
    if names.length > lim.maxDeclarations then
      throw { kind := .resource, message := "declared constant names" }
    freshNames env names
    let pending := headers.toList.map fun (n, _, _) => (n, ps.length)
    let mut types := #[]
    for (n, t, ctors) in headers do
      let t ← exprField env lim ps pending lim.maxExprDepth 0 t
      let mut cs := #[]
      for ctor in ctors do
        let .arr #[cn, ct] := ctor
          | throw { kind := .malformed, message := "constructor entry" }
        cs := cs.push {
          name := ← nameField lim cn
          type := ← exprField env lim ps pending lim.maxExprDepth 0 ct : Constructor }
      types := types.push { name := n, type := t, ctors := cs.toList : InductiveType }
    return .inductDecl ps np types.toList false
  | .arr fields =>
    if let some (Json.str tag) := fields[0]? then
      if ["theorem", "def", "opaque", "inductive"].contains tag then
        throw { kind := .malformed, message := "declaration shape" }
      throw { kind := .unsupported, message := "declaration kind" }
    throw { kind := .malformed, message := "declaration shape" }
  | _ => throw { kind := .malformed, message := "declaration shape" }

def nameJson (n : Name) : Json := .arr (parts n)
where
  parts : Name → Array Json
  | .anonymous => #[]
  | .str p s => (parts p).push (.str s)
  | .num p n => (parts p).push (.arr #[.str "n", .str (toString n)])

def levelJson : Level → Except Failure Json
  | .zero => pure (.str "zero")
  | .succ u => return .arr #[.str "succ", ← levelJson u]
  | .max u v => return .arr #[.str "max", ← levelJson u, ← levelJson v]
  | .imax u v => return .arr #[.str "imax", ← levelJson u, ← levelJson v]
  | .param n => return .arr #[.str "param", nameJson n]
  | .mvar _ => fail .malformed "cannot encode universe metavariable"

def binderJson : BinderInfo → Json
  | .default => .str "default"
  | .implicit => .str "implicit"
  | .strictImplicit => .str "strictImplicit"
  | .instImplicit => .str "instImplicit"

/-- Binder names, metadata, and let.nondep are kernel-irrelevant and canonicalized. -/
def encodeExpr : Expr → Except Failure Json
  | .bvar n => return .arr #[.str "bvar", .str (toString n)]
  | .sort u => return .arr #[.str "sort", ← levelJson u]
  | .const n us => return .arr #[.str "const", nameJson n, .arr (← us.toArray.mapM levelJson)]
  | .app f a => return .arr #[.str "app", ← encodeExpr f, ← encodeExpr a]
  | .lam _ t b bi => return .arr #[.str "lam", binderJson bi, ← encodeExpr t, ← encodeExpr b]
  | .forallE _ t b bi => return .arr #[.str "forall", binderJson bi, ← encodeExpr t, ← encodeExpr b]
  | .letE _ t v b _ => return .arr #[.str "let", ← encodeExpr t, ← encodeExpr v, ← encodeExpr b]
  | .lit (.natVal n) => return .arr #[.str "nat", .str (toString n)]
  | .lit (.strVal s) => return .arr #[.str "str", .str s]
  | .proj n i e => return .arr #[.str "proj", nameJson n, .str (toString i), ← encodeExpr e]
  | .mdata _ e => encodeExpr e
  | _ => fail .malformed "cannot encode free variable or metavariable"

def encodeDeclaration : Declaration → Except Failure Json
  | .thmDecl v => return .arr #[.str "theorem", nameJson v.name,
      .arr (v.levelParams.toArray.map nameJson), ← encodeExpr v.type, ← encodeExpr v.value]
  | .defnDecl v => do
    unless v.safety == .safe do return ← fail .audit "unsafe or partial definition"
    return .arr #[.str "def", nameJson v.name, .arr (v.levelParams.toArray.map nameJson),
      ← encodeExpr v.type, ← encodeExpr v.value]
  | .opaqueDecl v => do
    if v.isUnsafe then return ← fail .audit "unsafe opaque"
    return .arr #[.str "opaque", nameJson v.name, .arr (v.levelParams.toArray.map nameJson),
      ← encodeExpr v.type, ← encodeExpr v.value]
  | .inductDecl ps np types unsafeFlag => do
    if unsafeFlag then return ← fail .audit "unsafe inductive"
    let entries ← types.toArray.mapM fun t => do
      let cs ← t.ctors.toArray.mapM fun c => return .arr #[nameJson c.name, ← encodeExpr c.type]
      return .arr #[nameJson t.name, ← encodeExpr t.type, .arr cs]
    return .arr #[.str "inductive", .arr (ps.toArray.map nameJson), .str (toString np), .arr entries]
  | _ => fail .unsupported "declaration kind"

def encodePacket (decls : List Declaration) (value : Expr) : Except Failure String := do
  return (Json.arr #[.str "edsl-proof-v1", .arr (← decls.toArray.mapM encodeDeclaration),
    ← encodeExpr value]).compress

end EDSLGrader.Runtime
