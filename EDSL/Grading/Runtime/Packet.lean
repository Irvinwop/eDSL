/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Runtime.DAG

/-! Packet versions choose expression representation only. They cannot choose
the expected theorem, environment, kernel checking or dependency policy. -/
namespace EDSLGrader.Runtime
open Lean

namespace Packet

inductive Syntax where
  | tree | dag
  deriving BEq, Repr

structure Fields where
  dialect : Syntax
  declarations : Array Json
  proof : Json

/-- Both versions share bounded token preflight and declaration admission.
Every expression field uses the dialect fixed by the packet's version. -/
def fields (lim : Limits) (input : String) : Except Failure Fields := do
  preflight lim input
  let j ← (Json.parse input).mapError fun _ => { kind := .malformed, message := "JSON syntax" }
  let (dialect, decls, value) ← match j with
    | .arr #[.str "edsl-proof-v1", .arr decls, value] => pure (Syntax.tree, decls, value)
    | .arr #[.str "edsl-proof-v2", .arr decls, value] => pure (Syntax.dag, decls, value)
    | _ => fail .malformed "packet shape or version"
  if decls.size > lim.maxDeclarations then return ← fail .resource "declaration entries"
  return ⟨dialect, decls, value⟩

def expression (dialect : Syntax) (env : Kernel.Environment) (lim : Limits)
    (params : List Name := []) (pending : List (Name × Nat) := []) (value : Json) : DecodeM Expr :=
  match dialect with
  | .tree => exprField env lim params pending lim.maxExprDepth 0 value
  | .dag => DAG.decodeDag env lim params pending value

def declaration (dialect : Syntax) (env : Kernel.Environment) (lim : Limits)
    (value : Json) : DecodeM Declaration :=
  declarationFieldWith env lim
    (fun params pending field => expression dialect env lim params pending field) value

end Packet

/-- New clients preserve shared subexpressions in each independent type/value
field. Legacy v1 tree packets remain accepted by the same checked boundary. -/
def encodePacket (decls : List Declaration) (value : Expr) : Except Failure String := do
  return (Json.arr #[.str "edsl-proof-v2",
    .arr (← decls.toArray.mapM (encodeDeclarationWith DAG.encodeDag)),
    ← DAG.encodeDag value]).compress

end EDSLGrader.Runtime
