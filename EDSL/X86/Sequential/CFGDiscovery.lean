/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFG

namespace EDSL.X86.Sequential.CFG

inductive DiscoveryError where
  | empty
  | byteLimit
  | instructionLimit
  | decode (offset : Nat) (error : Error)
  | truncated (offset : Nat)
  | unsupportedInstruction (offset : Nat)
  | invalidGraph
  deriving DecidableEq, Repr

/-- Scan the entire explicitly supplied window, including instructions after
an early RET. Discovery proposes data; `check` independently validates it. -/
private def decodeNodes (bytes : List Byte) : Nat → Nat → Except DiscoveryError (List Node)
  | remaining, offset => do
    if offset = bytes.length then return []
    if offset > bytes.length then throw (.truncated offset)
    match remaining with
    | 0 => throw .instructionLimit
    | fuel + 1 =>
      let instruction ← (decodeAt (codeState bytes offset)).mapError (.decode offset)
      if !readOnly instruction then throw (.unsupportedInstruction offset)
      let finish := offset + instruction.length
      if finish > bytes.length then throw (.truncated offset)
      let rest ← decodeNodes bytes fuel finish
      return ⟨offset, instruction, false, 0⟩ :: rest

/-- Entry and nonforward-edge targets are proposed cutpoints. The proposed
interior depths decrease with linear instruction index. All fields are checked
again, so this heuristic carries no semantic trust. -/
def annotate (nodes : List Node) : Graph :=
  let targets := nodes.flatMap fun node =>
    node.successors.filterMap fun target =>
      if target.toNat ≤ node.offset then some target.toNat else none
  ⟨nodes.mapIdx (fun index node => { node with
    cutpoint := decide (node.offset = 0) || targets.contains node.offset
    depth := nodes.length - index }), nodes.length⟩

/-- Discover and validate a read-only CFG with sparse cutpoints. Successful
discovery establishes finite code facts, not a program's functional contract. -/
def analyze (bytes : List Byte) : Except DiscoveryError Graph :=
  if bytes.isEmpty then .error .empty
  else if bytes.length > 64 then .error .byteLimit
  else do
    let nodes ← decodeNodes bytes 32 0
    let graph := annotate nodes
    if check bytes graph then return graph else throw .invalidGraph

def discover (bytes : List Byte) : Option Graph := (analyze bytes).toOption

theorem analyze_checked {bytes : List Byte} {graph : Graph}
    (accepted : analyze bytes = .ok graph) : check bytes graph = true := by
  by_cases empty : bytes.isEmpty
  · simp [analyze, empty] at accepted
  · by_cases large : bytes.length > 64
    · simp [analyze, empty, large] at accepted
    · cases decoded : decodeNodes bytes 32 0 with
      | error fault => simp [analyze, empty, large, decoded] at accepted
      | ok nodes =>
        cases checked : check bytes (annotate nodes) with
        | false => simp [analyze, empty, large, decoded, checked] at accepted
        | true =>
          have same : annotate nodes = graph := by
            simpa [analyze, empty, large, decoded, checked] using accepted
          simpa only [same] using checked

theorem analyze_sound {bytes : List Byte} {graph : Graph}
    (accepted : analyze bytes = .ok graph) : Valid bytes graph :=
  check_sound (analyze_checked accepted)

theorem discover_sound {bytes : List Byte} {graph : Graph}
    (accepted : discover bytes = some graph) : Valid bytes graph := by
  cases result : analyze bytes with
  | error fault =>
    simp only [discover, result] at accepted
    cases accepted
  | ok candidate =>
    have same : candidate = graph := by simpa only [discover, result, Except.toOption, Option.some.injEq] using accepted
    subst candidate
    exact analyze_sound result

end EDSL.X86.Sequential.CFG
