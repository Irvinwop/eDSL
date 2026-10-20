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

/-- Discover under an explicitly selected static admission profile. The node
counter bounds only this finite scan, never a program's dynamic execution.
Successful discovery is rechecked and establishes no functional contract. -/
def analyzeWith (profile : Profile) (bytes : List Byte) : Except DiscoveryError Graph :=
  if bytes.isEmpty then .error .empty
  else if bytes.length > profile.maxBytes then .error .byteLimit
  else do
    let nodes ← decodeNodes bytes profile.maxNodes 0
    let graph := annotate nodes
    if checkWith profile bytes graph then return graph else throw .invalidGraph

def discoverWith (profile : Profile) (bytes : List Byte) : Option Graph :=
  (analyzeWith profile bytes).toOption

/-- Unchanged 64-byte/32-node compatibility entry points. -/
def analyze (bytes : List Byte) : Except DiscoveryError Graph := analyzeWith defaultProfile bytes

def discover (bytes : List Byte) : Option Graph := (analyze bytes).toOption

variable {profile : Profile}

theorem analyzeWith_checked {bytes : List Byte} {graph : Graph}
    (accepted : analyzeWith profile bytes = .ok graph) : checkWith profile bytes graph = true := by
  by_cases empty : bytes.isEmpty
  · simp [analyzeWith, empty] at accepted
  · by_cases large : bytes.length > profile.maxBytes
    · simp [analyzeWith, empty, large] at accepted
    · cases decoded : decodeNodes bytes profile.maxNodes 0 with
      | error fault => simp [analyzeWith, empty, large, decoded] at accepted
      | ok nodes =>
        cases checked : checkWith profile bytes (annotate nodes) with
        | false => simp [analyzeWith, empty, large, decoded, checked] at accepted
        | true =>
          have same : annotate nodes = graph := by
            simpa [analyzeWith, empty, large, decoded, checked] using accepted
          simpa only [same] using checked

theorem analyzeWith_sound {bytes : List Byte} {graph : Graph}
    (accepted : analyzeWith profile bytes = .ok graph) : Valid bytes graph profile :=
  checkWith_sound (analyzeWith_checked accepted)

theorem discoverWith_sound {bytes : List Byte} {graph : Graph}
    (accepted : discoverWith profile bytes = some graph) : Valid bytes graph profile := by
  cases result : analyzeWith profile bytes with
  | error fault =>
    simp only [discoverWith, result] at accepted
    cases accepted
  | ok candidate =>
    have same : candidate = graph := by
      simpa only [discoverWith, result, Except.toOption, Option.some.injEq] using accepted
    subst candidate
    exact analyzeWith_sound result

theorem analyze_checked {bytes : List Byte} {graph : Graph}
    (accepted : analyze bytes = .ok graph) : check bytes graph = true := analyzeWith_checked accepted

theorem analyze_sound {bytes : List Byte} {graph : Graph}
    (accepted : analyze bytes = .ok graph) : Valid bytes graph := analyzeWith_sound accepted

theorem discover_sound {bytes : List Byte} {graph : Graph}
    (accepted : discover bytes = some graph) : Valid bytes graph := discoverWith_sound accepted

end EDSL.X86.Sequential.CFG
