/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Audit
import EDSL.X86.Sequential.CFG

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

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
an early RET. The policy is checked at the original read-only rejection point,
before the length/truncation check. Discovery only proposes data. -/
private def decodeNodes (allowed : Instruction → Bool) (bytes : List Byte) :
    Nat → Nat → Except DiscoveryError (List Node)
  | remaining, offset => do
    if offset = bytes.length then return []
    if offset > bytes.length then throw (.truncated offset)
    match remaining with
    | 0 => throw .instructionLimit
    | fuel + 1 =>
      let instruction ← (decodeAt (codeState bytes offset)).mapError (.decode offset)
      if !allowed instruction then throw (.unsupportedInstruction offset)
      let finish := offset + instruction.length
      if finish > bytes.length then throw (.truncated offset)
      let rest ← decodeNodes allowed bytes fuel finish
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

/-- Shared untrusted proposal builder with explicit caps and an instruction
admission policy. It uses the production decoder and instruction lengths,
preserves every byte and decoded instruction, and reuses `annotate` unchanged.
Success here does not establish graph validity or any instruction behavior;
the consumer must independently check the proposal against the exact bytes. -/
def proposeWith (allowed : Instruction → Bool) (profile : Profile) (bytes : List Byte) :
    Except DiscoveryError Graph :=
  if bytes.isEmpty then .error .empty
  else if bytes.length > profile.maxBytes then .error .byteLimit
  else do
    let nodes ← decodeNodes allowed bytes profile.maxNodes 0
    return annotate nodes

/-- Discover under an explicitly selected static admission profile. The node
counter bounds only this finite scan, never a program's dynamic execution.
Successful discovery is rechecked and establishes no functional contract. -/
def analyzeWith (profile : Profile) (bytes : List Byte) : Except DiscoveryError Graph := do
  let graph ← proposeWith readOnly profile bytes
  if checkWith profile bytes graph then return graph else throw .invalidGraph

/-- Equality to the former read-only analysis body. Specializing the shared
scan to `readOnly` leaves its rejection point and offset unchanged; factoring
the proposal preserves the order of empty, byte-cap, scan and graph errors. -/
private theorem analyzeWith_readOnly_compat (profile : Profile) (bytes : List Byte) :
    analyzeWith profile bytes =
      (if bytes.isEmpty then .error .empty
      else if bytes.length > profile.maxBytes then .error .byteLimit
      else do
        let nodes ← decodeNodes readOnly bytes profile.maxNodes 0
        let graph := annotate nodes
        if checkWith profile bytes graph then return graph else throw .invalidGraph) := by
  by_cases empty : bytes.isEmpty
  · simp [analyzeWith, proposeWith, empty]
  · by_cases large : bytes.length > profile.maxBytes
    · simp [analyzeWith, proposeWith, empty, large]
    · cases decoded : decodeNodes readOnly bytes profile.maxNodes 0 with
      | error fault => simp [analyzeWith, proposeWith, empty, large, decoded]
      | ok nodes => simp [analyzeWith, proposeWith, empty, large, decoded]

def discoverWith (profile : Profile) (bytes : List Byte) : Option Graph :=
  (analyzeWith profile bytes).toOption

/-- Unchanged 64-byte/32-node compatibility entry points. -/
def analyze (bytes : List Byte) : Except DiscoveryError Graph := analyzeWith defaultProfile bytes

def discover (bytes : List Byte) : Option Graph := (analyze bytes).toOption

variable {profile : Profile}

theorem analyzeWith_checked {bytes : List Byte} {graph : Graph}
    (accepted : analyzeWith profile bytes = .ok graph) : checkWith profile bytes graph = true := by
  cases proposed : proposeWith readOnly profile bytes with
  | error fault => simp [analyzeWith, proposed] at accepted
  | ok candidate =>
    cases checked : checkWith profile bytes candidate with
    | false => simp [analyzeWith, proposed, checked] at accepted
    | true =>
      have same : candidate = graph := by
        simpa [analyzeWith, proposed, checked] using accepted
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

theorem discoverWith_checked {bytes : List Byte} {graph : Graph}
    (accepted : discoverWith profile bytes = some graph) : checkWith profile bytes graph = true :=
  checkWith_complete (discoverWith_sound accepted)

theorem analyze_checked {bytes : List Byte} {graph : Graph}
    (accepted : analyze bytes = .ok graph) : check bytes graph = true := analyzeWith_checked accepted

theorem analyze_sound {bytes : List Byte} {graph : Graph}
    (accepted : analyze bytes = .ok graph) : Valid bytes graph := analyzeWith_sound accepted

theorem discover_sound {bytes : List Byte} {graph : Graph}
    (accepted : discover bytes = some graph) : Valid bytes graph := discoverWith_sound accepted

theorem discover_checked {bytes : List Byte} {graph : Graph}
    (accepted : discover bytes = some graph) : check bytes graph = true := discoverWith_checked accepted

#print axioms analyzeWith_readOnly_compat
#print axioms analyzeWith_checked
#print axioms analyzeWith_sound
#print axioms discoverWith_checked
#print axioms discoverWith_sound
#print axioms analyze_checked
#print axioms analyze_sound
#print axioms discover_checked
#print axioms discover_sound

end EDSL.X86.Sequential.CFG

#audit_edsl
