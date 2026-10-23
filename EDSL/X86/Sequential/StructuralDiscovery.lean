/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.StructuralCFG

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Structural discovery uses the production CFG proposal builder, including its
decoder, instruction lengths, complete-window scan, static caps and annotations.
It imposes no instruction-effect policy. Every successful result is separately
accepted by `Structural.checkWith` against the exact supplied byte window,
including successor closure and the depth/cutpoint conditions.

Success establishes only `Structural.Valid`: structure and decoding, with the
explicit profile. It supplies no execution, termination, resource, synchronization,
functional, or corpus result. Consumers still need authentic current executable
memory and the actual instruction-effect and environmental obligations. Failure
rejects this discovery attempt; it establishes no defect in the program.
-/

namespace EDSL.X86.Sequential.CFG.Structural

/-- Discover structure under explicitly selected static caps, without filtering
decoded effects. The independent structural checker is the final admission gate;
its failure returns `invalidGraph` with no fallback or byte/effect omission. -/
def analyzeWith (profile : Profile) (bytes : List Byte) : Except DiscoveryError Graph := do
  let graph ← CFG.proposeWith (fun _ => true) profile bytes
  if checkWith profile bytes graph then return graph else throw .invalidGraph

def discoverWith (profile : Profile) (bytes : List Byte) : Option Graph :=
  (analyzeWith profile bytes).toOption

/-- Fixed 64-byte/32-node default; larger windows need an explicit profile. -/
def analyze (bytes : List Byte) : Except DiscoveryError Graph := analyzeWith defaultProfile bytes

def discover (bytes : List Byte) : Option Graph := (analyze bytes).toOption

variable {profile : Profile}

theorem analyzeWith_checked {bytes : List Byte} {graph : Graph}
    (accepted : analyzeWith profile bytes = .ok graph) : checkWith profile bytes graph = true := by
  cases proposed : CFG.proposeWith (fun _ => true) profile bytes with
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

theorem discoverWith_checked {bytes : List Byte} {graph : Graph}
    (accepted : discoverWith profile bytes = some graph) : checkWith profile bytes graph = true := by
  cases result : analyzeWith profile bytes with
  | error fault =>
    simp only [discoverWith, result] at accepted
    cases accepted
  | ok candidate =>
    have same : candidate = graph := by
      simpa only [discoverWith, result, Except.toOption, Option.some.injEq] using accepted
    subst candidate
    exact analyzeWith_checked result

theorem discoverWith_sound {bytes : List Byte} {graph : Graph}
    (accepted : discoverWith profile bytes = some graph) : Valid bytes graph profile :=
  checkWith_sound (discoverWith_checked accepted)

theorem analyze_checked {bytes : List Byte} {graph : Graph}
    (accepted : analyze bytes = .ok graph) : check bytes graph = true := analyzeWith_checked accepted

theorem analyze_sound {bytes : List Byte} {graph : Graph}
    (accepted : analyze bytes = .ok graph) : Valid bytes graph := analyzeWith_sound accepted

theorem discover_checked {bytes : List Byte} {graph : Graph}
    (accepted : discover bytes = some graph) : check bytes graph = true := discoverWith_checked accepted

theorem discover_sound {bytes : List Byte} {graph : Graph}
    (accepted : discover bytes = some graph) : Valid bytes graph := discoverWith_sound accepted

#print axioms analyzeWith_checked
#print axioms analyzeWith_sound
#print axioms discoverWith_checked
#print axioms discoverWith_sound
#print axioms analyze_checked
#print axioms analyze_sound
#print axioms discover_checked
#print axioms discover_sound

end EDSL.X86.Sequential.CFG.Structural

#audit_edsl
