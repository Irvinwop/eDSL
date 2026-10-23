/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Audit
import EDSL.X86.VCGen.MixedCFG

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Bounded proposals for complete byte windows decoded by the actual TSO64 decoder.
The caller selects the RMW family and static caps explicitly. Discovery retains
every decoded instruction, including instructions after RET, and uses the exact
tagged instruction lengths supplied by the mixed structural Core.

The final independent checker authenticates the proposed partition, successor
closure, cutpoints, and depths against those same bytes, family, and caps.
Success supplies only structural validity. It establishes no execution, resource,
synchronization, count, ABI, progress, or corpus result. Failure rejects the
proposal and does not establish a defect in the selected program.
-/

namespace EDSL.X86.VCGen.MixedCFG
open OS OS.TSO64

inductive DiscoveryError where
  | empty
  | byteLimit
  | instructionLimit
  | decode (offset : Nat) (fault : OS.TSO64.Fault)
  | truncated (offset : Nat)
  | invalidGraph
  deriving DecidableEq, Repr

/-- Scan the entire exact window, including instructions after RET. Core proves
that every tagged instruction length is positive. The node fuel bounds only
this finite scan, and an exact window end succeeds even when fuel is exhausted.
Every decoder failure retains its original offset and fault. -/
private def decodeNodes (family : RMWFamily) (bytes : List Byte) :
    Nat → Nat → Except DiscoveryError (List (Node family))
  | remaining, offset => do
    if offset = bytes.length then return []
    if offset > bytes.length then throw (.truncated offset)
    match remaining with
    | 0 => throw .instructionLimit
    | fuel + 1 =>
      let instruction ←
        (OS.TSO64.decode (Sequential.codeState bytes offset) family).mapError (.decode offset)
      let finish := offset + instructionLength instruction
      if finish > bytes.length then throw (.truncated offset)
      let rest ← decodeNodes family bytes fuel finish
      return ⟨offset, instruction, false, 0⟩ :: rest

/-- Propose entry and nonforward-edge targets as cutpoints. Interior depths use
the complete node count minus the linear index. These annotations carry no
semantic trust and are independently checked before admission. -/
private def annotate {family : RMWFamily} (nodes : List (Node family)) : Graph family :=
  let targets := nodes.flatMap fun node =>
    node.successors.filterMap fun target =>
      if target.toNat ≤ node.offset then some target.toNat else none
  ⟨nodes.mapIdx (fun index node => { node with
    cutpoint := decide (node.offset = 0) || targets.contains node.offset
    depth := nodes.length - index }), nodes.length⟩

/-- Empty input precedes the byte-cap check. Exactly the caller's node cap is
used as scan fuel; zero caps are not replaced by a default. This builder only
proposes certificate data for the independent checker. -/
private def proposeWith (family : RMWFamily) (caps : Caps) (bytes : List Byte) :
    Except DiscoveryError (Graph family) :=
  if bytes.isEmpty then .error .empty
  else if bytes.length > caps.maxBytes then .error .byteLimit
  else do
    let nodes ← decodeNodes family bytes caps.maxNodes 0
    return annotate nodes

/-- Discover with explicit family and caps, then independently check the exact
whole-window graph. A rejected certificate returns `invalidGraph`. -/
def analyzeWith (family : RMWFamily) (caps : Caps) (bytes : List Byte) :
    Except DiscoveryError (Graph family) := do
  let graph ← proposeWith family caps bytes
  if checkWith family caps bytes graph then return graph else throw .invalidGraph

/-- Accepted discovery results pass the independent mixed structural checker
under the exact family, caps, and byte window supplied by the caller. -/
theorem analyzeWith_checked {family : RMWFamily} {caps : Caps}
    {bytes : List Byte} {graph : Graph family}
    (accepted : analyzeWith family caps bytes = .ok graph) :
    checkWith family caps bytes graph = true := by
  cases proposed : proposeWith family caps bytes with
  | error fault => simp [analyzeWith, proposed] at accepted
  | ok candidate =>
    cases checked : checkWith family caps bytes candidate with
    | false => simp [analyzeWith, proposed, checked] at accepted
    | true =>
      have same : candidate = graph := by
        simpa [analyzeWith, proposed, checked] using accepted
      simpa only [same] using checked

/-- Structural validity follows from the checker theorem, independently of
the scanner and annotation heuristic. Runtime obligations remain separate. -/
theorem analyzeWith_sound {family : RMWFamily} {caps : Caps}
    {bytes : List Byte} {graph : Graph family}
    (accepted : analyzeWith family caps bytes = .ok graph) :
    Valid family caps bytes graph :=
  checkWith_sound (analyzeWith_checked accepted)

#print axioms analyzeWith_checked
#print axioms analyzeWith_sound

end EDSL.X86.VCGen.MixedCFG

#audit_edsl
