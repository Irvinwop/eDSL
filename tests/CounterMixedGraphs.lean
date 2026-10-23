/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterMixedGraphs
import EDSL.X86.VCGen.MixedCFGDiscovery

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Kernel-checkable regressions over the complete frozen counter windows and
project-owned synthetic mutations. Expected boundaries come from the actual
instruction encodings, independently of the supplied certificate annotations.
These are structural admission tests, with no function or execution contract.
-/

namespace EDSL.Tests.CounterMixedGraphs
open X86 X86.VCGen.MixedCFG EDSL.Corpus.V1.CounterMixedGraphs

/-- Observe actual scanner boundaries, without equality instances for mixed
instructions or graphs. An error produces no boundaries. -/
private def discoveredOffsets (family : OS.TSO64.RMWFamily) (caps : Caps)
    (bytes : List Byte) : List Nat :=
  match analyzeWith family caps bytes with
  | .ok proposal => proposal.nodes.map (·.offset)
  | .error _ => []

private def errorOf {family : OS.TSO64.RMWFamily} :
    Except DiscoveryError (Graph family) → Option DiscoveryError
  | .ok _ => none
  | .error fault => some fault

private def exactCaps : Compiler → Caps
  | .defaultGCC => ⟨49, 17, by decide +kernel⟩
  | .defaultClang => ⟨86, 28, by decide +kernel⟩

private def shortBytes : Compiler → Caps
  | .defaultGCC => ⟨48, 32, by decide +kernel⟩
  | .defaultClang => ⟨85, 32, by decide +kernel⟩

private def shortNodes : Compiler → Caps
  | .defaultGCC => ⟨64, 16, by decide +kernel⟩
  | .defaultClang => ⟨128, 27, by decide +kernel⟩

/-- Exact independent byte/node budgets admit the actual complete graphs. -/
theorem exact_caps_checked (compiler : Compiler) :
    checkWith .arithmetic (exactCaps compiler) (bytes compiler) (graph compiler) = true := by
  cases compiler <;> decide +kernel

/-- Discovery must consume both GCC RETs, the single NOP13, and every locked
site. This inspects actual decoder output, not the hand-supplied graph fields. -/
theorem discovery_boundaries (compiler : Compiler) :
    discoveredOffsets .arithmetic (caps compiler) (bytes compiler) =
      match compiler with
      | .defaultGCC => [0,4,6,8,11,15,17,22,24,26,28,32,37,42,45,47,48]
      | .defaultClang => [0,2,4,6,8,11,13,15,16,20,22,24,26,28,30,33,35,
          48,52,56,60,64,68,72,76,80,83,85] := by
  cases compiler <;> decide +kernel

/-- Reducing each independent required cap by one rejects, both through the
checker and through the scanner's distinct byte/fuel failure boundaries. -/
theorem tightened_caps_rejected (compiler : Compiler) :
    checkWith .arithmetic (shortBytes compiler) (bytes compiler) (graph compiler) = false ∧
    checkWith .arithmetic (shortNodes compiler) (bytes compiler) (graph compiler) = false ∧
    errorOf (analyzeWith .arithmetic (shortBytes compiler) (bytes compiler)) = some .byteLimit ∧
    errorOf (analyzeWith .arithmetic (shortNodes compiler) (bytes compiler)) =
      some .instructionLimit := by
  cases compiler <;> exact ⟨by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- Generous explicit size caps cannot widen the unchanged default XADD
instruction domain to the actual ADD/INC sites at offsets 17/16. -/
theorem xadd_only_rejected (compiler : Compiler) :
    errorOf (analyzeWith .xaddOnly (caps compiler) (bytes compiler)) =
      some (.decode (match compiler with | .defaultGCC => 17 | .defaultClang => 16)
        (.machine .unsupportedEncoding)) := by
  cases compiler <;> decide +kernel

/-- The reachable second GCC RET is mandatory even after the first RET has
already decoded. Mutating only its opcode must reach the suffix decoder. -/
theorem gcc_suffix_required :
    checkWith .arithmetic (caps .defaultGCC) (bytes .defaultGCC)
      { graph .defaultGCC with nodes := (graph .defaultGCC).nodes.take 16 } = false ∧
    errorOf (analyzeWith .arithmetic (caps .defaultGCC)
      ((bytes .defaultGCC).set 48 0x62)) =
        some (.decode 48 (.machine (.unsupportedOpcode 0x62))) := by
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- JB at +33 may target the NOP13 start (+35). Targeting +36, inside that
same real instruction, must fail closure after decoding the changed branch.
Both synthetic inputs go through fresh discovery, avoiding stale annotations. -/
theorem clang_padding_targets :
    (analyzeWith .arithmetic (caps .defaultClang)
      ((bytes .defaultClang).set 34 0)).isOk = true ∧
    errorOf (analyzeWith .arithmetic (caps .defaultClang)
      ((bytes .defaultClang).set 34 1)) = some .invalidGraph := by
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- A fabricated boundary in the middle of NOP13 cannot replace its real
start, even though all bytes and the rest of the graph remain present. -/
theorem clang_padding_boundary_rejected :
    checkWith .arithmetic (caps .defaultClang) (bytes .defaultClang)
      { graph .defaultClang with nodes := (graph .defaultClang).nodes.map fun node =>
        if node.offset = 35 then { node with offset := 36 } else node } = false := by
  decide +kernel

/-- Independent literal INC bytes; the graph uses the actual arithmetic tag.
The absence of a retired successor is a closure failure, not a decoder failure. -/
private def terminalInc : List Byte := [0xf0,0x48,0xff,0x07]

private def terminalGraph : Graph .arithmetic := ⟨[⟨0, incOne, true, 2⟩], 2⟩

private def incRetGraph : Graph .arithmetic :=
  ⟨[⟨0, incOne, true, 2⟩, ⟨4, .ordinary (.legacy .ret), false, 1⟩], 2⟩

/-- An exact terminal INC has an out-of-window successor. Appending RET
closes it and must admit under the same explicit arithmetic family/caps. -/
theorem terminal_inc_closure :
    checkWith .arithmetic ⟨5, 2, by decide +kernel⟩ terminalInc terminalGraph = false ∧
    errorOf (analyzeWith .arithmetic ⟨5, 2, by decide +kernel⟩ terminalInc) =
      some .invalidGraph ∧
    checkWith .arithmetic ⟨5, 2, by decide +kernel⟩ (terminalInc ++ [0xc3]) incRetGraph = true ∧
    discoveredOffsets .arithmetic ⟨5, 2, by decide +kernel⟩ (terminalInc ++ [0xc3]) = [0,4] := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms exact_caps_checked
#print axioms discovery_boundaries
#print axioms tightened_caps_rejected
#print axioms xadd_only_rejected
#print axioms gcc_suffix_required
#print axioms clang_padding_targets
#print axioms clang_padding_boundary_rejected
#print axioms terminal_inc_closure
end EDSL.Tests.CounterMixedGraphs
#audit_edsl
