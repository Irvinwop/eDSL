/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.Code

namespace EDSL.Sum32
open X86

inductive CheckFault where
  | byteLimit | instructionLimit
  | decode (offset : Nat) (error : X86.Error)
  | truncated (offset : Nat)
  | unsupportedLayout | invalidLayout
  deriving DecidableEq, Repr

/-- Decode a complete finite candidate, with explicit admission limits.
The limits concern static code size, never the symbolic input count. -/
def decodeNodesAux (bytes : List Byte) : Nat → Nat → Except CheckFault (List Node)
  | fuel, offset =>
    if offset = bytes.length then .ok []
    else match fuel with
    | 0 => .error .instructionLimit
    | fuel + 1 => do
      let instruction ← (Sequential.decodeAt (codeState bytes offset)).mapError (fun fault => .decode offset fault)
      if offset + instruction.length > bytes.length then throw (.truncated offset)
      let tail ← decodeNodesAux bytes fuel (offset + instruction.length)
      return ⟨offset, instruction⟩ :: tail

def decodeNodes (bytes : List Byte) : Except CheckFault (List Node) :=
  if bytes.length > 64 then .error .byteLimit else decodeNodesAux bytes 32 0

def splitPrologue : List Node → List Node × List Node
  | [] => ([], [])
  | node :: rest =>
    if allowedClear node.instruction then
      let (prefixNodes, suffix) := splitPrologue rest
      (node :: prefixNodes, suffix)
    else ([], node :: rest)

/-- Infer certificate data from the decoded graph. All inferred facts are
rechecked by `checkPlan`; discovery itself carries no semantic trust. -/
def discover (nodes : List Node) : Option Plan := do
  let (prologue, tail) := splitPrologue nodes
  let guard :: branch :: load :: rest := tail | none
  let mode ← if guard.instruction = Mode.pointerCount.guard then some Mode.pointerCount
    else if guard.instruction = Mode.index.guard then some Mode.index else none
  let exit :: back :: reverseUpdates := rest.reverse | none
  let .je forward := branch.instruction | none
  let .jmp backward := back.instruction | none
  return ⟨mode, prologue, guard.offset, ⟨branch.offset, forward⟩, load.offset,
    reverseUpdates.reverse, ⟨back.offset, backward⟩, exit.offset⟩

def analyze (bytes : List Byte) : Except CheckFault Plan := do
  let nodes ← decodeNodes bytes
  let some plan := discover nodes | throw .unsupportedLayout
  if checkPlan bytes plan then return plan else throw .invalidLayout

def check (bytes : List Byte) : Option Plan := (analyze bytes).toOption

theorem analyze_sound {bytes : List Byte} {plan : Plan}
    (accepted : analyze bytes = .ok plan) : Valid bytes plan := by
  cases decoded : decodeNodes bytes with
  | error fault => simp [analyze, decoded] at accepted
  | ok nodes =>
    cases discovered : discover nodes with
    | none => simp [analyze, decoded, discovered] at accepted
    | some proposed =>
      cases checked : checkPlan bytes proposed with
      | false => simp [analyze, decoded, discovered, checked] at accepted
      | true =>
        simp [analyze, decoded, discovered, checked] at accepted
        subst plan
        exact checkPlan_sound checked

theorem check_sound {bytes : List Byte} {plan : Plan}
    (accepted : check bytes = some plan) : Valid bytes plan := by
  cases analyzed : analyze bytes with
  | error fault =>
    simp only [check, analyzed] at accepted
    cases accepted
  | ok actual =>
    simp only [check, analyzed] at accepted
    have same : actual = plan := Option.some.inj accepted
    subst actual
    exact analyze_sound analyzed

end EDSL.Sum32
