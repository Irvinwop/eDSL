/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ShortBranch
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.CFGTransport
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialJcc
open X86 X86.Sequential

private def entry (code : List Byte) (flags : Word := 0x202) : State where
  registers := fun _ => 0x1234567800000000
  rip := 4096
  flags := flags
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length
      then code[address.toNat - 4096]? else none
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length)
    writable := fun _ => false }

private def nextPC (before : State) : Option Word :=
  match Sequential.step false before with
  | .ok ⟨.next after,_⟩ => some after.rip
  | _ => none

private def takenMask (flags : Word) : Nat :=
  ((List.range 16).map fun index =>
    if nextPC (entry [BitVec.ofNat 8 (0x70 + index),0x7f] flags) = some 4225
    then 2^index else 0).sum

/-- Architectural truth-table rows with one input bit changed independently.
These exercise the real opcode decoder and selected PC, including old JE/JNZ,
and distinguish SF from SF xor OF and strict from non-strict comparisons. -/
theorem independent_condition_rows :
    ([0x202,0x203,0x206,0x242,0x282,0xa02,0xa82] : List Word).map takenMask =
      [0xaaaa,0xaa66,0xa6aa,0x6a5a,0x59aa,0x5aa9,0xa9a9] := by decide

/-- Signed displacement boundary vectors use actual byte execution. They
catch zero extension and measuring from the instruction start. -/
theorem signed_displacement_boundaries :
    ([([0x70,0x80],0xa02),([0x70,0x7f],0xa02),([0x70,0xfe],0xa02),
      ([0x70,0x80],0x202)] : List (List Byte × Word)).map
      (fun (bytes,flags) => nextPC (entry bytes flags)) =
      [some 3970,some 4225,some 4096,some 4098] := by decide

/-- Byte-level API compatibility: opcode74 remains JE and75 remains legacy
JNZ. New conditions cannot accidentally expand the old concurrent profile. -/
theorem legacy_identity :
    (Sequential.decodeAt (entry [0x74,0x80]), Sequential.decodeAt (entry [0x75,0x7f]),
      X86.decodeAt (entry [0x7c,0]), X86.decodeAt (entry [0x70,0])) =
    (.ok (.je 0x80),.ok (.legacy (.jnz 0x7f)),
      .error (.unsupportedOpcode 0x7c),.error (.unsupportedOpcode 0x70)) := by rfl

/-- Truncation fails on the actual second fetch. Near and prefixed forms
remain unsupported rather than receiving an unintended rel8 interpretation. -/
theorem unsupported_and_truncated :
    ([ [0x70], [0x7f], [0x66,0x7c,0], [0x48,0x7c,0],
      [0xf0,0x7c,0], [0x0f,0x8c,0,0,0,0] ] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error (.inaccessibleInstruction 4097),.error (.inaccessibleInstruction 4097),
      .error (.unsupportedOpcode 0x66),.error .unsupportedEncoding,
      .error .unsupportedEncoding,.error .unsupportedEncoding] := by rfl

/-- A taken destination is checked before any continuation. The identical
invalid unused target must not fault for a false condition. -/
theorem selected_target_canonicality :
    (Sequential.execute { entry [] 0xa02 with rip := 0x7ffffffffffe } (.jcc .overflow 0) false,
      (Sequential.execute { entry [] with rip := 0x7ffffffffffe } (.jcc .overflow 0) true).map
        (fun observation => match observation.result with
          | .next after => some after.rip | _ => none)) =
    (.error (.noncanonicalBranch 0x800000000000),.ok (some 0x800000000000)) := by rfl

/-- Both branch successors must remain in the supplied CFG even if a
particular initial flag row chooses only one. -/
theorem static_edges :
    (CFG.Node.successors ⟨126,.jcc .less 0x80,false,0⟩,
      CFG.Targets 4096 (.jcc .above 0x7f)) = ([128,0],[4098,4225]) := by rfl

/-- For every opcode, real CFG discovery accepts two reachable RETs and a
self-loop cutpoint, but rejects an outside target and an instruction-middle
target. Incoming flags cannot hide an omitted or malformed static edge. -/
theorem branch_closure :
    (List.range 16).all (fun index =>
      let opcode := BitVec.ofNat 8 (0x70 + index)
      (CFG.discover [opcode,1,0xc3,0xc3]).isSome &&
      !(CFG.discover [opcode,2,0xc3,0xc3]).isSome &&
      (CFG.discover [opcode,0xfe,0xc3]).isSome &&
      !(CFG.discover [opcode,0xff,0xc3]).isSome) = true := by decide

end EDSL.Tests.SequentialJcc

#audit_edsl
