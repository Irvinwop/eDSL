/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.Audit

namespace EDSL.Tests.SequentialPadding
open X86 X86.Sequential

private def entry (bytes : List Byte) : State where
  registers := fun _ => 0x8000000000000001
  rip := 4096
  flags := 0xffffffffffffffff
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length
      then bytes[address.toNat - 4096]? else none
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)
    writable := fun _ => false }

/-- Exact short windows succeed without fetching bytes beyond the instruction.
Noncanonical apparent NOP operands cannot cause a data-access failure. -/
theorem exact_lengths_and_no_data_read (af : Bool) :
    ([ [0x90], [0x66,0x90], [0x0f,0x1f,0], [0x0f,0x1f,0x40,0],
       [0x0f,0x1f,0x44,0,0], [0xf3,0x0f,0x1e,0xfa] ] : List (List Byte)).map
      (fun bytes => (Sequential.step af (entry bytes)).map (fun observation =>
        match observation.result with
        | .next final => some (final.rip, final.registers .rax, final.flags, observation.reads)
        | _ => none)) =
    [.ok (some (4097,0x8000000000000001,0xffffffffffffffff,[])),
     .ok (some (4098,0x8000000000000001,0xffffffffffffffff,[])),
     .ok (some (4099,0x8000000000000001,0xffffffffffffffff,[])),
     .ok (some (4100,0x8000000000000001,0xffffffffffffffff,[])),
     .ok (some (4101,0x8000000000000001,0xffffffffffffffff,[])),
     .ok (some (4100,0x8000000000000001,0xffffffffffffffff,[]))] := by rfl

/-- ENDBR32, extra prefixes, reserved hints and valid hardware NOP aliases
outside the exact supported list must not be admitted as no-ops. -/
theorem reject_aliases :
    ([ [0xf3,0x0f,0x1e,0xfb], [0x0f,0x1e,0xfa], [0xf2,0x0f,0x1e,0xfa],
       [0xf3,0xf3,0x0f,0x1e,0xfa], [0x66,0xf3,0x0f,0x1e,0xfa],
       [0x48,0xf3,0x0f,0x1e,0xfa], [0xf0,0xf3,0x0f,0x1e,0xfa],
       [0x41,0x90], [0xf3,0x90], [0x66,0x66,0x90],
       [0x0f,0x1f,1], [0x0f,0x1f,0xc0], [0x0f,0x1f,8],
       [0x0f,0x1f,0x40,1], [0x0f,0x1f,0x44,1,0],
       [0x66,0x0f,0x1f,0x44,0,0], [0x0f,0x1f,0x80,0,0,0,0] ] : List (List Byte)).all
      (fun bytes => !(Sequential.decodeAt (entry bytes)).isOk) = true := by decide

/-- Every encoded byte is fetched: not just prefixes, opcode and ModRM, but
also the last SIB/displacement byte, even though there is no data read. -/
theorem truncation_faults :
    ([ [0x66], [0xf3], [0xf3,0x0f], [0xf3,0x0f,0x1e],
       [0x0f], [0x0f,0x1f], [0x0f,0x1f,0x40],
       [0x0f,0x1f,0x44], [0x0f,0x1f,0x44,0] ] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error (.inaccessibleInstruction 4097), .error (.inaccessibleInstruction 4097),
     .error (.inaccessibleInstruction 4098), .error (.inaccessibleInstruction 4099),
     .error (.inaccessibleInstruction 4097), .error (.inaccessibleInstruction 4098),
     .error (.inaccessibleInstruction 4099), .error (.inaccessibleInstruction 4099),
     .error (.inaccessibleInstruction 4100)] := by rfl

theorem final_byte_requires_execute_permission :
    let initial := entry [0x0f,0x1f,0x44,0,0]
    Sequential.decodeAt { initial with memory := { initial.memory with
      executable := fun address => address != 4100 } } =
      .error (.inaccessibleInstruction 4100) := by rfl

theorem nop_is_not_rex_xchg :
    (Sequential.decodeAt (entry [0x49,0x90]),
      X86.decodeAt (entry [0xf3,0x0f,0x1e,0xfa])) =
    (.ok (.xchgRax64 .r8), .error (.unsupportedOpcode 0xf3)) := by rfl

/-- Whole-window CFG checking accepts padding and rejects an edge into a
padding operand. Admitting ENDBR is not by itself a function certificate. -/
theorem cfg_whole_window :
    ((CFG.discover [0xf3,0x0f,0x1e,0xfa,0x66,0x90,0x0f,0x1f,0x44,0,0,0xc3]).isSome,
      (CFG.discover [0xeb,1,0x0f,0x1f,0x44,0,0,0xc3]).isSome) = (true,false) := by decide

end EDSL.Tests.SequentialPadding

#audit_edsl
