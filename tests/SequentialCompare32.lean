/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.ConditionFlags
import EDSL.Audit

namespace EDSL.Tests.SequentialCompare32
open X86 X86.Sequential

private def entry (bytes : List Byte) (left right : Word) : State where
  registers := fun register => if register = .rdi then left else
    if register = .rsi then right else 0xfedcba9876543210
  rip := 4096
  flags := 0xffffffffffffffff
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length
      then bytes[address.toNat - 4096]? else none
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)
    writable := fun _ => false }

private def conditions (bytes : List Byte) (left right : Word) : Except Error (List Bool) := do
  let observation ← Sequential.step false (entry bytes left right)
  match observation.result with
  | .next final =>
    return ([.below, .equal, .less, .greater, .overflow, .parity] : List Condition).map
      (fun condition => condition.holds final.flags)
  | _ => throw .unexpectedReturn

/-- Literal mathematical order/overflow/parity vectors. High halves differ
from the low32 signed order, so using a 64-bit subtract fails these cases. -/
theorem cmp_boundary_conditions :
    ([ (0x0000000000000000, 0xffffffff00000001),
       (0xffffffff80000000, 0x0000000000000001),
       (0x000000007fffffff, 0xffffffff80000000),
       (0x1111111100000003, 0x2222222200000003) ] : List (Word × Word)).map
      (fun (left, right) => conditions [0x39, 0xf7] left right) =
    [.ok [true, false, true, false, false, true],
     .ok [false, false, true, false, true, true],
     .ok [true, false, false, true, true, true],
     .ok [false, true, false, false, false, true]] := by rfl

/-- The direction bit changes the subtraction; ignoring it reverses both
unsigned and signed order on these non-equal operands. -/
theorem cmp_opcode_direction :
    (conditions [0x39, 0xf7] 1 2, conditions [0x3b, 0xfe] 1 2,
      conditions [0x3b, 0xf7] 1 2) =
    (.ok [true, false, true, false, false, true],
     .ok [true, false, true, false, false, true],
     .ok [false, false, false, true, false, false]) := by rfl

/-- Literal ModRM/REX operands distinguish R from B and retain X as ignored.
The last entries include RSP/RBP and high register aliases. -/
theorem register_banks :
    ([ [0x39,0xd8], [0x40,0x39,0xd8], [0x41,0x39,0xd8], [0x42,0x39,0xd8],
       [0x43,0x39,0xd8], [0x44,0x39,0xd8], [0x45,0x39,0xd8],
       [0x46,0x39,0xd8], [0x47,0x39,0xd8], [0x47,0x3b,0xd8],
       [0x85,0xec], [0x45,0x85,0xff] ] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes 0 0)) =
    [.ok (.cmp32 .rax .rbx false), .ok (.cmp32 .rax .rbx true),
     .ok (.cmp32 .r8 .rbx true), .ok (.cmp32 .rax .rbx true),
     .ok (.cmp32 .r8 .rbx true), .ok (.cmp32 .rax .r11 true),
     .ok (.cmp32 .r8 .r11 true), .ok (.cmp32 .rax .r11 true),
     .ok (.cmp32 .r8 .r11 true), .ok (.cmp32 .r11 .r8 true),
     .ok (.test32 .rsp .rbp false), .ok (.test32 .r15 .r15 true)] := by rfl

/-- A 64-bit AND would be nonzero here. AF is unconstrained at BOTH choices;
all GPRs and nonarithmetic flag bits survive the actual decoded step. -/
theorem test32_low_half_and_frame (af : Bool) :
    let initial := entry [0x85,0xf7] 0x8000000000000000 0xffffffffffffffff
    (Sequential.step af initial).map (fun observation => match observation.result with
      | .next final => some (final.registers .rdi, final.registers .rsi, final.registers .rsp,
          final.rip, final.flags.getLsbD 0, final.flags.getLsbD 2, final.flags.getLsbD 4,
          final.flags.getLsbD 6, final.flags.getLsbD 7, final.flags.getLsbD 11,
          final.flags &&& ~~~arithmeticFlagMask, observation.reads)
      | _ => none) =
    .ok (some (0x8000000000000000, 0xffffffffffffffff, 0xfedcba9876543210,
      4098, false, true, af, true, false, false, 0xfffffffffffff72a, [])) := by
  cases af <;> rfl

/-- Unsupported byte/word/immediate and memory addressing/direction forms,
including mod=01 displacement, and repeated prefixes are rejected.
REX.W retains its previous TEST64/CMP64 interpretation. -/
theorem reject_other_forms :
    ([ [0x39,0x40,0x00], [0x3b,0x06], [0x85,0x3f], [0x41,0x85,0x07],
       [0x40,0x40,0x85,0xff], [0x66,0x85,0xff], [0xf0,0x39,0xf7],
       [0x38,0xf7], [0x3d,0,0,0,0] ] : List (List Byte)).all
      (fun bytes => !(Sequential.decodeAt (entry bytes 0 0)).isOk) = true := by decide

theorem truncated_fetches :
    ([ [0x39], [0x3b], [0x85], [0x47], [0x47,0x85] ] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes 0 0)) =
    [.error (.inaccessibleInstruction 4097), .error (.inaccessibleInstruction 4097),
     .error (.inaccessibleInstruction 4097), .error (.inaccessibleInstruction 4097),
     .error (.inaccessibleInstruction 4098)] := by rfl

theorem old_profile_and_full_width_unchanged :
    (X86.decodeAt (entry [0x39,0xf7] 0 0),
      Sequential.decodeAt (entry [0x48,0x39,0xf7] 0 0),
      Sequential.decodeAt (entry [0x48,0x85,0xf7] 0 0)) =
    (.error (.unsupportedOpcode 0x39), .ok (.cmp64 .rdi .rsi),
      .ok (.test64 .rdi .rsi)) := by rfl

/-- The production CFG validates a whole partition including both static
branch edges. A target into CMP's operand byte is still rejected. -/
theorem cfg_composition :
    ((CFG.discover [0xf3,0x0f,0x1e,0xfa,0x85,0xff,0x7e,2,0x39,0xf7,0xc3]).isSome,
      (CFG.discover [0x85,0xff,0x7e,1,0x39,0xf7,0xc3]).isSome) = (true, false) := by decide

end EDSL.Tests.SequentialCompare32

#audit_edsl
