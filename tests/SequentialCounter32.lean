/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Counter32
import EDSL.X86.Sequential.Code

set_option autoImplicit false
set_option warningAsError true

open EDSL.X86 EDSL.X86.Sequential

private def input (bytes : List Byte) (destination : Register) (value flags : Word) : State :=
  { codeState bytes 0 with
    registers := fun r => if r = destination then value else 0x123456789abcdef0
    flags := flags }

private def observed (bytes : List Byte) (destination : Register) (value flags : Word) :
    Except Error (Word × Word × Word × List Read) := do
  let outcome ← step false (input bytes destination value flags)
  match outcome.result with
  | .next final => return (final.registers destination, final.flags, final.rip, outcome.reads)
  | _ => throw .unexpectedReturn

-- Wrap distinguishes width32 from full64 and ADD's carry from INC's old carry.
example : observed [0x83,0xc0,1] .rax 0xabcdefffffffffff 0 = .ok (0,0x55,3,[]) := by rfl
example : observed [0xff,0xc0] .rax 0xabcdefffffffffff 0 = .ok (0,0x54,2,[]) := by rfl
example : observed [0xff,0xc0] .rax 0xabcdefffffffffff 1 = .ok (0,0x55,2,[]) := by rfl

-- Signed imm8 endpoints and defined overflow/auxiliary/parity effects.
example : observed [0x83,0xc0,0xff] .rax 0x80000000 0 = .ok (0x7fffffff,0x805,3,[]) := by rfl
example : observed [0x83,0xc0,0x80] .rax 128 0 = .ok (0,0x45,3,[]) := by rfl
example : observed [0x83,0xc0,0x80] .rax 0 0 = .ok (0xffffff80,0x80,3,[]) := by rfl
example : observed [0x83,0xc0,0x7f] .rax 1 0 = .ok (128,0x10,3,[]) := by rfl
example : observed [0x83,0xc0,0] .rax 0xdeadbeef00000000 0x203 = .ok (0,0x246,3,[]) := by rfl
example : observed [0xff,0xc0] .rax 0xffff00007fffffff 1 = .ok (0x80000000,0x895,2,[]) := by rfl

-- REX.B and preserved nonarithmetic bits, including a noncanonical upper half.
example : observed [0x41,0xff,0xc7] .r15 0xffffffffffffffff 0x203 =
    .ok (0,0x257,3,[]) := by rfl
example : observed [0x41,0x83,0xc4,1] .r12 0x123400000000000f 0x202 =
    .ok (16,0x212,4,[]) := by rfl

-- Unsupported width/group/memory/prefix forms must not become counter updates.
example : Sequential.decodeAt (codeState [0x83,0x00,1] 0) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (codeState [0x83,0xd0,1] 0) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (codeState [0xff,0xc8] 0) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (codeState [0x42,0xff,0xc0] 0) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (codeState [0x44,0x83,0xc0,1] 0) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (codeState [0x40,0x40,0xff,0xc0] 0) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (codeState [0x83,0xc0] 0) = .error (.inaccessibleInstruction 2) := by rfl
example : Sequential.decodeAt (codeState [0x41,0x83,0xc0] 0) = .error (.inaccessibleInstruction 3) := by rfl

-- Legacy CMP83 and W=1 operations preserve their original interpretation.
example : Sequential.decodeAt (codeState [0x83,0xf8,0] 0) = .ok (.legacy .cmpEaxZero) := by rfl
example : Sequential.decodeAt (codeState [0x48,0xff,0xc0] 0) = .ok (.inc64 .rax) := by rfl
example : Sequential.decodeAt (codeState [0x48,0x83,0xc0,1] 0) = .ok (.addImm64 .rax 1) := by rfl

-- The Nat counter adapter admits arbitrary high32 input bits.
example (value : Word) (count : Nat) (matching : (value.setWidth 32).toNat = count)
    (small : count ≤ 64) :
    (((value.setWidth 32 + 1).setWidth 64).toNat) = count + 1 :=
  counter32_increment_nat value count matching (by omega)
