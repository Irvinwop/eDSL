/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine
import EDSL.Audit

namespace EDSL.Tests.SequentialISA
open X86

def entry (code : List Byte) (registers : Register → Word := fun _ => 0)
    (flags : Word := 0x602) (data : Word → Option Byte := fun _ => none) : State where
  registers := registers
  flags := flags
  rip := 4096
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length
      then code[address.toNat - 4096]? else data address
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length)
    writable := fun _ => false }

def nextView (af : Bool) (state : State) (view : State → List X86.Sequential.Read → α) : Except Error α := do
  let observation ← X86.Sequential.step af state
  match observation.result with
  | .next final => return view final observation.reads
  | _ => throw .unexpectedReturn

/-- AF is independently available at both values; EAX zeroes all of RAX,
while IF/DF and the abstract reserved bit survive. -/
example : nextView false (entry [0x31, 0xc0] (fun _ => 0xffffffffffffffff))
    (fun s reads => (s.registers .rax, s.registers .rcx, s.rip, s.flags, reads)) =
    .ok (0, 0xffffffffffffffff, 4098, 0x646, []) := by rfl
example : nextView true (entry [0x31, 0xc9] (fun _ => 0xffffffffffffffff))
    (fun s reads => (s.registers .rcx, s.registers .rax, s.rip, s.flags, reads)) =
    .ok (0, 0xffffffffffffffff, 4098, 0x656, []) := by rfl

/-- The high sign bit makes a 32-bit implementation get both SF and ZF wrong.
TEST also preserves both operand registers, including their high halves. -/
example (af : Bool) : nextView af
    (entry [0x48, 0x85, 0xfe] (fun r => if r = .rsi then 0x8000000000000000 else 0xffffffffffffffff))
    (fun s _ => (s.registers .rsi, s.registers .rdi, s.rip,
      s.flags.getLsbD 0, s.flags.getLsbD 2, s.flags.getLsbD 4,
      s.flags.getLsbD 6, s.flags.getLsbD 7, s.flags.getLsbD 11)) =
    .ok (0x8000000000000000, 0xffffffffffffffff, 4099, false, true, af, false, true, false) := by
  cases af <;> rfl

/-- Direction is RSI minus RCX, and subtraction uses all 64 bits. -/
example : nextView false
    (entry [0x48, 0x39, 0xce] (fun r => if r = .rcx then 1 else 0))
    (fun s _ => (s.registers .rsi, s.registers .rcx, s.flags, s.rip)) =
    .ok (0, 1, 0x697, 4099) := by rfl
example : nextView true
    (entry [0x48, 0x39, 0xce] (fun r => if r = .rsi then 0x8000000000000000 else 1))
    (fun s _ => s.flags) = .ok 0xe16 := by rfl

/-- Sign extension of FF is minus one, not plus 255. -/
example : nextView false (entry [0x48, 0x83, 0xc7, 0xff])
    (fun s _ => (s.registers .rdi, s.flags, s.rip)) =
    .ok (0xffffffffffffffff, 0x686, 4100) := by rfl
example : nextView true
    (entry [0x48, 0x83, 0xc3, 1] (fun _ => 0xffffffffffffffff))
    (fun s _ => (s.registers .rbx, s.flags)) = .ok (0, 0x657) := by rfl
example : nextView false
    (entry [0x48, 0x83, 0xc2, 1] (fun _ => 0x7fffffffffffffff))
    (fun s _ => (s.registers .rdx, s.flags)) = .ok (0x8000000000000000, 0xe96) := by rfl

/-- INC/DEC update signed overflow but preserve CF at both values, even on
unsigned wrap/borrow. These are independent arithmetic boundary vectors. -/
example : nextView false
    (entry [0x48, 0xff, 0xc1] (fun _ => 0x7fffffffffffffff) 0x603)
    (fun s _ => (s.registers .rcx, s.flags, s.rip)) =
    .ok (0x8000000000000000, 0xe97, 4099) := by rfl
example : nextView true
    (entry [0x48, 0xff, 0xce] (fun _ => 0x8000000000000000) 0x603)
    (fun s _ => (s.registers .rsi, s.flags)) = .ok (0x7fffffffffffffff, 0xe17) := by rfl
example : nextView true
    (entry [0x48, 0xff, 0xc0] (fun _ => 0xffffffffffffffff))
    (fun s _ => (s.registers .rax, s.flags)) = .ok (0, 0x656) := by rfl
example : nextView false (entry [0x48, 0xff, 0xc8])
    (fun s _ => (s.registers .rax, s.flags)) = .ok (0xffffffffffffffff, 0x696) := by rfl

/-- Little-endian four-byte input, low-width addition and full destination
zero extension; successful input bytes have neither write nor execute permission. -/
def addInput (address : Word) : Option Byte :=
  if address = 8192 then some 3
  else if address = 8193 ∨ address = 8194 ∨ address = 8195 then some 0 else none
example : nextView false
    (entry [3, 7] (fun r => if r = .rdi then 8192 else 0xfffffffffffffffe) 0x602 addInput)
    (fun s reads => (s.registers .rax, s.flags, s.rip, reads)) =
    .ok (1, 0x613, 4098, [⟨.data, 8192, 4⟩]) := by rfl

/-- A scale of four uses BOTH full 64-bit base/index values; only the resulting
high address is mapped, so truncation or an incorrect scale would fault. -/
def indexedInput (address : Word) : Option Byte :=
  if address = 0x600000004 then some 9
  else if address = 0x600000005 ∨ address = 0x600000006 ∨ address = 0x600000007 then some 0 else none
example : nextView true
    (entry [3, 4, 0x8f] (fun r =>
      if r = .rdi then 0x200000000 else if r = .rcx then 0x100000001 else 2) 0x602 indexedInput)
    (fun s reads => (s.registers .rax, s.rip, s.flags, reads)) =
    .ok (11, 4099, 0x602, [⟨.data, 0x600000004, 4⟩]) := by rfl

/-- Missing final byte faults there, after the first three readable bytes.
A permission query or successful decoder cannot replace the actual operand load. -/
example : nextView false
    (entry [3, 7] (fun _ => 8192) 0x602
      (fun a => if a = 8192 ∨ a = 8193 ∨ a = 8194 then some 0 else none))
    (fun s _ => s.registers .rax) = .error (.inaccessibleData 8195) := by rfl

/-- rel8 is signed and measured from the next instruction; branches keep all flags. -/
example : nextView false (entry [0x74, 0xfe] (flags := 0x642))
    (fun s reads => (s.rip, s.flags, reads)) = .ok (4096, 0x642, []) := by rfl
example : nextView true (entry [0x74, 0x7f])
    (fun s _ => (s.rip, s.flags)) = .ok (4098, 0x602) := by rfl
example : nextView true (entry [0xeb, 0xf0])
    (fun s _ => (s.rip, s.flags)) = .ok (4082, 0x602) := by rfl
example : X86.Sequential.execute { entry [] with rip := 0x7ffffffffffe } (.jmp 0) false =
    .error (.noncanonicalBranch 0x800000000000) := by rfl
example : X86.Sequential.execute { entry [] (flags := 0x642) with rip := 0x7ffffffffffe } (.je 0) true =
    .error (.noncanonicalBranch 0x800000000000) := by rfl

/-- Non-self XOR32 uses the shared logical instruction and correct operand order. -/
example : X86.Sequential.decodeAt (entry [0x31, 0xc1]) =
    .ok (.logicalReg32 .bxor .rcx .rax false) := by rfl

/-- Deliberate decoding boundary: wrong register mode,
address/operand overrides, extended REX, displacements, missing-index/base SIB. -/
example : X86.Sequential.decodeAt (entry [0x48, 0x85, 0x36]) = .error .unsupportedEncoding := by rfl
example : X86.Sequential.decodeAt (entry [3, 0x47, 0xfc]) = .error .unsupportedEncoding := by rfl
example : X86.Sequential.decodeAt (entry [3, 4, 0x27]) = .error .unsupportedEncoding := by rfl
example : X86.Sequential.decodeAt (entry [3, 4, 0x0d]) = .error .unsupportedEncoding := by rfl
example : X86.Sequential.decodeAt (entry [0x67, 3, 7]) = .error (.unsupportedOpcode 0x67) := by rfl
example : X86.Sequential.decodeAt (entry [0x66, 0x31, 0xc0]) = .error .unsupportedEncoding := by rfl
example : X86.Sequential.decodeAt (entry [0x49, 0x85, 0xf6]) = .error .unsupportedEncoding := by rfl
example : X86.Sequential.decodeAt (entry [0x48, 0xff]) = .error (.inaccessibleInstruction 4098) := by rfl

/-- All nine added families remain rejected by the old profile used by TSO.
This tests the admission boundary directly, without altering any old decoder. -/
example : ([ [0x31, 0xc0], [0x48, 0x85, 0xf6], [0x48, 0x39, 0xce], [3, 7],
    [0x48, 0x83, 0xc7, 4], [0x48, 0xff, 0xc1], [0x48, 0xff, 0xce], [0x74, 0], [0xeb, 0] ]
    : List (List Byte)).all (fun bytes => (match X86.decodeAt (entry bytes) with | .error _ => true | .ok _ => false)) = true := by rfl

/-- The final legacy RET needs only its one executable byte. It retains its
actual stack read and full incoming flags at both AF choices. -/
def stackInput (address : Word) : Option Byte :=
  if address = 32768 then some 0x34 else if address = 32769 then some 0x12
  else if 32770 ≤ address.toNat ∧ address.toNat < 32776 then some 0 else none
example : X86.Sequential.decodeAt (entry [0xc3]) = .ok (.legacy .ret) := by rfl
example (af : Bool) :
    (X86.Sequential.step af (entry [0xc3] (fun _ => 32768) 0xabcdef stackInput)).map
      (fun observation => match observation.result with
        | .returned s => some (s.rip, s.registers .rsp, s.flags, observation.reads)
        | _ => none) =
    .ok (some (0x1234, 32776, 0xabcdef, [⟨.stack, 32768, 8⟩])) := by
  cases af <;> rfl

/-- Other low-register destinations, bases and SIB scales are decoded as
operands rather than recognized as a complete client byte string. -/
example : nextView false
    (entry [3, 0x14, 0x4b] (fun r =>
      if r = .rbx then 8186 else if r = .rcx then 3
      else if r = .rdx then 0xfffffffffffffffe else 0x55) 0x602 addInput)
    (fun s reads => (s.registers .rdx, s.registers .rax, s.rip, s.flags, reads)) =
    .ok (1, 0x55, 4099, 0x613, [⟨.data, 8192, 4⟩]) := by rfl
example : X86.Sequential.decodeAt (entry [3, 0x1c, 0x1a]) =
    .ok (.addMem32 .rbx (.indexed .rdx .rbx 0)) := by rfl
example : X86.Sequential.decodeAt (entry [3, 0x14, 0xcf]) =
    .ok (.addMem32 .rdx (.indexed .rdi .rcx 3)) := by rfl
example : X86.Sequential.decodeAt (entry [0x31, 0xff]) = .ok (.xorSelf32 .rdi) := by rfl
example : X86.Sequential.decodeAt (entry [0x48, 0xff, 0xc3]) = .ok (.inc64 .rbx) := by rfl

/-- A mapped byte value alone does not grant permission to fetch instructions. -/
example : X86.Sequential.step false { entry [0x31, 0xc0] with
      memory := { (entry [0x31, 0xc0]).memory with executable := fun _ => false } } =
    .error (.inaccessibleInstruction 4096) := by rfl
example : nextView false
    (entry [3, 7] (fun _ => 0x7ffffffffffe) 0x602 (fun _ => some 0))
    (fun s _ => s.registers .rax) = .error (.inaccessibleData 0x800000000000) := by rfl
example : nextView false
    (entry [3, 7] (fun _ => 0xffffffffffffffff) 0x602 (fun _ => some 0))
    (fun s _ => s.registers .rax) = .error (.inaccessibleData 0xffffffffffffffff) := by rfl

/-- A finite one-byte candidate can be moved to ANY CodeAt memory/base,
without padding or assuming permissions beyond that one-byte function. -/
example (destination : State) (code : CodeAt destination.memory destination.rip [0xc3]) :
    X86.Sequential.decodeAt destination = .ok (.legacy .ret) := by
  apply X86.Sequential.decodeAt_transport (source := entry [0xc3]) ?_ (by rfl)
  intro offset bound byte fetched
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 ∨
      offset = 5 ∨ offset = 6 ∨ offset = 7 ∨ offset = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Except.ok (0xc3 : Byte) = .ok byte at fetched
    cases fetched
    simpa only [BitVec.add_zero] using code.2 0 0xc3 (by rfl)
  · cases fetched
  · cases fetched
  · cases fetched
  · cases fetched
  · cases fetched
  · cases fetched
  · cases fetched
  · cases fetched

end EDSL.Tests.SequentialISA

#audit_edsl
