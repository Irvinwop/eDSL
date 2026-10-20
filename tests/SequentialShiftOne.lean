/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ShiftOne
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.Return
import EDSL.X86.Sequential.Literals
import EDSL.X86.CallReturn.DecodeTransport
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SequentialShiftOne
open X86 X86.Sequential

private def allRegisters : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

private def canary : Register → Word
  | .rax => 0x8000000100000001 | .rcx => 0x8000000100000002
  | .rdx => 0x8000000100000003 | .rbx => 0x8000000100000004
  | .rsp => 0x8000000100000005 | .rbp => 0x8000000100000006
  | .rsi => 0x8000000100000007 | .rdi => 0x8000000100000008
  | .r8 => 0x8000000100000009 | .r9 => 0x800000010000000a
  | .r10 => 0x800000010000000b | .r11 => 0x800000010000000c
  | .r12 => 0x800000010000000d | .r13 => 0x800000010000000e
  | .r14 => 0x800000010000000f | .r15 => 0x8000000100000010

/-- The only readable bytes are the exact instruction; every ordinary operand
address is unmapped. RSP and all nondestination registers hold noncanonical
canaries. These abstract flag words are not native PUSHFQ observations. -/
private def entry (code : List Byte) (destination : Register := .rax)
    (input : Word := 0x8000000000000001) (flags : Word := 0x602)
    (rip : Word := 4096) : State where
  registers := fun r => if r = destination then input else canary r
  flags := flags
  rip := rip
  memory := {
    read := fun address => code[(address - rip).toNat]?
    executable := fun address => decide ((address - rip).toNat < code.length)
    writable := fun address => address.getLsbD 4 }

/- Literal /5 r/m vectors, independent of the decoder and any encoder.
RSP/R12 and RBP/R13 use register mode without a SIB or displacement. -/
private def lowForms : List (Byte × Register) :=
  [(0xe8,.rax),(0xe9,.rcx),(0xea,.rdx),(0xeb,.rbx),
   (0xec,.rsp),(0xed,.rbp),(0xee,.rsi),(0xef,.rdi)]

private def highForms : List (Byte × Register) :=
  [(0xe8,.r8),(0xe9,.r9),(0xea,.r10),(0xeb,.r11),
   (0xec,.r12),(0xed,.r13),(0xee,.r14),(0xef,.r15)]

private def decoded (rex : Byte) (form : Byte × Register) : Bool :=
  let state := entry [rex,0xd1,form.1]
  match Sequential.decodeAt state, X86.decodeAt state, CallReturn.decodeAt state with
  | .ok actual, .error _, .ok lifted =>
    decide (actual = .shrOne64 form.2) && actual.length == 3 && actual.isNew &&
    actual.choosesAF && !actual.isLocked && actual.operandReads state == [] &&
    actual.storeIntent state == none && actual.storeIntent64 state == none &&
    decide (lifted = .sequential (.shrOne64 form.2))
  | _, _, _ => false

theorem decode_low_banks : lowForms.all (decoded 0x48) = true := by decide +kernel
theorem decode_high_banks : highForms.all (decoded 0x49) = true := by decide +kernel

/-- R and X are individually and jointly ignored; B alone selects the bank.
In particular R must not turn /5 into an unsupported ninth group selector. -/
theorem decode_low_rex_aliases :
    ([0x4a,0x4c,0x4e] : List Byte).all (fun rex => lowForms.all (decoded rex)) = true :=
  by decide +kernel

theorem decode_high_rex_aliases :
    ([0x4b,0x4d,0x4f] : List Byte).all (fun rex => highForms.all (decoded rex)) = true :=
  by decide +kernel

/-- Exact final value/flags and every GPR are independently supplied. Physical
AF need not vary, but both abstract choices must execute with their own AF. -/
private def outcome (code : List Byte) (destination : Register)
    (input output beforeFlags flagsFalse flagsTrue : Word) (rip : Word := 4096) : Bool :=
  let initial := entry code destination input beforeFlags rip
  [false,true].all fun af => match Sequential.step af initial with
  | .error _ => false
  | .ok observation => match observation.result with
    | .next final =>
      final.flags == (if af then flagsTrue else flagsFalse) && final.rip == rip + 3 &&
      observation.reads == [] &&
      allRegisters.all (fun r => final.registers r == if r = destination then output else canary r) &&
      ([0,rip-1,rip,rip+1,rip+2,rip+3,0x7fffffffffff,0x800000000000,
        0xffff800000000000,0xffffffffffffffff] : List Word).all (fun address =>
        final.memory.read address == initial.memory.read address &&
        final.memory.executable address == initial.memory.executable address &&
        final.memory.writable address == initial.memory.writable address)
    | _ => false

private def bankOutcome (rex : Byte) (form : Byte × Register) : Bool :=
  outcome [rex,0xd1,form.1] form.2 0x8000000000000001 0x4000000000000000
    0x602 0xe07 0xe17

theorem execution_low_banks : lowForms.all (bankOutcome 0x48) = true := by decide +kernel
theorem execution_high_banks : highForms.all (bankOutcome 0x49) = true := by decide +kernel
theorem execution_low_aliases :
    ([0x4a,0x4c,0x4e] : List Byte).all (fun rex => lowForms.all (bankOutcome rex)) = true :=
  by decide +kernel
theorem execution_high_aliases :
    ([0x4b,0x4d,0x4f] : List Byte).all (fun rex => highForms.all (bankOutcome rex)) = true :=
  by decide +kernel

/- Literal expectations distinguish SHR from SAR, byte/low32 shifts, SF from
the wrong width, CF from the new low bit, OF from the new high bit, and PF
from the entire word. Zero and one both have ZF set with different CF. -/
theorem edge_values_and_flags :
    ([(0,0,0x646,0x656), (1,0,0x647,0x657), (2,1,0x602,0x612),
      (3,1,0x603,0x613), (6,3,0x606,0x616),
      (0x100,0x80,0x602,0x612), (0x200,0x100,0x606,0x616),
      (0x100000000,0x80000000,0x606,0x616),
      (0x100000001,0x80000000,0x607,0x617),
      (0x8000000000000000,0x4000000000000000,0xe06,0xe16),
      (0xffffffffffffffff,0x7fffffffffffffff,0xe07,0xe17)] :
      List (Word × Word × Word × Word)).all (fun (input,output,flagsFalse,flagsTrue) =>
        outcome [0x4f,0xd1,0xef] .r15 input output 0x602 flagsFalse flagsTrue) = true :=
  by decide +kernel

/-- Every old status bit is overwritten while arbitrary high/reserved/RF/VM/DF
bits remain. These are synthetic abstract-frame challenges, not host profiles. -/
theorem dirty_flags_and_rsp :
    outcome [0x48,0xd1,0xec] .rsp 2 1 0xffffffffffffffff
      0xfffffffffffff72a 0xfffffffffffff73a = true ∧
    outcome [0x4b,0xd1,0xec] .r12 0 0 0xffffffffffffffff
      0xfffffffffffff76e 0xfffffffffffff77e = true ∧
    outcome [0x4c,0xd1,0xed] .rbp 1 0 0 0x45 0x55 = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

private def fault {α : Type} (result : Except Error α) (expected : Error) : Bool :=
  match result with | .error actual => actual == expected | .ok _ => false

private def rejects (code : List Byte) (expected : Error := .unsupportedEncoding) : Bool :=
  let state := entry code
  fault (Sequential.decodeAt state) expected &&
    [false,true].all (fun af => fault (Sequential.step af state) expected)

/-- The group selector is the three encoded bits, even with REX.R. Wrong
groups must not be silently interpreted as SHR; memory never becomes a GPR. -/
theorem wrong_group_and_memory :
    ([[0x48,0xd1,0xc0], [0x48,0xd1,0xc8], [0x48,0xd1,0xd0],
      [0x48,0xd1,0xd8], [0x48,0xd1,0xe0], [0x48,0xd1,0xf0], [0x48,0xd1,0xf8],
      [0x4f,0xd1,0xc0], [0x4f,0xd1,0xe0], [0x4f,0xd1,0xf8],
      [0x48,0xd1,0x28], [0x49,0xd1,0x2c,0x24],
      [0x48,0xd1,0x68,0], [0x4f,0xd1,0xa8,0,0,0,0]] : List (List Byte)).all
      (fun bytes => rejects bytes) = true := by decide +kernel

theorem wrong_width_count_and_prefix :
    ([[0x40,0xd1,0xe8], [0x41,0xd1,0xef], [0x47,0xd1,0xe8],
      [0x48,0xd0,0xe8], [0x48,0xd2,0xe8], [0x48,0xd3,0xe8],
      [0x48,0xc0,0xe8,1], [0x48,0xc1,0xe8,1], [0x48,0xc1,0xe8,0],
      [0x48,0xc1,0xe8,2], [0x48,0x48,0xd1,0xe8], [0x49,0x48,0xd1,0xe8],
      [0x66,0x48,0xd1,0xe8], [0xf0,0x48,0xd1,0xe8],
      [0xf3,0x48,0xd1,0xe8]] : List (List Byte)).all
      (fun bytes => rejects bytes) = true := by decide +kernel

/-- Unknown first bytes preserve the old error API. Unsupported here does not
assert that an encoding is invalid on a physical processor. -/
theorem unprefixed_and_unknown_prefix :
    rejects [0xd1,0xe8] (.unsupportedOpcode 0xd1) = true ∧
    rejects [0x67,0x48,0xd1,0xe8] (.unsupportedOpcode 0x67) = true ∧
    rejects [0xf2,0x48,0xd1,0xe8] (.unsupportedOpcode 0xf2) = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

private def fetchFailures (rex : Byte) : Bool :=
  let initial := entry [rex,0xd1,0xef]
  (List.range 3).all fun i =>
    let address := initial.rip + BitVec.ofNat 64 i
    let missing := { initial with memory := { initial.memory with
      read := fun a => if a = address then none else initial.memory.read a } }
    let denied := { initial with memory := { initial.memory with
      executable := fun a => if a = address then false else initial.memory.executable a } }
    [missing,denied].all fun state =>
      fault (Sequential.decodeAt state) (.inaccessibleInstruction address) &&
      fault (CallReturn.decodeAt state) (.inaccessibleInstruction address) &&
      [false,true].all (fun af => fault (Sequential.step af state) (.inaccessibleInstruction address))

theorem every_byte_fetch_authenticated :
    ([0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f] : List Byte).all fetchFailures = true :=
  by decide +kernel

theorem truncated_fetch :
    rejects [] (.inaccessibleInstruction 4096) = true ∧
    rejects [0x48] (.inaccessibleInstruction 4097) = true ∧
    rejects [0x49,0xd1] (.inaccessibleInstruction 4098) = true ∧
    rejects [0x4e,0xd1] (.inaccessibleInstruction 4098) = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem canonical_boundary_and_wrapped_rip :
    fault (Sequential.step false (entry [0x48,0xd1,0xe8] .rax 1 0x602 0x7ffffffffffe))
      (.inaccessibleInstruction 0x800000000000) = true ∧
    outcome [0x4f,0xd1,0xec] .r12 0x8000000000000001 0x4000000000000000
      0x602 0xe07 0xe17 0xfffffffffffffffd = true ∧
    outcome [0x48,0xd1,0xec] .rsp 2 1 0x602 0x602 0x612 0x7ffffffffffd = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Independent graph inventory: one SHR followed by RET, with precise
fallthrough and no extra cutpoint or operand effect. -/
theorem cfg_discovers_shared_instruction :
    CFG.analyze [0x49,0xd1,0xe8,0xc3] = .ok {
      nodes := [⟨0,.shrOne64 .r8,true,2⟩,⟨3,.legacy .ret,false,1⟩], maxDepth := 2 } :=
  rfl

theorem generated_literal_uses_public_constructor :
    Literals.instruction (.shrOne64 .r12) = "(.shrOne64 .r12)" := rfl

end EDSL.Tests.SequentialShiftOne

#audit_edsl
