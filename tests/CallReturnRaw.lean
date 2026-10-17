/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.CallReturn
import EDSL.X86.CodeCheck
import EDSL.Audit

namespace EDSL.Tests.CallReturnRaw
open X86
open X86.CallReturn

set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

-- Literal complete final .text windows from separate-TU compiler probes.
def gcc : List Byte := [0x50,0xe8,5,0,0,0,0x5a,0x48,0xff,0xc0,0xc3,0x48,0x8d,0x47,1,0xc3]
def clang : List Byte := [0x50,0xe8,5,0,0,0,0x48,0xff,0xc0,0x59,0xc3,0x48,0x8d,0x47,1,0xc3]
def backward : List Byte := [0x48,0x8d,0x47,1,0xc3,0xe8,0xf6,0xff,0xff,0xff,0x48,0xff,0xc0,0xc3]

-- 16 writable frame bytes followed by a read-only original caller slot.
-- Literal RA bytes and literal saved-register bytes are independent of encoders.
def ram (bytes : List Byte) (caller : List Byte := [0,0x30,0,0,0,0,0,0]) : Memory where
  read address :=
    if 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + bytes.length then bytes[address.toNat - 0x1000]?
    else if 0x1ff0 ≤ address.toNat ∧ address.toNat < 0x2000 then some 0xaa
    else if 0x2000 ≤ address.toNat ∧ address.toNat < 0x2008 then caller[address.toNat - 0x2000]?
    else none
  executable address := decide (0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + bytes.length)
  writable address := decide (0x1ff0 ≤ address.toNat ∧ address.toNat < 0x2000)

def initial (bytes : List Byte) (x : Word := 0) : State where
  registers r := match r with
    | .rax => 0x1122334455667788 | .rsp => 0x2000 | .rdi => x
    | .rcx => 0x1000000000000001 | .rdx => 0x2000000000000002
    | .rbx => 0x3000000000000003 | .rbp => 0x5000000000000005
    | .rsi => 0x6000000000000006 | .r8 => 0x8000000000000008
    | .r9 => 0x9000000000000009 | .r10 => 0xa00000000000000a
    | .r11 => 0xb00000000000000b | .r12 => 0xc00000000000000c
    | .r13 => 0xd00000000000000d | .r14 => 0xe00000000000000e | .r15 => 0xf00000000000000f
  rip := 0x1000
  flags := 0x203
  memory := ram bytes

def registers : List Register := [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

structure Summary where
  gpr : List Word
  pc : Word
  flags : Word
  count : Nat
  reads : List Sequential.Read
  frame : List (Option Byte)
  caller : Except Error Word

def summary (result : Result) : Summary :=
  ⟨registers.map result.state.registers, result.state.rip, result.state.flags, result.instructions, result.reads,
    (List.range 16).map (fun n => result.state.memory.read (0x1ff0 + BitVec.ofNat 64 n)),
    readWord result.state.memory 0x2000⟩

def gccAnswer (x answer : Word) : Summary :=
  ⟨[answer,0x1000000000000001,0x1122334455667788,0x3000000000000003,0x2008,
    0x5000000000000005,0x6000000000000006,x,0x8000000000000008,0x9000000000000009,
    0xa00000000000000a,0xb00000000000000b,0xc00000000000000c,0xd00000000000000d,
    0xe00000000000000e,0xf00000000000000f],0x3000,0x203,7,
    [⟨.stack,0x1ff0,8⟩,⟨.stack,0x1ff8,8⟩,⟨.stack,0x2000,8⟩],
    [some 6,some 0x10,some 0,some 0,some 0,some 0,some 0,some 0,
     some 0x88,some 0x77,some 0x66,some 0x55,some 0x44,some 0x33,some 0x22,some 0x11],.ok 0x3000⟩

def clangAnswer (x answer : Word) : Summary :=
  { gccAnswer x answer with gpr :=
    [answer,0x1122334455667788,0x2000000000000002,0x3000000000000003,0x2008,
    0x5000000000000005,0x6000000000000006,x,0x8000000000000008,0x9000000000000009,
    0xa00000000000000a,0xb00000000000000b,0xc00000000000000c,0xd00000000000000d,
    0xe00000000000000e,0xf00000000000000f] }

-- Seven instructions, including continuation AFTER the helper RET. Every AF
-- choice stream is quantified: the retained INC/RET semantics ignore choices.
example (choices : Choices) : (run choices 7 (initial gcc)).map summary = .ok (gccAnswer 0 2) := by rfl
example (choices : Choices) : (run choices 7 (initial clang)).map summary = .ok (clangAnswer 0 2) := by rfl
example (choices : Choices) : (run choices 7 (initial gcc 0xffffffffffffffff)).map summary =
    .ok (gccAnswer 0xffffffffffffffff 1) := by rfl
example (choices : Choices) : (run choices 7 (initial clang 0xffffffffffffffff)).map summary =
    .ok (clangAnswer 0xffffffffffffffff 1) := by rfl
example (choices : Choices) : run choices 6 (initial gcc) = .error .exhaustedFuel := by rfl

-- Backwards E8 -10 reaches the helper prefix at offset zero. CodeAt covers
-- the full fourteen-byte window although entry is +5 (nine-byte caller).
example : checkCode (ram backward) 0x1000 backward = true := by rfl
example : CodeAt (ram backward) 0x1000 backward := checkCode_sound _ _ _ (by rfl)
example : CallReturn.decodeAt { initial backward with rip := 0x1005 } = .ok (.callRelative32 0xfffffff6) := by rfl
example (choices : Choices) :
    (run choices 5 { initial backward with rip := 0x1005 }).map
      (fun r => (r.state.registers .rax,r.state.rip,r.state.registers .rsp,r.instructions,r.reads)) =
      .ok (2,0x3000,0x2008,5,[⟨.stack,0x1ff8,8⟩,⟨.stack,0x2000,8⟩]) := by rfl

-- Every GPR bank and RSP are decoded from opcode+rd; ignored R/X/W bits do
-- not extend the register bank. Prefix presence still changes RIP by two.
def decode (bytes : List Byte) : Except Error CallReturn.Instruction :=
  CallReturn.decodeAt (Sequential.codeState bytes 0)
example : ([0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57] : List Byte).map (fun b => decode [b]) =
    [.ok (.push64 .rax false),.ok (.push64 .rcx false),.ok (.push64 .rdx false),.ok (.push64 .rbx false),
     .ok (.push64 .rsp false),.ok (.push64 .rbp false),.ok (.push64 .rsi false),.ok (.push64 .rdi false)] := by rfl
example : ([0x58,0x59,0x5a,0x5b,0x5c,0x5d,0x5e,0x5f] : List Byte).map (fun b => decode [b]) =
    [.ok (.pop64 .rax false),.ok (.pop64 .rcx false),.ok (.pop64 .rdx false),.ok (.pop64 .rbx false),
     .ok (.pop64 .rsp false),.ok (.pop64 .rbp false),.ok (.pop64 .rsi false),.ok (.pop64 .rdi false)] := by rfl
example : ([0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57] : List Byte).map (fun b => decode [0x4f,b]) =
    [.ok (.push64 .r8 true),.ok (.push64 .r9 true),.ok (.push64 .r10 true),.ok (.push64 .r11 true),
     .ok (.push64 .r12 true),.ok (.push64 .r13 true),.ok (.push64 .r14 true),.ok (.push64 .r15 true)] := by rfl
example : ([0x58,0x59,0x5a,0x5b,0x5c,0x5d,0x5e,0x5f] : List Byte).map (fun b => decode [0x41,b]) =
    [.ok (.pop64 .r8 true),.ok (.pop64 .r9 true),.ok (.pop64 .r10 true),.ok (.pop64 .r11 true),
     .ok (.pop64 .r12 true),.ok (.pop64 .r13 true),.ok (.pop64 .r14 true),.ok (.pop64 .r15 true)] := by rfl
example : decode [0x40,0x50] = .ok (.push64 .rax true) := by rfl
example : decode [0x4e,0x5c] = .ok (.pop64 .rsp true) := by rfl
-- Every REX prefix selects the opcode register bank with B alone, including
-- prefixes whose ignored R/X/W bits differ individually.
example : ([0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,
    0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f] : List Byte).map (fun b => decode [b,0x50]) =
    [.ok (.push64 .rax true),.ok (.push64 .r8 true),
     .ok (.push64 .rax true),.ok (.push64 .r8 true),
     .ok (.push64 .rax true),.ok (.push64 .r8 true),
     .ok (.push64 .rax true),.ok (.push64 .r8 true),
     .ok (.push64 .rax true),.ok (.push64 .r8 true),
     .ok (.push64 .rax true),.ok (.push64 .r8 true),
     .ok (.push64 .rax true),.ok (.push64 .r8 true),
     .ok (.push64 .rax true),.ok (.push64 .r8 true)] := by rfl

def rawCPU (state : State) : Except Error (Word × Word × Word × Word × List Sequential.Read × Except Error Word) := do
  let observation ← rawStep false state
  match observation.result with
  | .next after | .returned after => return (after.rip,after.registers .rsp,after.registers .rax,after.flags,
      observation.reads,readWord after.memory 0x1ff8)
  | _ => throw .unexpectedReturn

-- PUSH RSP stores the old value, and POP RSP's loaded full value wins over +8.
example : rawCPU (initial [0x54]) = .ok (0x1001,0x1ff8,0x1122334455667788,0x203,[],.ok 0x2000) := by rfl
example : rawCPU (initial [0x40,0x54]) = .ok (0x1002,0x1ff8,0x1122334455667788,0x203,[],.ok 0x2000) := by rfl
example : rawCPU { initial [0x5c] with memory := ram [0x5c] [0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88] } =
    .ok (0x1001,0x8877665544332211,0x1122334455667788,0x203,[⟨.stack,0x2000,8⟩],.ok 0xaaaaaaaaaaaaaaaa) := by rfl
example : rawCPU { initial [0x58] with memory := ram [0x58] [0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88] } =
    .ok (0x1001,0x2008,0x8877665544332211,0x203,[⟨.stack,0x2000,8⟩],.ok 0xaaaaaaaaaaaaaaaa) := by rfl

-- High-half arithmetic, negative disp8, R13 base, R12 SIB index versus missing
-- index, and the encoded five-byte no-index SIB length.
example : decode [0x4d,0x8d,0x45,0xff] = .ok (.leaDisp8 .r8 (.plain .r13) 0xff) := by rfl
example : decode [0x4b,0x8d,0x44,0xa5,0x80] =
    .ok (.leaDisp8 .rax (.sib .r13 (some .r12) 2) 0x80) := by rfl
example : decode [0x49,0x8d,0x44,0xa5,0x80] =
    .ok (.leaDisp8 .rax (.sib .r13 none 2) 0x80) := by rfl
example : rawCPU (initial [0x48,0x8d,0x47,0xff] 0xffff800000000001) =
    .ok (0x1004,0x2000,0xffff800000000000,0x203,[],.ok 0xaaaaaaaaaaaaaaaa) := by rfl
example : rawCPU (initial [0x4b,0x8d,0x44,0xa5,0x80]) =
    .ok (0x1005,0x2000,0xcfffffffffffffbd,0x203,[],.ok 0xaaaaaaaaaaaaaaaa) := by rfl
example : rawCPU (initial [0x49,0x8d,0x44,0xa5,0x80]) =
    .ok (0x1005,0x2000,0xcfffffffffffff8d,0x203,[],.ok 0xaaaaaaaaaaaaaaaa) := by rfl

-- No premature target fetch in CALL. Its following actual fetch must fault.
example : rawCPU (initial [0xe8,0,0xe0,0xff,0xff]) =
    .ok (0xfffffffffffff005,0x1ff8,0x1122334455667788,0x203,[],.ok 0x1005) := by rfl
example (choices : Choices) : run choices 2 (initial [0xe8,0,0xe0,0xff,0xff]) =
    .error (.inaccessibleInstruction 0xfffffffffffff005) := by rfl
example : rawStep false (initial [0xe8,0,0,0]) = .error (.inaccessibleInstruction 0x1004) := by rfl
example : rawStep false { initial [0xe8,0,0,0,0] with memory :=
    { ram [0xe8,0,0,0,0] with executable := fun a => decide (a ≠ 0x1002) } } =
    .error (.inaccessibleInstruction 0x1002) := by rfl
example : rawStep false { initial [0x50] with memory :=
    { ram [0x50] with read := fun a => if a = 0x1fff then none else (ram [0x50]).read a } } =
    .error (.writeDenied 0x1ff8) := by rfl
example : rawStep false { initial [0xe8,0,0,0,0] with memory :=
    { ram [0xe8,0,0,0,0] with writable := fun a => decide (a ≠ 0x1fff) } } =
    .error (.writeDenied 0x1ff8) := by rfl
example : rawStep false { initial [0x58] with memory :=
    { ram [0x58] with read := fun a => if a = 0x2007 then none else (ram [0x58]).read a } } =
    .error (.inaccessibleStack 0x2007) := by rfl

-- Relocate a five-byte instruction to the last five lower-canonical bytes.
def edgeState (last : Byte) : State :=
  { initial [] with rip := 0x7ffffffffffb, memory :=
    { read := fun a => if 0x7ffffffffffb ≤ a.toNat ∧ a.toNat ≤ 0x7fffffffffff then
          ([0xe8,last,0xff,0xff,0xff] : List Byte)[a.toNat - 0x7ffffffffffb]?
        else (ram []).read a
      executable := fun a => decide (0x7ffffffffffb ≤ a.toNat ∧ a.toNat ≤ 0x7fffffffffff)
      writable := (ram []).writable } }
example : rawCPU (edgeState 0xff) =
    .ok (0x7fffffffffff,0x1ff8,0x1122334455667788,0x203,[],.ok 0x800000000000) := by rfl
-- Noncanonical target wins even when the store would be denied.
example : execute { initial [] with rip := 0x7ffffffffffa, memory := { ram [] with writable := fun _ => false } }
    (.callRelative32 1) false = .error (.noncanonicalBranch 0x800000000000) := by rfl
-- The same priority must hold through actual E8 decoding and raw execution.
example : rawStep false { edgeState 0 with memory :=
    { (edgeState 0).memory with
      read := fun a => if a = 0x7ffffffffffd ∨ a = 0x7ffffffffffe ∨ a = 0x7fffffffffff
        then some 0 else (edgeState 0).memory.read a
      writable := fun _ => false } } =
    .error (.noncanonicalBranch 0x800000000000) := by rfl

-- Original-slot RET terminates even if its actual target is executable inside
-- the same code window. An inner-slot RET to outside must instead try fetching.
example (choices : Choices) :
    (run choices 1 { initial [0xc3] with memory := ram [0xc3] [0,0x10,0,0,0,0,0,0] }).map
      (fun r => (r.state.rip,r.state.registers .rsp,r.instructions,r.reads)) =
    .ok (0x1000,0x2008,1,[⟨.stack,0x2000,8⟩]) := by rfl
example (choices : Choices) : runFrom 0x2010 choices 2 (initial [0xc3]) =
    .error (.inaccessibleInstruction 0x3000) := by rfl

-- An internal RET follows a replacement RAM word, including when its target
-- is another RET. There is no target-range heuristic or ghost repair.
def tampered (target : Word) : State :=
  { (initial [0xc3]).writeRegister .rsp 0x1ff8 with
    memory := writeQWordUnchecked (ram [0xc3]) 0x1ff8 target }
example (choices : Choices) : runFrom 0x2000 choices 2 (tampered 0x4444) =
    .error (.inaccessibleInstruction 0x4444) := by rfl
example (choices : Choices) :
    (runFrom 0x2000 choices 2 (tampered 0x1000)).map (fun r => (r.instructions,r.state.rip,r.reads)) =
    .ok (2,0x3000,[⟨.stack,0x1ff8,8⟩,⟨.stack,0x2000,8⟩]) := by rfl

-- Execute PUSH, CALL, and the helper LEA before overwriting its saved return
-- address. Continuing with the original boundary must follow that overwrite.
private def continuing (observation : Observation) : Except Error State :=
  match observation.result with
  | .next after => .ok after
  | _ => .error .unexpectedReturn

def tamperAfterCall (target : Word) : Except Error State := do
  let pushed ← continuing (← rawStep false (initial gcc))
  let called ← continuing (← rawStep false pushed)
  let beforeRet ← continuing (← rawStep false called)
  return { beforeRet with memory := writeQWordUnchecked beforeRet.memory 0x1ff0 target }

example (choices : Choices) :
    (tamperAfterCall 0x4444 >>= runFrom 0x2000 choices 2) =
      .error (.inaccessibleInstruction 0x4444) := by rfl
example (choices : Choices) :
    (tamperAfterCall 0x100a >>= runFrom 0x2000 choices 2) =
      .error (.noncanonicalReturn 0x1122334455667788) := by rfl

-- Explicit unsupported forms: no extra prefixes, prefixed/indirect/far CALL,
-- RET immediate, stack memory/16-bit or mod=10 LEA are admitted by extension.
example : decode [0x66,0x50] = .error (.unsupportedOpcode 0x66) := by rfl
example : decode [0x40,0x41,0x50] = .error .unsupportedEncoding := by rfl
example : decode [0xf0,0xe8,0,0,0,0] = .error .unsupportedEncoding := by rfl
example : decode [0xff,0xd0] = .error (.unsupportedOpcode 0xff) := by rfl
example : decode [0xff,0x37] = .error (.unsupportedOpcode 0xff) := by rfl
example : decode [0x8f,0x00] = .error (.unsupportedOpcode 0x8f) := by rfl
example : decode [0x9a,0,0,0,0] = .error (.unsupportedOpcode 0x9a) := by rfl
example : decode [0xc2,8,0] = .error (.unsupportedOpcode 0xc2) := by rfl
example : decode [0x48,0x8d,0x87,0,0,0,0] = .error .unsupportedEncoding := by rfl
example : decode [0x48,0x8d,0x47] = .error (.inaccessibleInstruction 3) := by rfl
example : Sequential.decodeAt (Sequential.codeState [0xe8,0,0,0,0] 0) =
    .error (.unsupportedOpcode 0xe8) := by rfl
example : Sequential.decodeAt (Sequential.codeState [0x50] 0) = .error (.unsupportedOpcode 0x50) := by rfl
example : Sequential.decodeAt (Sequential.codeState [0x5a] 0) = .error (.unsupportedOpcode 0x5a) := by rfl
example : Sequential.decodeAt (Sequential.codeState [0x48,0x8d,0x47,1] 0) = .error .unsupportedEncoding := by rfl
example : decode [0x48,0xff,0xc0] = .ok (.sequential (.inc64 .rax)) := by rfl
example : decode [0xc3] = .ok (.sequential (.legacy .ret)) := by rfl

end EDSL.Tests.CallReturnRaw

#print axioms EDSL.X86.CallReturn.execute_call_success_iff
#print axioms EDSL.X86.CallReturn.execute_call_context
#print axioms EDSL.X86.CallReturn.execute_push_context
#print axioms EDSL.X86.CallReturn.execute_pop_context
#print axioms EDSL.X86.CallReturn.execute_lea_context
#print axioms EDSL.X86.CallReturn.decodeNewAt_rejects_sequential
#print axioms EDSL.X86.CallReturn.decodeNewAt_admitted
#print axioms EDSL.X86.CallReturn.decodeAt_transport
#print axioms EDSL.X86.CallReturn.decodeAt_code
#print axioms EDSL.X86.CallReturn.rawStep_read_origin
#print axioms EDSL.X86.CallReturn.boundaryStep_terminal_iff
#print axioms EDSL.X86.CallReturn.boundaryStep_projection
#print axioms EDSL.X86.CallReturn.run_sound
#print axioms EDSL.X86.CallReturn.run_complete
#print axioms EDSL.X86.CallReturn.ExecutesFrom.read_origin
#print axioms EDSL.X86.CallReturn.ExecutesFrom.terminal_origin
#audit_edsl

namespace EDSL.Tests.CallReturnRaw
open X86 X86.CallReturn
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

-- Complete byte frame, quantified over every address outside the 16-byte
-- frame, rather than checking a few neighboring sentinel bytes.
theorem gcc_outside (choices : Choices) (query : Word)
    (outside : 16 ≤ (query - 0x1ff0).toNat) :
    (run choices 7 (initial gcc)).map (fun r => r.state.memory.read query) = .ok ((ram gcc).read query) := by
  have upper : 8 ≤ (query - 0x1ff8).toNat := by bv_omega
  have lower : 8 ≤ (query - 0x1ff0).toNat := by omega
  change Except.ok ((writeQWordUnchecked
    (writeQWordUnchecked (ram gcc) 0x1ff8 0x1122334455667788) 0x1ff0 0x1006).read query) = _
  rw [writeQWord_frame _ _ _ _ lower, writeQWord_frame _ _ _ _ upper]

theorem clang_outside (choices : Choices) (query : Word)
    (outside : 16 ≤ (query - 0x1ff0).toNat) :
    (run choices 7 (initial clang)).map (fun r => r.state.memory.read query) = .ok ((ram clang).read query) := by
  have upper : 8 ≤ (query - 0x1ff8).toNat := by bv_omega
  have lower : 8 ≤ (query - 0x1ff0).toNat := by omega
  change Except.ok ((writeQWordUnchecked
    (writeQWordUnchecked (ram clang) 0x1ff8 0x1122334455667788) 0x1ff0 0x1006).read query) = _
  rw [writeQWord_frame _ _ _ _ lower, writeQWord_frame _ _ _ _ upper]

example (choices : Choices) : (run choices 7 (initial gcc)).map (fun r => r.state.memory.executable) =
    .ok (ram gcc).executable := by rfl
example (choices : Choices) : (run choices 7 (initial clang)).map (fun r => r.state.memory.writable) =
    .ok (ram clang).writable := by rfl

end EDSL.Tests.CallReturnRaw
#print axioms EDSL.Tests.CallReturnRaw.gcc_outside
#print axioms EDSL.Tests.CallReturnRaw.clang_outside
#audit_edsl
