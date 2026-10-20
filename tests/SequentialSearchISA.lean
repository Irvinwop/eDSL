/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Search
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.CFGTransport
import EDSL.X86.Sequential.Literals
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SequentialSearchISA
open X86 X86.Sequential

private def entry (bytes : List Byte) (registers : Register → Word := fun _ => 8192)
    (data : Word → Option Byte := fun _ => none) : State where
  registers := registers
  rip := 4096
  flags := 0x602
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length
      then bytes[address.toNat - 4096]? else data address
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)
    writable := fun _ => false }

private def observe (state : State) (af : Bool := false) :
    Except Error (Word × Word × List Read) := do
  let observation ← Sequential.step af state
  match observation.result with
  | .next final => return (final.flags, final.rip, observation.reads)
  | _ => throw .unexpectedReturn

private def singleByte (value : Byte) (address : Word) : Option Byte :=
  if address = 8192 then some value else none

private def littleWord (bytes : List Byte) (address : Word) : Option Byte :=
  if 8192 ≤ address.toNat then bytes[address.toNat - 8192]? else none

/-- Independently specified flag vectors distinguish byte-width subtraction,
operand order, high source bits, overflow, parity, and nibble borrow. -/
theorem cmp8_flags (af : Bool) :
    ([(0,0x123456789abcde01), (0x80,0x100000001), (0x7f,0x12345678000000ff),
      (0xff,0x80000000000000ff), (0,0x8000000000000080), (0x10,0x100000001)] :
      List (Byte × Word)).map (fun (left,right) =>
        observe (entry [0x38,0x17]
          (fun (register : Register) => if register = Register.rdx then right else 8192) (singleByte left)) af) =
    [.ok (0x697,4098,[⟨.data,8192,1⟩]), .ok (0xe12,4098,[⟨.data,8192,1⟩]),
     .ok (0xe83,4098,[⟨.data,8192,1⟩]), .ok (0x646,4098,[⟨.data,8192,1⟩]),
     .ok (0xe83,4098,[⟨.data,8192,1⟩]), .ok (0x616,4098,[⟨.data,8192,1⟩])] := by rfl

/-- The byte key must come from the actual source field, for all supported
unprefixed byte registers. Data has no write or execute permission. -/
theorem cmp8_sources :
    ([[0x38,7], [0x38,0x0f], [0x38,0x17], [0x38,0x1f]] : List (List Byte)).map
      (fun bytes => observe (entry bytes (fun register => match register with
        | .rax => 0x100000001 | .rcx => 0x200000002 | .rdx => 0x300000003
        | .rbx => 0x400000004 | _ => 8192) (singleByte 3))) =
    [.ok (0x602,4098,[⟨.data,8192,1⟩]), .ok (0x602,4098,[⟨.data,8192,1⟩]),
     .ok (0x646,4098,[⟨.data,8192,1⟩]), .ok (0x697,4098,[⟨.data,8192,1⟩])] := by rfl

/-- Word operands use all four little-endian bytes, LOW32 of the source and
32-bit flags. A byte compare, full64 compare or reversed subtraction fails. -/
theorem cmp32_flags (af : Bool) :
    ([([0,0,0,0],0xabcdef0100000001), ([0,0,0,0x80],0x100000001),
      ([0xff,0xff,0xff,0x7f],0x12345678ffffffff),
      ([0x78,0x56,0x34,0x12],0xfedcba9812345678),
      ([0,0,0,0],0x100000080), ([0x10,0,0,0],0x100000001)] :
      List (List Byte × Word)).map (fun (left,right) =>
        observe (entry [0x39,0x17]
          (fun (register : Register) => if register = Register.rdx then right else 8192) (littleWord left)) af) =
    [.ok (0x697,4098,[⟨.data,8192,4⟩]), .ok (0xe16,4098,[⟨.data,8192,4⟩]),
     .ok (0xe87,4098,[⟨.data,8192,4⟩]), .ok (0x646,4098,[⟨.data,8192,4⟩]),
     .ok (0x683,4098,[⟨.data,8192,4⟩]), .ok (0x616,4098,[⟨.data,8192,4⟩])] := by rfl

/-- The byte high-register rejection must not reject the same source fields
at width32: here they mean ESP/EBP/ESI/EDI, with unrestricted upper halves. -/
theorem cmp32_upper_source_fields :
    ([[0x39,0x20], [0x39,0x28], [0x39,0x30], [0x39,0x38]] : List (List Byte)).map
      (fun bytes => observe (entry bytes (fun register => match register with
        | .rsp => 0x100000001 | .rbp => 0x200000002 | .rsi => 0x300000003
        | .rdi => 0x400000004 | _ => 8192) (littleWord [3,0,0,0]))) =
    [.ok (0x602,4098,[⟨.data,8192,4⟩]), .ok (0x602,4098,[⟨.data,8192,4⟩]),
     .ok (0x646,4098,[⟨.data,8192,4⟩]), .ok (0x697,4098,[⟨.data,8192,4⟩])] := by rfl

/-- One byte is readable at the last low canonical address; a wider read
would fault. Conversely CMP32 needs bytes 1..3 even when the low byte matches. -/
theorem exact_width :
    observe (entry [0x38,0x17]
      (fun register => if register = .rdx then 0xff000080 else 0x7fffffffffff)
      (fun address => if address = 0x7fffffffffff then some 0x80 else none)) =
      .ok (0x646,4098,[⟨.data,0x7fffffffffff,1⟩]) ∧
    observe (entry [0x39,0x17] (fun _ => 8192) (singleByte 0)) =
      .error (.inaccessibleData 8193) := by exact ⟨rfl,rfl⟩

/-- Full64 base/index and scale four select a high address. Source and index
alias RDX, so the same high register must provide the address and LOW32 key. -/
theorem high_address_and_source_alias :
    observe (entry [0x39,0x14,0x97]
      (fun register => if register = .rdi then 0x200000001 else 0x100000002)
      (fun address => if 0x600000009 ≤ address.toNat then
        ([2,0,0,0] : List Byte)[address.toNat - 0x600000009]? else none)) =
      .ok (0x646,4099,[⟨.data,0x600000009,4⟩]) := by rfl

theorem all_address_registers_alias :
    observe (entry [0x38,0x14,0x52] (fun _ => 8192)
      (fun address => if address = 24576 then some 0 else none)) =
      .ok (0x646,4099,[⟨.data,24576,1⟩]) := by rfl

/-- Byte canonicality and complete word-span validation come from production
memory primitives, including the high canonical range's wrapping boundary. -/
theorem data_faults :
    (observe (entry [0x38,0x17]),
      observe (entry [0x38,0x17] (fun _ => 0x800000000000) (fun _ => some 0)),
      observe (entry [0x39,0x17] (fun _ => 0x7ffffffffffe) (fun _ => some 0)),
      observe (entry [0x39,0x17] (fun _ => 0xfffffffffffffffe) (fun _ => some 0))) =
    (.error (.inaccessibleData 8192), .error (.inaccessibleData 0x800000000000),
     .error (.inaccessibleData 0x800000000000), .error (.inaccessibleData 0xfffffffffffffffe)) := by rfl

private def moved (bytes : List Byte) (destination : Register := .rax) :
    Except Error (Word × Word × Word × List Read) := do
  let observation ← Sequential.step true (entry bytes (fun _ => 0x123456789abcdef0))
  match observation.result with
  | .next final => return (final.registers destination, final.flags, final.rip, observation.reads)
  | _ => throw .unexpectedReturn

/-- Sign extension uses bit31 and all four immediate bytes. These cases
separate signExtend32 from zero extension and signExtend8/16, and check LE. -/
theorem mov_immediate_width :
    ([[0x48,0xc7,0xc0,0xff,0xff,0xff,0xff], [0x48,0xc7,0xc0,0,0,0,0x80],
      [0x48,0xc7,0xc0,0xff,0xff,0xff,0x7f], [0x48,0xc7,0xc0,0x80,0,0,0],
      [0x48,0xc7,0xc0,0,0x80,0,0], [0x48,0xc7,0xc0,0x78,0x56,0x34,0x12]] :
      List (List Byte)).map (fun bytes => moved bytes) =
    [.ok (0xffffffffffffffff,0x602,4103,[]), .ok (0xffffffff80000000,0x602,4103,[]),
     .ok (0x7fffffff,0x602,4103,[]), .ok (128,0x602,4103,[]),
     .ok (32768,0x602,4103,[]), .ok (0x12345678,0x602,4103,[])] := by rfl

/-- Destinations include RSP and both banks; /0 must not be decoded as a
source register. No stack/data memory exists in any of these cases. -/
theorem mov_destinations :
    ([([0x48,0xc7,0xc4,0xfe,0xff,0xff,0xff],.rsp),
      ([0x49,0xc7,0xc0,0xfe,0xff,0xff,0xff],.r8),
      ([0x49,0xc7,0xc7,0xfe,0xff,0xff,0xff],.r15)] :
      List (List Byte × Register)).map (fun (bytes,destination) => moved bytes destination) =
    List.replicate 3 (.ok (0xfffffffffffffffe,0x602,4103,[])) := by rfl

private def sentinel : List Byte := [0x48,0xc7,0xc0,0xff,0xff,0xff,0xff]

/-- Every truncated instruction and every fetch-permission hole fails at
that byte, including immediate offsets5/6 beyond the old five-byte bound. -/
theorem mov_fetches :
    (List.range 7).map (fun count => Sequential.decodeAt (entry (sentinel.take count))) =
      (List.range 7).map (fun count => .error (.inaccessibleInstruction (4096 + BitVec.ofNat 64 count))) ∧
    (List.range 7).map (fun offset =>
      let initial := entry sentinel
      Sequential.decodeAt { initial with memory := { initial.memory with
        executable := fun address => address != 4096 + BitVec.ofNat 64 offset } }) =
      (List.range 7).map (fun offset => .error (.inaccessibleInstruction (4096 + BitVec.ofNat 64 offset))) := by
  exact ⟨rfl,rfl⟩

theorem cmp_fetches :
    ([[0x38], [0x38,0x14], [0x39], [0x39,0x14]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error (.inaccessibleInstruction 4097), .error (.inaccessibleInstruction 4098),
     .error (.inaccessibleInstruction 4097), .error (.inaccessibleInstruction 4098)] := by rfl

theorem cmp_sib_fetch_permission :
    ([[0x38,0x14,7], [0x39,0x14,0x8f]] : List (List Byte)).map (fun bytes =>
      let initial := entry bytes (data := fun _ => some 0)
      observe { initial with memory := { initial.memory with
        executable := fun address => address != 4098 } }) =
    List.replicate 2 (.error (.inaccessibleInstruction 4098)) := by rfl

/-- Transport binds all seven current bytes at an arbitrary code address,
while preserving the complete supplied RAM, flag word, and other GPRs. -/
theorem sentinel_current_code (state : State) (code : CodeAt state.memory state.rip sentinel)
    (af : Bool) :
    Sequential.step af state = .ok ⟨.next { state.writeRegister .rax 0xffffffffffffffff with
      rip := state.rip + 7 }, []⟩ := by
  rw [step_code_eq_execute code (by decide) (offset := 0) (by decide) state rfl
    (by simp) (by rfl : Sequential.decodeAt (codeState sentinel 0) =
      .ok (.movSignImm32 .rax 0xffffffff)) af]
  rfl

/-- The relocated memory comparisons preserve all registers and the entire
current memory, including permission maps, for every key and every AF choice.
These concrete instruction bytes select the source and scale independently. -/
theorem cmp32_current_code (state : State) (af : Bool) (value : BitVec 32)
    (code : CodeAt state.memory state.rip [0x39,0x14,0x8f])
    (loaded : loadDWord state.memory (state.registers .rdi + (state.registers .rcx <<< (2 : Nat))) = .ok value) :
    Sequential.step af state = .ok ⟨.next { state with
      rip := state.rip + 3
      flags := cmpFlags32 state.flags value ((state.registers .rdx).setWidth 32) },
      [⟨.data,state.registers .rdi + (state.registers .rcx <<< (2 : Nat)),4⟩]⟩ := by
  rw [step_code_eq_execute code (by decide) (offset := 0) (by decide) state rfl (by simp)
    (by rfl : Sequential.decodeAt (codeState [0x39,0x14,0x8f] 0) =
      .ok (.cmpMemReg32 (.indexed .rdi .rcx 2) .rdx)) af]
  have actualLoad : loadDWord state.memory ((Address.indexed .rdi .rcx 2).eval state) = .ok value := loaded
  rw [execute_cmpMemReg32, actualLoad]
  rfl

theorem cmp8_current_code (state : State) (af : Bool) (value : Byte)
    (code : CodeAt state.memory state.rip [0x38,0x14,7])
    (loaded : readDataByte state.memory (state.registers .rdi + state.registers .rax) = .ok value) :
    Sequential.step af state = .ok ⟨.next { state with
      rip := state.rip + 3
      flags := cmpFlags8 state.flags value ((state.registers .rdx).setWidth 8) },
      [⟨.data,state.registers .rdi + state.registers .rax,1⟩]⟩ := by
  rw [step_code_eq_execute code (by decide) (offset := 0) (by decide) state rfl (by simp)
    (by rfl : Sequential.decodeAt (codeState [0x38,0x14,7] 0) =
      .ok (.cmpMemReg8 (.indexed .rdi .rax 0) .rdx)) af]
  have actualLoad : readDataByte state.memory ((Address.indexed .rdi .rax 0).eval state) = .ok value := by
    change readDataByte state.memory (state.registers .rdi + (state.registers .rax <<< (0 : Nat))) = .ok value
    simpa only [BitVec.shiftLeft_zero] using loaded
  rw [execute_cmpMemReg8, actualLoad]
  simp only [Address.eval, show (0 : Fin 4).val = 0 from rfl, BitVec.shiftLeft_zero]
  rfl

/-- The checked encoder preserves independent known encodings. It rejects
unencodable byte registers/addresses rather than dropping bank or width bits. -/
theorem literal_encodings :
    ([.cmpMemReg8 (.indexed .rdi .rax 0) .rdx,
      .cmpMemReg32 (.indexed .rdi .rcx 2) .rdx,
      .movSignImm32 .rax 0xffffffff, .movSignImm32 .r15 0x12345678] : List Sequential.Instruction).map
      Literals.searchEncoding =
    [some [0x38,0x14,7], some [0x39,0x14,0x8f], some sentinel,
      some [0x49,0xc7,0xc7,0x78,0x56,0x34,0x12]] ∧
    ([.cmpMemReg8 (.base .rdi) .rsp, .cmpMemReg8 (.base .rdi) .r8,
      .cmpMemReg32 (.base .rdi) .r10, .cmpMemReg32 (.base .r12) .rdx,
      .cmpMemReg8 (.base .rbp) .rdx, .cmpMemReg32 (.indexed .rdi .rsp 2) .rdx,
      .cmpMemReg32 (.indexed .r13 .rcx 2) .rdx] : List Sequential.Instruction).map
      Literals.searchEncoding = List.replicate 7 none := by exact ⟨rfl,rfl⟩

/-- Unsupported high-byte codes, displacements, absent SIB
components, extra prefixes, memory C7, and C7 extensions other than /0 reject. -/
theorem unsupported_forms :
    ([[0x38,0x27], [0x38,0x2f], [0x38,0x37], [0x38,0x3f],
      [0x38,0x57,0], [0x39,0x97,0,0,0,0], [0x38,0x15,0,0,0,0],
      [0x39,0x14,0x27], [0x38,0x14,5],
      [0x66,0x38,0x17], [0x40,0x38,0x17], [0x48,0x38,0x17],
      [0x40,0x39,0x17], [0x48,0x39,0x17],
      [0x48,0xc7,7,1,0,0,0], [0x49,0xc7,4,0x24,1,0,0,0],
      [0x48,0xc7,0xc8,1,0,0,0], [0x48,0xc7,0xf8,1,0,0,0],
      [0x4a,0xc7,0xc0,1,0,0,0], [0x4c,0xc7,0xc0,1,0,0,0],
      [0x40,0xc7,0xc0,1,0,0,0], [0x66,0x48,0xc7,0xc0,1,0,0,0],
      [0x48,0x48,0xc7,0xc0,1,0,0,0]] : List (List Byte)).all
      (fun bytes => match Sequential.decodeAt (entry bytes) with
        | .error .unsupportedEncoding => true | _ => false) = true ∧
    (Sequential.decodeAt (entry [0xc7,0xc0,1,0,0,0])).isOk = false ∧
    (X86.decodeAt (entry sentinel)).isOk = false ∧
    (X86.decodeAt (entry [0x38,0x17])).isOk = false := by exact ⟨rfl,rfl,rfl,rfl⟩

/-- Exact full frozen ELF slices independently extracted by manifest offsets.
These finite CFG tests confer no functional certificate or corpus score. -/
def gccByte : List Byte :=
  [0xf3,0x0f,0x1e,0xfa,0x48,0x85,0xf6,0x74,0x17,0x31,0xc0,0xeb,0x0c,0x0f,0x1f,0,
   0x48,0x83,0xc0,1,0x48,0x39,0xc6,0x74,7,0x38,0x14,7,0x75,0xf2,0xc3,0x90,
   0x48,0xc7,0xc0,0xff,0xff,0xff,0xff,0xc3]

def gccWord : List Byte :=
  [0xf3,0x0f,0x1e,0xfa,0x48,0x85,0xf6,0x74,0x17,0x31,0xc0,0xeb,0x0c,0x0f,0x1f,0,
   0x48,0x83,0xc0,1,0x48,0x39,0xc6,0x74,7,0x39,0x14,0x87,0x75,0xf2,0xc3,0x90,
   0x48,0xc7,0xc0,0xff,0xff,0xff,0xff,0xc3]

def clangByte : List Byte :=
  [0x48,0xc7,0xc0,0xff,0xff,0xff,0xff,0x48,0x85,0xf6,0x74,0x11,0x31,0xc9,0x66,0x90,
   0x38,0x14,0x0f,0x74,9,0x48,0xff,0xc1,0x48,0x39,0xce,0x75,0xf3,0xc3,0x48,0x89,0xc8,0xc3]

def clangWord : List Byte :=
  [0x48,0xc7,0xc0,0xff,0xff,0xff,0xff,0x48,0x85,0xf6,0x74,0x11,0x31,0xc9,0x66,0x90,
   0x39,0x14,0x8f,0x74,9,0x48,0xff,0xc1,0x48,0x39,0xce,0x75,0xf3,0xc3,0x48,0x89,0xc8,0xc3]

theorem frozen_cfgs :
    ([gccByte,gccWord,clangByte,clangWord].map fun bytes =>
      (CFG.analyze bytes).map (fun graph => (bytes.length, graph.nodes.map (·.offset)))) =
    [.ok (40,[0,4,7,9,11,13,16,20,23,25,28,30,31,32,39]),
     .ok (40,[0,4,7,9,11,13,16,20,23,25,28,30,31,32,39]),
     .ok (34,[0,7,10,12,14,16,19,21,24,27,29,30,33]),
     .ok (34,[0,7,10,12,14,16,19,21,24,27,29,30,33])] := by rfl

private def gccGraph : CFG.Graph := CFG.annotate [
  ⟨0,.endbr64IbtDisabled,false,0⟩, ⟨4,.test64 .rsi .rsi,false,0⟩,
  ⟨7,.je 0x17,false,0⟩, ⟨9,.xorSelf32 .rax,false,0⟩, ⟨11,.jmp 12,false,0⟩,
  ⟨13,.nop .three,false,0⟩, ⟨16,.addImm64 .rax 1,false,0⟩,
  ⟨20,.cmp64 .rsi .rax,false,0⟩, ⟨23,.je 7,false,0⟩,
  ⟨25,.cmpMemReg8 (.indexed .rdi .rax 0) .rdx,false,0⟩,
  ⟨28,.legacy (.jnz 0xf2),false,0⟩, ⟨30,.legacy .ret,false,0⟩,
  ⟨31,.nop .one,false,0⟩, ⟨32,.movSignImm32 .rax 0xffffffff,false,0⟩,
  ⟨39,.legacy .ret,false,0⟩]

/-- Checking binds the comparison width, full address scale, MOV immediate
and exact instruction starts. A graph accepted for one row cannot certify the
other row, a changed sentinel, or an edge entering an instruction suffix. -/
theorem cfg_binding :
    CFG.check gccByte gccGraph = true ∧ CFG.check gccWord gccGraph = false ∧
    CFG.check (gccByte.set 35 0x7f) gccGraph = false ∧
    (CFG.discover (gccByte.set 12 13)).isSome = false ∧
    CFG.check (gccByte ++ List.replicate 25 0x90) gccGraph = false ∧
    CFG.check (List.replicate 32 0x90 ++ [0xc3])
      ⟨(List.range 32).map (fun offset => ⟨offset,.nop .one,true,0⟩) ++
        [⟨32,.legacy .ret,false,0⟩],0⟩ = false := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end EDSL.Tests.SequentialSearchISA

#audit_edsl
