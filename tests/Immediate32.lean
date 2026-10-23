/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Immediate32
import EDSL.X86.Sequential.CallerOnly
import EDSL.X86.Sequential.Code
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.Immediate32
open X86 X86.Sequential

private def entry (bytes : List Byte) (registers : Register → Word) (flags : Word) : State :=
  { codeState bytes 0 with registers := registers, flags := flags }

private def valueEntry (bytes : List Byte) (destination : Register) (value : Word)
    (flags : Word := 0x602) : State :=
  entry bytes (fun register => if register = destination then value else 0x123456789abcdef0) flags

private structure Snapshot where
  registers : List Word
  flags : Word
  rip : Word
  reads : List Read
  deriving DecidableEq, Repr

private def observe (state : State) (registers : List Register) (af : Bool := false) : Option Snapshot :=
  match Sequential.step af state with
  | .ok ⟨.next final, reads⟩ => some ⟨registers.map final.registers, final.flags, final.rip, reads⟩
  | _ => none

/-- Borrow is not the carry of ADD(-imm). These independent RFLAGS words
also distinguish nibble borrow, zero, sign, low-byte parity and both overflow
directions; old upper halves must not enter the arithmetic. -/
theorem sub_full_flags :
    [observe (valueEntry [0x83,0xee,1] .rsi 0xdeadbeef00000000) [.rsi],
     observe (valueEntry [0x83,0xee,1] .rsi 0xdeadbeef00000010) [.rsi],
     observe (valueEntry [0x83,0xee,1] .rsi 0xdeadbeef00000001) [.rsi],
     observe (valueEntry [0x83,0xee,1] .rsi 0xdeadbeef80000000) [.rsi],
     observe (valueEntry [0x83,0xee,0xff] .rsi 0xdeadbeef7fffffff) [.rsi],
     observe (valueEntry [0x83,0xee,0xff] .rsi 0xdeadbeef00000000) [.rsi]] =
    [some ⟨[0xffffffff],0x697,3,[]⟩, some ⟨[15],0x616,3,[]⟩,
     some ⟨[0],0x646,3,[]⟩, some ⟨[0x7fffffff],0xe16,3,[]⟩,
     some ⟨[0x80000000],0xe87,3,[]⟩, some ⟨[1],0x613,3,[]⟩] := by
  decide +kernel

/-- -128, -1, 0 and +127 are mathematical signed-byte cases, including
width32 wrap. In particular subtracting -128 from zero produces +128. -/
theorem signed_immediate_endpoints :
    [observe (valueEntry [0x83,0xee,0x80] .rsi 0xdeadbeef00000000) [.rsi],
     observe (valueEntry [0x83,0xee,0x80] .rsi 0xdeadbeef00000080) [.rsi],
     observe (valueEntry [0x83,0xee,0xff] .rsi 0xdeadbeefffffffff) [.rsi],
     observe (valueEntry [0x83,0xee,0] .rsi 0xdeadbeef00000000) [.rsi],
     observe (valueEntry [0x83,0xee,0x7f] .rsi 0xdeadbeef0000007f) [.rsi]] =
    [some ⟨[128],0x603,3,[]⟩, some ⟨[256],0x607,3,[]⟩,
     some ⟨[0],0x646,3,[]⟩, some ⟨[0],0x646,3,[]⟩,
     some ⟨[0],0x646,3,[]⟩] := by
  decide +kernel

/-- CMP computes the same subtraction flags while preserving its full input
register. The -128 case rejects an accidental zero-extended immediate; the
signed-minimum case rejects CMP64 and its different SF/OF interpretation. -/
theorem cmp_full_flags_and_upper_halves :
    [observe (valueEntry [0x83,0xfe,0x80] .rsi 0xdeadbeef00000000) [.rsi],
     observe (valueEntry [0x83,0xfe,1] .rsi 0xdeadbeef80000000) [.rsi],
     observe (valueEntry [0x83,0xfe,0xff] .rsi 0xdeadbeef7fffffff) [.rsi],
     observe (valueEntry [0x83,0xfe,8] .rsi 0xdeadbeef00000008) [.rsi],
     observe (valueEntry [0x83,0xfe,0xff] .rsi 0xdeadbeefffffffff) [.rsi]] =
    [some ⟨[0xdeadbeef00000000],0x603,3,[]⟩,
     some ⟨[0xdeadbeef80000000],0xe16,3,[]⟩,
     some ⟨[0xdeadbeef7fffffff],0xe87,3,[]⟩,
     some ⟨[0xdeadbeef00000008],0x646,3,[]⟩,
     some ⟨[0xdeadbeefffffffff],0x646,3,[]⟩] := by
  decide +kernel

/-- Incoming arithmetic flags are overwritten, all other abstract flag bits
survive, and the Bool choice cannot override any defined subtraction flag. -/
theorem defined_flags_and_full_flag_frame :
    [observe (valueEntry [0x83,0xee,1] .rsi 0xdeadbeef00000010 0xfedcba9800070ed7) [.rsi] false,
     observe (valueEntry [0x83,0xee,1] .rsi 0xdeadbeef00000010 0xfedcba9800070ed7) [.rsi] true,
     observe (valueEntry [0x83,0xfe,0] .rsi 0xdeadbeef00000000 0xfedcba9800070ed7) [.rsi] true] =
    [some ⟨[15],0xfedcba9800070616,3,[]⟩,
     some ⟨[15],0xfedcba9800070616,3,[]⟩,
     some ⟨[0xdeadbeef00000000],0xfedcba9800070646,3,[]⟩] := by
  decide +kernel

/-- Real ModRM bytes select distinct low/high banks, including RSP/R12.
The literal corpus blocker encodings are exercised as generic instructions,
without changing any corpus file or granting a program certificate. -/
theorem production_register_mapping :
    ([[0x83,0xee,2], [0x83,0xfe,8], [0x40,0x83,0xec,0xff], [0x40,0x83,0xfc,0x80],
      [0x41,0x83,0xe8,0x80], [0x41,0x83,0xef,0x7f],
      [0x41,0x83,0xfc,0xff], [0x41,0x83,0xff,0]] : List (List Byte)).map
      (fun bytes => (Sequential.decodeAt (codeState bytes 0)).toOption) =
    [some (.subImm32 .rsi 2 false), some (.cmpImm32 .rsi 8 false),
     some (.subImm32 .rsp 0xff true), some (.cmpImm32 .rsp 0x80 true),
     some (.subImm32 .r8 0x80 true), some (.subImm32 .r15 0x7f true),
     some (.cmpImm32 .r12 0xff true), some (.cmpImm32 .r15 0 true)] := by
  decide +kernel

/-- The real prefixed step writes R12 rather than its low-bank partner RSP,
then independently compares R15, preserving its upper half. -/
theorem high_bank_steps :
    let registers : Register → Word := fun register => match register with
      | .rsp => 0x1111111100000010 | .r12 => 0x2222222200000000
      | .r15 => 0x3333333300000008 | _ => 0x4444444400000002
    [observe (entry [0x40,0x83,0xec,0xff] registers 0x602) [.rsp,.r12,.r15],
     observe (entry [0x41,0x83,0xec,0xff] registers 0x602) [.rsp,.r12,.r15],
     observe (entry [0x41,0x83,0xff,8] registers 0x602) [.rsp,.r12,.r15]] =
    [some ⟨[17,0x2222222200000000,0x3333333300000008],0x617,4,[]⟩,
     some ⟨[0x1111111100000010,1,0x3333333300000008],0x613,4,[]⟩,
     some ⟨[0x1111111100000010,0x2222222200000000,0x3333333300000008],0x646,4,[]⟩] := by
  decide +kernel

private theorem ok_of_toOption {ε α : Type} {result : Except ε α} {value : α}
    (present : result.toOption = some value) : result = .ok value := by
  cases result with
  | error fault => cases present
  | ok actual => exact congrArg Except.ok (Option.some.inj present)

private theorem entry_decoded {bytes : List Byte} {instruction : Sequential.Instruction}
    (registers : Register → Word) (flags : Word)
    (literal : (Sequential.decodeAt (codeState bytes 0)).toOption = some instruction) :
    Sequential.decodeAt (entry bytes registers flags) = .ok instruction :=
  @decodeAt_transport (codeState bytes 0) (entry bytes registers flags) instruction
    (fun _ _ _ fetched => fetched)
    (@ok_of_toOption Error Sequential.Instruction (Sequential.decodeAt (codeState bytes 0))
      instruction literal)

/-- Arbitrary GPRs/upper halves, not just sampled sentinels, survive actual
CMP decoding and execution. CF and OF have independent mathematical contracts. -/
theorem cmp_arbitrary_context (registers : Register → Word) (flags : Word) (af : Bool) :
    ∃ final, Sequential.step af (entry [0x83,0xfe,8] registers flags) = .ok ⟨.next final, []⟩ ∧
      final.registers = registers ∧
      final.memory = (entry [0x83,0xfe,8] registers flags).memory ∧
      final.flags &&& ~~~arithmeticFlagMask = flags &&& ~~~arithmeticFlagMask ∧
      (final.flags.getLsbD 0 = true ↔ (registers .rsi).toNat % 2^32 < 8) ∧
      (final.flags.getLsbD 11 = true ↔
        ((registers .rsi).setWidth 32).toInt - 8 < -(2^31 : Int) ∨
          2^31 ≤ ((registers .rsi).setWidth 32).toInt - 8) ∧
      final.rip = 3 := by
  let initial := entry [0x83,0xfe,8] registers flags
  have decoded : Sequential.decodeAt initial = .ok (.cmpImm32 .rsi 8 false) :=
    entry_decoded registers flags (by decide +kernel)
  obtain ⟨final, actual, registerFrame, memoryFrame, _, flagFrame, pc⟩ :=
    execute_cmpImm32_context initial .rsi 8 false af
  have bits := execute_cmpImm32_flags actual
  refine ⟨final, (step_eq_execute af decoded).trans actual, registerFrame, memoryFrame,
    flagFrame, ?_, ?_, ?_⟩
  · simpa [initial, entry, BitVec.toNat_setWidth] using bits.1
  · simpa [initial, entry] using bits.2.2.2.2.2
  · simpa [initial, entry, codeState] using pc

/-- A real high-bank SUB step refines mathematical addition of one for -1,
clears upper32 for every input, and frames all fifteen other arbitrary GPRs. -/
theorem sub_arbitrary_context (registers : Register → Word) (flags : Word) (af : Bool) :
    ∃ final, Sequential.step af (entry [0x41,0x83,0xec,0xff] registers flags) = .ok ⟨.next final, []⟩ ∧
      (final.registers .r12).toNat = (1 + (registers .r12).toNat % 2^32) % 2^32 ∧
      (final.registers .r12).toNat < 2^32 ∧
      (∀ register, register ≠ .r12 → final.registers register = registers register) ∧
      final.memory = (entry [0x41,0x83,0xec,0xff] registers flags).memory ∧
      final.flags &&& ~~~arithmeticFlagMask = flags &&& ~~~arithmeticFlagMask ∧
      final.rip = 4 := by
  let initial := entry [0x41,0x83,0xec,0xff] registers flags
  have decoded : Sequential.decodeAt initial = .ok (.subImm32 .r12 0xff true) :=
    entry_decoded registers flags (by decide +kernel)
  obtain ⟨final, actual, value, bound, registerFrame, memoryFrame, _, flagFrame, pc⟩ :=
    execute_subImm32_context initial .r12 0xff true af
  refine ⟨final, (step_eq_execute af decoded).trans actual, ?_, bound, registerFrame,
    memoryFrame, flagFrame, ?_⟩
  · simpa [initial, entry] using value
  · simpa [initial, entry, codeState] using pc

/-- The constructive raw classifier feeds exact execution transport for both
new forms with completely arbitrary replacement RAM and permissions. -/
theorem caller_memory_transport (input : State) (replacement : Memory) (destination : Register)
    (immediate : Byte) (prefixed af : Bool) :
    Sequential.execute { input with memory := replacement }
        (.subImm32 destination immediate prefixed) af =
      (Sequential.execute input (.subImm32 destination immediate prefixed) af).map
        (Observation.mapMemory (fun _ => replacement)) ∧
    Sequential.execute { input with memory := replacement }
        (.cmpImm32 destination immediate prefixed) af =
      (Sequential.execute input (.cmpImm32 destination immediate prefixed) af).map
        (Observation.mapMemory (fun _ => replacement)) := by
  have sub : CallerOnly (.subImm32 destination immediate prefixed) := trivial
  have cmp : CallerOnly (.cmpImm32 destination immediate prefixed) := trivial
  exact ⟨sub.execute_memory_eq input replacement af (by intro impossible; cases impossible),
    cmp.execute_memory_eq input replacement af (by intro impossible; cases impossible)⟩

/-- Generic code transport retains the fetched nonzero immediate at the
legacy 83 F8 overlap, for arbitrary code memory/base and arbitrary CPU context. -/
theorem relocated_cmp_eax (memory : Memory) (base : Word) (registers : Register → Word)
    (flags : Word) (code : CodeAt memory base [0x83,0xf8,0xff]) :
    Sequential.decodeAt ⟨registers,base,flags,memory⟩ = .ok (.cmpImm32 .rax 0xff false) := by
  exact decodeAt_transport
    (code_fetch_transport_of_bound code (by decide) 0 (by decide)
      ⟨registers,base,flags,memory⟩ rfl (by simp)) (by rfl)

private def fault {α : Type} (result : Except Error α) (expected : Error) : Bool :=
  match result with | .error actual => actual == expected | .ok _ => false

private def rejects (bytes : List Byte) (expected : Error := .unsupportedEncoding) : Bool :=
  let state := valueEntry bytes .rsi 0xdeadbeef00000000
  fault (Sequential.decodeAt state) expected &&
    [false,true].all (fun af => fault (Sequential.step af state) expected)

/-- Excluded group selectors, memory modes (including SIB/displacements),
16/64-bit SUB, LOCK, extra prefixes and noncanonical R/X aliases stay rejected. -/
theorem excluded_forms :
    ([[0x83,0xc8,1], [0x83,0xd0,1], [0x83,0xd8,1], [0x83,0xf0,1],
      [0xff,0xe8], [0xff,0xf8], [0x83,0x28,1], [0x83,0x38,1],
      [0x83,0x6e,0,1], [0x83,0xbe,0,0,0,0,1], [0x83,0x2c,0x24,1],
      [0x40,0x83,0x2c,0x24,1], [0x41,0x83,0x3f,1],
      [0x42,0x83,0xe8,1], [0x43,0x83,0xf8,1], [0x44,0x83,0xee,1],
      [0x45,0x83,0xfe,1], [0x46,0x83,0xee,1], [0x47,0x83,0xfe,1],
      [0x40,0x41,0x83,0xee,1], [0x41,0x40,0x83,0xfe,1],
      [0x66,0x83,0xee,1], [0x66,0x83,0xfe,1], [0x48,0x83,0xee,1],
      [0xf0,0x83,0xee,1], [0xf3,0x83,0xfe,1], [0x80,0xee,1], [0x80,0xfe,1],
      [0x40,0x81,0xee,1,0,0,0], [0x41,0x81,0xff,1,0,0,0]] : List (List Byte)).all
      (fun bytes => rejects bytes) = true := by
  decide +kernel

theorem excluded_imm32_and_address_override :
    rejects [0x81,0xee,1,0,0,0] (.unsupportedOpcode 0x81) = true ∧
    rejects [0x81,0xfe,1,0,0,0] (.unsupportedOpcode 0x81) = true ∧
    rejects [0x67,0x83,0xee,1] (.unsupportedOpcode 0x67) = true := by
  decide +kernel

/-- Accepted old forms retain their constructors/width. The adjacent nonzero
CMP EAX immediate becomes new CMP32; CMP64 stays a separate existing family. -/
theorem legacy_and_other_width_priority :
    ([[0x83,0xf8,0], [0x83,0xf8,0xff], [0x83,0xc0,1], [0x83,0xe0,0xff],
      [0xff,0xc0], [0x48,0x83,0xf8,0x80]] : List (List Byte)).map
      (fun bytes => (Sequential.decodeAt (codeState bytes 0)).toOption) =
    [some (.legacy .cmpEaxZero), some (.cmpImm32 .rax 0xff false),
     some (.addImm32 .rax 1 false), some (.logicalImm32 .band .rax 0xff false),
     some (.inc32 .rax false), some (.cmpImm64 .rax 0x80)] := by
  decide +kernel

private def fetchFailures (bytes : List Byte) : Bool :=
  let initial := valueEntry bytes .rsi 0
  (List.range bytes.length).all fun offset =>
    let address := BitVec.ofNat 64 offset
    let missing := { initial with memory := { initial.memory with
      read := fun query => if query = address then none else initial.memory.read query } }
    let denied := { initial with memory := { initial.memory with
      executable := fun query => if query = address then false else initial.memory.executable query } }
    [missing,denied].all fun state =>
      fault (Sequential.decodeAt state) (.inaccessibleInstruction address) &&
        [false,true].all (fun af => fault (Sequential.step af state) (.inaccessibleInstruction address))

/-- Every original prefix/opcode/ModRM/immediate byte needs both availability
and execute permission. No reconstructed instruction may bypass an actual fetch. -/
theorem all_sub_bytes_authenticated :
    ([[0x83,0xee,2], [0x40,0x83,0xec,0xff], [0x41,0x83,0xef,0x80]] : List (List Byte)).all
      fetchFailures = true := by
  decide +kernel

theorem all_cmp_bytes_authenticated :
    ([[0x83,0xfe,8], [0x40,0x83,0xfc,0x80], [0x41,0x83,0xff,0xff],
      [0x83,0xf8,0xff]] : List (List Byte)).all fetchFailures = true := by
  decide +kernel

/-- Required suffixes fault at their actual offset. Rejected groups/memory
forms stop before any immediate, and rejected R/X bits stop before ModRM. -/
theorem truncation_and_failure_order :
    rejects [] (.inaccessibleInstruction 0) = true ∧
    rejects [0x83] (.inaccessibleInstruction 1) = true ∧
    rejects [0x40] (.inaccessibleInstruction 1) = true ∧
    rejects [0x41,0x83] (.inaccessibleInstruction 2) = true ∧
    rejects [0x83,0xee] (.inaccessibleInstruction 2) = true ∧
    rejects [0x83,0xfe] (.inaccessibleInstruction 2) = true ∧
    rejects [0x83,0xf8] (.inaccessibleInstruction 2) = true ∧
    rejects [0x40,0x83,0xec] (.inaccessibleInstruction 3) = true ∧
    rejects [0x41,0x83,0xff] (.inaccessibleInstruction 3) = true ∧
    rejects [0x83,0xc8] = true ∧ rejects [0x83,0x28] = true ∧
    rejects [0x83,0x38] = true ∧ rejects [0x42,0x83] = true := by
  decide +kernel

end EDSL.Tests.Immediate32

#print axioms EDSL.X86.Sequential.signExtend8_toNat32
#print axioms EDSL.X86.Sequential.execute_subImm32_context
#print axioms EDSL.X86.Sequential.execute_subImm32_signed
#print axioms EDSL.X86.Sequential.execute_subImm32_flags
#print axioms EDSL.X86.Sequential.execute_cmpImm32_context
#print axioms EDSL.X86.Sequential.execute_cmpImm32_flags
#print axioms EDSL.X86.Sequential.decodeAt_transport
#print axioms EDSL.Tests.Immediate32.cmp_arbitrary_context
#print axioms EDSL.Tests.Immediate32.sub_arbitrary_context
#print axioms EDSL.Tests.Immediate32.caller_memory_transport
#print axioms EDSL.Tests.Immediate32.relocated_cmp_eax
#audit_edsl
