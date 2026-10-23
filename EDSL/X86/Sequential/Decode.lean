/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Model

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

def NopEncoding.length : NopEncoding → Nat
  | .one => 1 | .two => 2 | .three => 3 | .four => 4 | .five => 5 | .six => 6 | .nine => 9 | .fifteen => 15

def NopEncoding.bytes : NopEncoding → List Byte
  | .one => [0x90]
  | .two => [0x66, 0x90]
  | .three => [0x0f, 0x1f, 0x00]
  | .four => [0x0f, 0x1f, 0x40, 0x00]
  | .five => [0x0f, 0x1f, 0x44, 0x00, 0x00]
  | .six => [0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]
  | .nine => [0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]
  | .fifteen => [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84,
      0x00, 0x00, 0x00, 0x00, 0x00]

@[simp] theorem NopEncoding.bytes_length (encoding : NopEncoding) :
    encoding.bytes.length = encoding.length := by cases encoding <;> rfl

def Instruction.length : Instruction → Nat
  | .logicalReg32 _ _ _ prefixed | .test32 _ _ prefixed | .cmp32 _ _ prefixed
  | .cmpReg8 _ _ prefixed | .subReg32 _ _ prefixed | .negReg32 _ prefixed => if prefixed then 3 else 2
  | .movzxReg8 _ _ prefixed => if prefixed then 4 else 3
  | .movzxMem8 _ address prefixed => (if prefixed then 4 else 3) + address.suffixBytes
  | .cmpMemImm8 address _ => 3 + address.suffixBytes
  | .cmpMemReg8 address _ | .cmpMemReg32 address _ => 2 + address.suffixBytes
  | .cmpRegMem8 _ address prefixed => (if prefixed then 3 else 2) + address.suffixBytes
  | .movSignImm32 _ _ => 7
  | .setcc _ _ prefixed => if prefixed then 4 else 3
  | .movImm8 _ _ prefixed => if prefixed then 3 else 2
  | .cmovReg32 _ _ _ prefixed => if prefixed then 4 else 3
  | .endbr64IbtDisabled => 4
  | .nop encoding => encoding.length
  | .legacy (.leaEaxRdiDisp8 _) | .legacy (.leaEaxRaxDisp8 _) | .legacy .cmpEaxZero => 3
  | .legacy .fetchAddEaxRdi => 4
  | .legacy (.mov32 _ _) => 5
  | .legacy .ret => 1
  | .legacy _ => 2
  | .xorSelf32 _ | .movReg32 _ _ | .xchgRax64 _ | .je _ | .jcc _ _ | .jmp _ => 2
  | .movReg64 _ _ | .addReg64 _ _ | .logicalReg64 _ _ _ | .xchgReg64 _ _ | .test64 _ _ | .cmp64 _ _
  | .inc64 _ | .dec64 _ | .bswapReg64 _ | .shrOne64 _ | .rolCL64 _ => 3
  | .addMem32 _ address | .loadMem32 _ address | .storeMem32 address _ => 2 + address.suffixBytes
  | .lea64 _ address | .loadMem64 _ address | .addMem64 _ address | .storeMem64 address _ =>
    3 + address.suffixBytes
  | .shiftRightImm32 _ _ _ prefixed | .logicalImm32 _ _ _ prefixed | .addImm32 _ _ prefixed => if prefixed then 4 else 3
  | .inc32 _ prefixed => if prefixed then 3 else 2
  | .imulReg64 _ _ | .cmpImm64 _ _ | .addImm64 _ _ | .cmovReg64 _ _ _ => 4

def Instruction.isNew : Instruction → Bool
  | .legacy _ => false
  | _ => true

/-- Only the eight registers encodable without REX extensions. -/
def lowRegister (code : Fin 8) : Register :=
  match code.val with
  | 0 => .rax | 1 => .rcx | 2 => .rdx | 3 => .rbx
  | 4 => .rsp | 5 => .rbp | 6 => .rsi | _ => .rdi

def highRegister (code : Fin 8) : Register :=
  match code.val with
  | 0 => .r8 | 1 => .r9 | 2 => .r10 | 3 => .r11
  | 4 => .r12 | 5 => .r13 | 6 => .r14 | _ => .r15

/-- One REX.W prefix. R and B extend register operands; X has no role in
register mode, while the encoded prefix still occupies one byte. -/
def rexWPrefix (rex : Byte) : Bool :=
  rex == 0x48 || rex == 0x49 || rex == 0x4a || rex == 0x4b ||
    rex == 0x4c || rex == 0x4d || rex == 0x4e || rex == 0x4f

/-- Exactly one REX prefix with W=0. R/B select register banks and X extends
a supported SIB index (and is ignored in register mode). No legacy prefixes. -/
def rex32Prefix (rex : Byte) : Bool :=
  rex == 0x40 || rex == 0x41 || rex == 0x42 || rex == 0x43 ||
    rex == 0x44 || rex == 0x45 || rex == 0x46 || rex == 0x47

@[simp] theorem rex32Prefix_eq_true (rex : Byte) : rex32Prefix rex = true ↔
    rex = 0x40#8 ∨ rex = 0x41#8 ∨ rex = 0x42#8 ∨ rex = 0x43#8 ∨
      rex = 0x44#8 ∨ rex = 0x45#8 ∨ rex = 0x46#8 ∨ rex = 0x47#8 := by
  simp only [rex32Prefix, Bool.or_eq_true, beq_iff_eq, or_assoc, BitVec.ofNat_eq_ofNat]

@[simp] theorem rexWPrefix_eq_true (rex : Byte) : rexWPrefix rex = true ↔
    rex = 0x48#8 ∨ rex = 0x49#8 ∨ rex = 0x4a#8 ∨ rex = 0x4b#8 ∨
      rex = 0x4c#8 ∨ rex = 0x4d#8 ∨ rex = 0x4e#8 ∨ rex = 0x4f#8 := by
  simp only [rexWPrefix, Bool.or_eq_true, beq_iff_eq, or_assoc, BitVec.ofNat_eq_ofNat]

def modRMReg (byte : Byte) : Register := lowRegister ⟨byte.toNat / 8 % 8, Nat.mod_lt _ (by decide)⟩
def modRMRM (byte : Byte) : Register := lowRegister ⟨byte.toNat % 8, Nat.mod_lt _ (by decide)⟩

def rexModRMReg (rex byte : Byte) : Register :=
  if rex.getLsbD 2 then highRegister ⟨byte.toNat / 8 % 8, Nat.mod_lt _ (by decide)⟩
  else modRMReg byte

def rexModRMRM (rex byte : Byte) : Register :=
  if rex.getLsbD 0 then highRegister ⟨byte.toNat % 8, Nat.mod_lt _ (by decide)⟩
  else modRMRM byte

def rexSIBIndex (rex sib : Byte) : Register :=
  if rex.getLsbD 1 then highRegister ⟨sib.toNat / 8 % 8, Nat.mod_lt _ (by decide)⟩
  else modRMReg sib

/-- B0..B7 opcode-register immediate byte forms, with no prefix or exactly
one 40/41 REX. The enclosing decoder authenticates opcode/prefix bytes. -/
def decodeMovImm8At (state : State) (opcode rex : Byte) (prefixed : Bool) :
    Except Error Instruction := do
  if opcode.toNat < 0xb0 ∨ 0xb7 < opcode.toNat then throw .unsupportedEncoding
  if prefixed ∧ rex ≠ 0x40 ∧ rex ≠ 0x41 then throw .unsupportedEncoding
  if !prefixed ∧ 4 ≤ opcode.toNat % 8 then throw .unsupportedEncoding
  let immediate ← fetchByte state.memory (state.rip + (if prefixed then 2 else 1))
  return .movImm8 (rexModRMRM rex opcode) immediate prefixed

/-- Continue after authenticated 0F, with no prefix or exactly one 40/41 REX.
All sixteen conditions are admitted. Only C0..C7 ModRM (mod=3, reg=0) is
reviewed; real nonzero-reg aliases reject conservatively. Memory destinations
and unprefixed AH/CH/DH/BH reject, without interpreting an address as a GPR. -/
def decodeSetccAt (state : State) (rex : Byte) (prefixed : Bool) :
    Except Error Instruction := do
  if prefixed ∧ rex ≠ 0x40 ∧ rex ≠ 0x41 then throw .unsupportedEncoding
  let opcode ← fetchByte state.memory (state.rip + (if prefixed then 2 else 1))
  if opcode.toNat < 0x90 ∨ 0x9f < opcode.toNat then throw .unsupportedEncoding
  let modrm ← fetchByte state.memory (state.rip + (if prefixed then 3 else 2))
  if modrm.toNat / 64 ≠ 3 ∨ modrm.toNat / 8 % 8 ≠ 0 then throw .unsupportedEncoding
  if !prefixed ∧ 4 ≤ modrm.toNat % 8 then throw .unsupportedEncoding
  return .setcc (Condition.ofNibble ⟨opcode.toNat % 16, Nat.mod_lt _ (by decide)⟩)
    (rexModRMRM rex modrm) prefixed

/-- Only register operands. CMP admits both opcode directions; TEST has
opcode 85 only. `rex=0` is used by the unprefixed caller. This helper assumes
the enclosing decoder has fetched/authenticated the supplied opcode and the
optional single non-W REX prefix. Only `decodeAt` authenticates full bytes. -/
def decodeCompare32At (state : State) (opcode rex : Byte) (prefixed : Bool) :
    Except Error Instruction := do
  if opcode ≠ 0x39 ∧ opcode ≠ 0x3b ∧ opcode ≠ 0x85 then throw .unsupportedEncoding
  let modrm ← fetchByte state.memory (state.rip + (if prefixed then 2 else 1))
  if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
  let rm := rexModRMRM rex modrm
  let reg := rexModRMReg rex modrm
  return if opcode = 0x85 then .test32 rm reg prefixed
    else if opcode = 0x39 then .cmp32 rm reg prefixed else .cmp32 reg rm prefixed

/-- Continue after an authenticated 0F opcode, with either no prefix or one
non-W REX. Every condition-opcode/ModRM byte is fetched; only mod=3 is admitted.
`rex=0` denotes the unprefixed path. This helper does not authenticate the
supplied prefix/opcode; `decodeAt` does that before calling it. -/
def decodeCmov32At (state : State) (rex : Byte) (prefixed : Bool) :
    Except Error Instruction := do
  let conditionOpcode ← fetchByte state.memory (state.rip + (if prefixed then 2 else 1))
  if conditionOpcode.toNat < 0x40 ∨ 0x4f < conditionOpcode.toNat then
    throw .unsupportedEncoding
  let modrm ← fetchByte state.memory (state.rip + (if prefixed then 3 else 2))
  if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
  return .cmovReg32
    (Condition.ofNibble ⟨conditionOpcode.toNat % 16, Nat.mod_lt _ (by decide)⟩)
    (rexModRMReg rex modrm) (rexModRMRM rex modrm) prefixed

/-- LOW8 register comparisons admit both opcode directions, with mod=3 only.
The prefix is authenticated by the caller. Unprefixed codes 4..7 are high-byte
registers, so both fields reject rather than being confused with SPL..DIL. -/
def decodeCmpReg8At (state : State) (opcode rex : Byte) (prefixed : Bool) :
    Except Error Instruction := do
  if opcode ≠ 0x38 ∧ opcode ≠ 0x3a then throw .unsupportedEncoding
  let modrm ← fetchByte state.memory (state.rip + (if prefixed then 2 else 1))
  if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
  if !prefixed ∧ (4 ≤ modrm.toNat / 8 % 8 ∨ 4 ≤ modrm.toNat % 8) then
    throw .unsupportedEncoding
  return if opcode = 0x38 then .cmpReg8 (rexModRMRM rex modrm) (rexModRMReg rex modrm) prefixed
    else .cmpReg8 (rexModRMReg rex modrm) (rexModRMRM rex modrm) prefixed

/-- Register-only LOW32 SUB in either opcode direction. Neither memory SUB
nor immediate SUB is admitted; the enclosing caller authenticates W=0. -/
def decodeSubReg32At (state : State) (opcode rex : Byte) (prefixed : Bool) :
    Except Error Instruction := do
  if opcode ≠ 0x29 ∧ opcode ≠ 0x2b then throw .unsupportedEncoding
  let modrm ← fetchByte state.memory (state.rip + (if prefixed then 2 else 1))
  if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
  return if opcode = 0x29 then .subReg32 (rexModRMRM rex modrm) (rexModRMReg rex modrm) prefixed
    else .subReg32 (rexModRMReg rex modrm) (rexModRMRM rex modrm) prefixed

/-- Register-only low32 XOR and OR in either direction. The caller authenticates
no prefix or one W=0 REX; R/B extend the two fields and X is ignored. Preserve
the historical unprefixed 31 self-XOR constructor exactly. -/
def decodeLogicalReg32At (state : State) (opcode rex : Byte) (prefixed : Bool) :
    Except Error Instruction := do
  if opcode ≠ 0x31 ∧ opcode ≠ 0x33 ∧ opcode ≠ 0x09 ∧ opcode ≠ 0x0b then
    throw .unsupportedEncoding
  let modrm ← fetchByte state.memory (state.rip + (if prefixed then 2 else 1))
  if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
  let rm := rexModRMRM rex modrm
  let reg := rexModRMReg rex modrm
  if !prefixed ∧ opcode = 0x31 ∧ rm = reg then return .xorSelf32 rm
  let operation := if opcode = 0x09 ∨ opcode = 0x0b then LogicalOp.bor else .bxor
  return if opcode = 0x31 ∨ opcode = 0x09 then .logicalReg32 operation rm reg prefixed
    else .logicalReg32 operation reg rm prefixed

/-- Continue after authenticated C1, with no prefix or exactly one W=0
REX. Only register mode /5 and /7 with a nonzero masked count are admitted.
REX.B extends the destination; REX.R does not extend an opcode group selector,
and X is ignored in register mode. Every immediate byte is actually fetched. -/
def decodeShiftRightImm32At (state : State) (rex : Byte) (prefixed : Bool) :
    Except Error Instruction := do
  if prefixed ∧ rex32Prefix rex ≠ true then throw .unsupportedEncoding
  let modrm ← fetchByte state.memory (state.rip + (if prefixed then 2 else 1))
  let group := modrm.toNat / 8 % 8
  if modrm.toNat / 64 ≠ 3 ∨ (group ≠ 5 ∧ group ≠ 7) then throw .unsupportedEncoding
  let immediate ← fetchByte state.memory (state.rip + (if prefixed then 3 else 2))
  if immediate.toNat % 32 = 0 then throw .unsupportedEncoding
  return .shiftRightImm32 (if group = 5 then .logical else .arithmetic)
    (rexModRMRM (if prefixed then rex else 0) modrm) immediate prefixed

/-- Continue after an authenticated F7 opcode. Only /3, mod=3 and no prefix
or exactly 40/41 are supported. The caller authenticates prefix/opcode;
REX.B selects the destination bank. No memory or other width is reinterpreted.
Intel SDM Vol.2 NEG (F7 /3). -/
def decodeNegReg32At (state : State) (rex : Byte) (prefixed : Bool) :
    Except Error Instruction := do
  if prefixed ∧ rex ≠ 0x40 ∧ rex ≠ 0x41 then throw .unsupportedEncoding
  let modrm ← fetchByte state.memory (state.rip + (if prefixed then 2 else 1))
  if modrm.toNat / 64 ≠ 3 ∨ modrm.toNat / 8 % 8 ≠ 3 then throw .unsupportedEncoding
  return .negReg32 (rexModRMRM (if prefixed then rex else 0) modrm) prefixed

/-- Register-only low32 group operations: 83 /0 ib (ADD), 83 /4 ib (AND)
or FF /0 (INC), with no prefix
or one canonical 40/41. The caller authenticates opcode/prefix, and this helper
fetches the full register ModRM and optional immediate. No memory or other
group operation is lowered to a counter operation. -/
def decodeCounter32At (state : State) (opcode rex : Byte) (prefixed : Bool) :
    Except Error Instruction := do
  if opcode ≠ 0x83 ∧ opcode ≠ 0xff then throw .unsupportedEncoding
  if prefixed ∧ rex ≠ 0x40 ∧ rex ≠ 0x41 then throw .unsupportedEncoding
  let modrm ← fetchByte state.memory (state.rip + (if prefixed then 2 else 1))
  if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
  let destination := rexModRMRM (if prefixed then rex else 0) modrm
  if opcode = 0x83 ∧ modrm.toNat / 8 % 8 = 4 then
    return .logicalImm32 .band destination
      (← fetchByte state.memory (state.rip + (if prefixed then 3 else 2))) prefixed
  else if modrm.toNat / 8 % 8 ≠ 0 then throw .unsupportedEncoding
  else if opcode = 0x83 then
    return .addImm32 destination
      (← fetchByte state.memory (state.rip + (if prefixed then 3 else 2))) prefixed
  else return .inc32 destination prefixed

/-- Mod01 addressing with an authenticated REX.W and ModRM. Every base is
real, including RBP/R13. A no-index SIB remains distinct from a plain address;
X=1 turns encoded index4 into R12. All suffix bytes are permission-checked.
This helper does not authenticate its supplied prefix or ModRM. -/
def decodeDisp8AddressAt (state : State) (rex modrm : Byte) : Except Error Address := do
  if modrm.toNat / 64 ≠ 1 then throw .unsupportedEncoding
  if modrm.toNat % 8 = 4 then
    let sib ← fetchByte state.memory (state.rip + 3)
    let index := if sib.toNat / 8 % 8 = 4 ∧ rex.getLsbD 1 = false then none
      else some (rexSIBIndex rex sib)
    return .sibDisp8 (rexModRMRM rex sib) index
      ⟨sib.toNat / 64, by have := sib.isLt; omega⟩
      (← fetchByte state.memory (state.rip + 4))
  else
    let displacement ← fetchByte state.memory (state.rip + 3)
    return .baseDisp8 (rexModRMRM rex modrm) displacement

/-- MOVZX's mod00 full64 addresses, with a SIB at offset 3/4 depending on
prefix presence. REX.B/X extend real bases/indices. Encoded base5 is absent
even with B=1; encoded index4 denotes R12 only with X=1. No displacement,
RIP-relative, missing-base/index or address-size override is modeled. -/
def decodeMovzxAddressAt (state : State) (rex modrm : Byte) (prefixed : Bool) :
    Except Error Address := do
  if modrm.toNat / 64 ≠ 0 then throw .unsupportedEncoding
  if modrm.toNat % 8 = 4 then
    let sib ← fetchByte state.memory (state.rip + (if prefixed then 4 else 3))
    if (sib.toNat / 8 % 8 = 4 ∧ rex.getLsbD 1 = false) ∨ sib.toNat % 8 = 5 then
      throw .unsupportedEncoding
    return .indexed (rexModRMRM rex sib) (rexSIBIndex rex sib)
      ⟨sib.toNat / 64, by have := sib.isLt; omega⟩
  else if modrm.toNat % 8 = 5 then throw .unsupportedEncoding
  else return .base (rexModRMRM rex modrm)

/-- Continue after authenticated 0F B6 with no prefix or one W=0 REX. The
destination is r32; an unprefixed byte source4..7 would mean AH..BH and rejects.
The memory variant fetches the complete supported ModRM/SIB encoding. -/
def decodeMovzx8At (state : State) (rex : Byte) (prefixed : Bool) :
    Except Error Instruction := do
  let modrm ← fetchByte state.memory (state.rip + (if prefixed then 3 else 2))
  if modrm.toNat / 64 = 3 then
    if !prefixed ∧ 4 ≤ modrm.toNat % 8 then throw .unsupportedEncoding
    return .movzxReg8 (rexModRMReg rex modrm) (rexModRMRM rex modrm) prefixed
  else
    return .movzxMem8 (rexModRMReg rex modrm)
      (← decodeMovzxAddressAt state rex modrm prefixed) prefixed

/-- Dispatch the authenticated 0F lead byte, preserving CMOV32 while adding
MOVZX8. This helper does not authenticate its supplied prefix or lead byte. -/
def decode0FREX32At (state : State) (rex : Byte) : Except Error Instruction := do
  let second ← fetchByte state.memory (state.rip + 2)
  if second = 0xb6 then decodeMovzx8At state rex true
  else if 0x90 ≤ second.toNat ∧ second.toNat ≤ 0x9f then decodeSetccAt state rex true
  else decodeCmov32At state rex true

/-- Fetch and check a fixed suffix in order. Missing/nonexecutable bytes retain
their precise fetch fault; a differing fetched byte is an unsupported encoding. -/
def fetchExactAt (state : State) (offset : Nat) : List Byte → Except Error Unit
  | [] => .ok ()
  | expected :: rest => do
    let actual ← fetchByte state.memory (state.rip + BitVec.ofNat 64 offset)
    if actual = expected then fetchExactAt state (offset + 1) rest
    else throw .unsupportedEncoding

/-- Decode the suffix after the enclosing decoder's successful first-byte
fetch: `opcode` must be that authenticated byte. Every required suffix byte,
including ModRM/SIB/displacement, is fetched here. This helper alone does not
authenticate its supplied first byte. Other /0 operands, nonzero displacements,
unlisted repeated prefixes, ENDBR32 and reserved hint-NOP aliases are unsupported.
The sole repeated-prefix form is the exact fifteen-byte assembler padding. -/
def decodePaddingAt (state : State) (opcode : Byte) : Except Error Instruction := do
  if opcode = 0x90 then return .nop .one
  let second ← fetchByte state.memory (state.rip + 1)
  if opcode = 0x66 then
    if second = 0x90 then return .nop .two
    if second = 0x66 then
      fetchExactAt state 2 [0x66, 0x66, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0]
      return .nop .fifteen
    if second ≠ 0x0f then throw .unsupportedEncoding
    let third ← fetchByte state.memory (state.rip + 2)
    if third ≠ 0x1f then throw .unsupportedEncoding
    let modrm ← fetchByte state.memory (state.rip + 3)
    if modrm = 0x44 then
      fetchExactAt state 4 [0, 0]
      return .nop .six
    else if modrm = 0x84 then
      fetchExactAt state 4 [0, 0, 0, 0, 0]
      return .nop .nine
    else throw .unsupportedEncoding
  else if opcode = 0xf3 then
    if second ≠ 0x0f then throw .unsupportedEncoding
    let third ← fetchByte state.memory (state.rip + 2)
    if third ≠ 0x1e then throw .unsupportedEncoding
    let fourth ← fetchByte state.memory (state.rip + 3)
    if fourth = 0xfa then return .endbr64IbtDisabled else throw .unsupportedEncoding
  else if opcode = 0x0f then
    if second ≠ 0x1f then throw .unsupportedEncoding
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm = 0x00 then return .nop .three
    else if modrm = 0x40 then
      let displacement ← fetchByte state.memory (state.rip + 3)
      if displacement = 0x00 then return .nop .four else throw .unsupportedEncoding
    else if modrm = 0x44 then
      let sib ← fetchByte state.memory (state.rip + 3)
      if sib ≠ 0x00 then throw .unsupportedEncoding
      let displacement ← fetchByte state.memory (state.rip + 4)
      if displacement = 0x00 then return .nop .five else throw .unsupportedEncoding
    else throw .unsupportedEncoding
  else throw .unsupportedEncoding

/-- Unprefixed 0F shares a lead byte with hint NOP and legacy SYSCALL.
Preserve NOP's suffix decoder and dispatch MOVZX8 or register CMOV32. -/
def decode0F32At (state : State) : Except Error Instruction := do
  let second ← fetchByte state.memory (state.rip + 1)
  if second = 0x1f then decodePaddingAt state 0x0f
  else if second = 0xb6 then decodeMovzx8At state 0 false
  else if 0x90 ≤ second.toNat ∧ second.toNat ≤ 0x9f then decodeSetccAt state 0 false
  else decodeCmov32At state 0 false

/-- Decode a rel8 conditional-branch operand after its opcode was authenticated
and classified by the enclosing decoder. This helper alone does not check it. -/
def decodeJccAt (state : State) (opcode : Byte) : Except Error Instruction := do
  let displacement ← fetchByte state.memory (state.rip + 1)
  return .jcc (Condition.ofNibble ⟨opcode.toNat % 16, Nat.mod_lt _ (by decide)⟩)
    displacement

/-- The common mod=00 address subset. SIB has a real base and index; prefixes,
displacements, RIP-relative and absent-base/index forms remain unsupported. -/
def decodeAddressAt (state : State) (modrm : Byte) : Except Error Address := do
  if modrm.toNat / 64 ≠ 0 then throw .unsupportedEncoding
  if modrm.toNat % 8 = 4 then
    let sib ← fetchByte state.memory (state.rip + 2)
    if sib.toNat / 8 % 8 = 4 ∨ sib.toNat % 8 = 5 then throw .unsupportedEncoding
    return .indexed (modRMRM sib) (modRMReg sib)
      ⟨sib.toNat / 64, by have := sib.isLt; omega⟩
  else if modrm.toNat % 8 = 5 then throw .unsupportedEncoding
  else return .base (modRMRM modrm)

/-- Continue after authenticated opcode 80. Only /7 and the existing unprefixed
mod=00 address subset are admitted. The immediate follows the complete address;
register operands, displacements, absent bases/indices and prefixes stay unsupported. -/
def decodeCmpMemImm8At (state : State) : Except Error Instruction := do
  let modrm ← fetchByte state.memory (state.rip + 1)
  if modrm.toNat / 8 % 8 ≠ 7 then throw .unsupportedEncoding
  let address ← decodeAddressAt state modrm
  let immediate ← fetchByte state.memory (state.rip + BitVec.ofNat 64 (2 + address.suffixBytes))
  return .cmpMemImm8 address immediate

/-- Continue after authenticated unprefixed 38/39. Only the existing mod=00
address subset is admitted. Without REX, byte source codes 4..7 denote
AH/CH/DH/BH, so they are rejected instead of being interpreted as low8 GPRs.
Intel SDM Vol.2 CMP (38/39 /r): memory is the left subtraction operand. -/
def decodeCmpMemRegAt (state : State) (byteWidth : Bool) : Except Error Instruction := do
  let modrm ← fetchByte state.memory (state.rip + 1)
  if byteWidth ∧ 4 ≤ modrm.toNat / 8 % 8 then throw .unsupportedEncoding
  let address ← decodeAddressAt state modrm
  return if byteWidth then .cmpMemReg8 address (modRMReg modrm)
    else .cmpMemReg32 address (modRMReg modrm)

/-- Continue after authenticated REX.W C7. This conservative register subset
admits prefixes 48/49 only (R=X=0), mod=3 and /0. B selects the destination
bank. Every immediate byte is fetched in order; memory C7 is unsupported.
Intel SDM Vol.2 MOV: imm32 is sign-extended to 64 bits and flags are unchanged.
https://cdrdv2-public.intel.com/835757/325383-sdm-vol-2abcd.pdf -/
def decodeMovSignImm32At (state : State) (rex : Byte) : Except Error Instruction := do
  if rex ≠ 0x48 ∧ rex ≠ 0x49 then throw .unsupportedEncoding
  let modrm ← fetchByte state.memory (state.rip + 2)
  if modrm.toNat / 64 ≠ 3 ∨ modrm.toNat / 8 % 8 ≠ 0 then throw .unsupportedEncoding
  let b0 ← fetchByte state.memory (state.rip + 3)
  let b1 ← fetchByte state.memory (state.rip + 4)
  let b2 ← fetchByte state.memory (state.rip + 5)
  let b3 ← fetchByte state.memory (state.rip + 6)
  return .movSignImm32 (rexModRMRM rex modrm) (joinDWord b0 b1 b2 b3)

/-- Mod=00 operands after a one-byte REX and one-byte opcode. B extends the real base and X extends the SIB
index. Encoded base=5 still denotes a missing/RIP-relative base regardless
of B. Index=4 is missing only when X=0; X=1 selects the real R12 index. -/
def decodeQWordAddressAt (state : State) (rex modrm : Byte) : Except Error Address := do
  if modrm.toNat / 64 ≠ 0 then throw .unsupportedEncoding
  if modrm.toNat % 8 = 4 then
    let sib ← fetchByte state.memory (state.rip + 3)
    if (sib.toNat / 8 % 8 = 4 ∧ rex.getLsbD 1 = false) ∨ sib.toNat % 8 = 5 then
      throw .unsupportedEncoding
    return .indexed (rexModRMRM rex sib) (rexSIBIndex rex sib)
      ⟨sib.toNat / 64, by have := sib.isLt; omega⟩
  else if modrm.toNat % 8 = 5 then throw .unsupportedEncoding
  else return .base (rexModRMRM rex modrm)

/-- Continue after authenticated 3A, with no prefix or one non-W REX. Only
mod00 memory addresses from the existing helpers are admitted. Unprefixed
reg4..7 mean AH..BH and reject. This helper does not authenticate its supplied
prefix/opcode; `decodeAt` does. No register operand is fabricated from memory. -/
def decodeCmpRegMem8At (state : State) (rex : Byte) (prefixed : Bool) :
    Except Error Instruction := do
  if prefixed ∧ rex32Prefix rex = false then throw .unsupportedEncoding
  let modrm ← fetchByte state.memory (state.rip + (if prefixed then 2 else 1))
  if !prefixed ∧ 4 ≤ modrm.toNat / 8 % 8 then throw .unsupportedEncoding
  let address ← if prefixed then decodeQWordAddressAt state rex modrm
    else decodeAddressAt state modrm
  return .cmpRegMem8 (rexModRMReg (if prefixed then rex else 0) modrm) address prefixed

/-- Complete the unprefixed low-bank immediate32 forms not recognized by the
legacy decoder (B9/BB/BC/BD). The enclosing decoder authenticates the opcode;
all four immediate bytes are executable fetches. Semantics remain the shared
legacy MOV32 operation, including zero extension and unchanged flags. -/
def decodeMovImm32At (state : State) (opcode : Byte) : Except Error Instruction := do
  let b0 ← fetchByte state.memory (state.rip + 1)
  let b1 ← fetchByte state.memory (state.rip + 2)
  let b2 ← fetchByte state.memory (state.rip + 3)
  let b3 ← fetchByte state.memory (state.rip + 4)
  return .legacy (.mov32 (lowRegister ⟨opcode.toNat % 8, Nat.mod_lt _ (by decide)⟩)
    (joinDWord b0 b1 b2 b3))

/-- Continue after the enclosing decoder has recognized one non-W REX prefix.
The operation is fetched once at offset one. Each selected family retains its
own operand and prefix restrictions; this helper does not authenticate `rex`.
Separating prefix dispatch keeps the main decoder's elaboration bounded. -/
def decodeREX32At (state : State) (rex : Byte) : Except Error Instruction := do
  let operation ← fetchByte state.memory (state.rip + 1)
  if 0xb0 ≤ operation.toNat ∧ operation.toNat ≤ 0xb7 then decodeMovImm8At state operation rex true
  else if operation = 0x0f then decode0FREX32At state rex
  else if operation = 0x3a then
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 = 0 then decodeCmpRegMem8At state rex true
    else decodeCmpReg8At state operation rex true
  else if operation = 0x38 then decodeCmpReg8At state operation rex true
  else if operation = 0x29 ∨ operation = 0x2b then decodeSubReg32At state operation rex true
  else if operation = 0x31 ∨ operation = 0x33 ∨ operation = 0x09 ∨ operation = 0x0b then decodeLogicalReg32At state operation rex true
  else if operation = 0xc1 then decodeShiftRightImm32At state rex true
  else if operation = 0xf7 then decodeNegReg32At state rex true
  else if operation = 0x83 ∨ operation = 0xff then decodeCounter32At state operation rex true
  else decodeCompare32At state operation rex true

/-- Continue after the enclosing decoder has recognized one REX.W prefix.
All addressing restrictions, ADD operand direction and register-only CMOV
checks remain explicit. -/
def decodeREXWAt (state : State) (opcode : Byte) : Except Error Instruction := do
  let operation ← fetchByte state.memory (state.rip + 1)
  if operation = 0xd3 then
    if opcode ≠ 0x48 ∧ opcode ≠ 0x49 then throw .unsupportedEncoding
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 ≠ 3 ∨ modrm.toNat / 8 % 8 ≠ 0 then throw .unsupportedEncoding
    return .rolCL64 (rexModRMRM opcode modrm)
  else if operation = 0xd1 then
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 ≠ 3 ∨ modrm.toNat / 8 % 8 ≠ 5 then throw .unsupportedEncoding
    return .shrOne64 (rexModRMRM opcode modrm)
  else if operation = 0xc7 then decodeMovSignImm32At state opcode
  else if operation = 0x0f then
    let conditionOpcode ← fetchByte state.memory (state.rip + 2)
    if 0xc8 ≤ conditionOpcode.toNat ∧ conditionOpcode.toNat ≤ 0xcf then
      if opcode ≠ 0x48 ∧ opcode ≠ 0x49 then throw .unsupportedEncoding
      return .bswapReg64 (rexModRMRM opcode conditionOpcode)
    if conditionOpcode = 0xaf then
      let modrm ← fetchByte state.memory (state.rip + 3)
      if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
      return .imulReg64 (rexModRMReg opcode modrm) (rexModRMRM opcode modrm)
    if conditionOpcode.toNat < 0x40 ∨ 0x4f < conditionOpcode.toNat then
      throw .unsupportedEncoding
    let modrm ← fetchByte state.memory (state.rip + 3)
    if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
    return .cmovReg64
      (Condition.ofNibble ⟨conditionOpcode.toNat % 16, Nat.mod_lt _ (by decide)⟩)
      (rexModRMReg opcode modrm) (rexModRMRM opcode modrm)
  else if operation = 0x87 then
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
    return .xchgReg64 (rexModRMRM opcode modrm) (rexModRMReg opcode modrm)
  else if 0x90 ≤ operation.toNat ∧ operation.toNat ≤ 0x97 then
    return .xchgRax64 (rexModRMRM opcode operation)
  else if operation = 0x89 ∨ operation = 0x8b then
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 = 3 then
      return if operation = 0x89 then .movReg64 (rexModRMRM opcode modrm) (rexModRMReg opcode modrm)
        else .movReg64 (rexModRMReg opcode modrm) (rexModRMRM opcode modrm)
    else
      let address ← decodeQWordAddressAt state opcode modrm
      return if operation = 0x89 then .storeMem64 address (rexModRMReg opcode modrm)
        else .loadMem64 (rexModRMReg opcode modrm) address
  else if operation = 0x8d then
    let modrm ← fetchByte state.memory (state.rip + 2)
    return .lea64 (rexModRMReg opcode modrm)
      (← if modrm.toNat / 64 = 1 then decodeDisp8AddressAt state opcode modrm
          else decodeQWordAddressAt state opcode modrm)
  else if operation = 0x01 ∨ operation = 0x03 then
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 = 3 then
      return if operation = 0x01 then .addReg64 (rexModRMRM opcode modrm) (rexModRMReg opcode modrm)
        else .addReg64 (rexModRMReg opcode modrm) (rexModRMRM opcode modrm)
    else if operation = 0x03 then
      return .addMem64 (rexModRMReg opcode modrm) (← decodeQWordAddressAt state opcode modrm)
    else throw .unsupportedEncoding
  else if operation = 0x21 ∨ operation = 0x23 ∨ operation = 0x09 ∨
      operation = 0x0b ∨ operation = 0x31 ∨ operation = 0x33 then
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
    let logical := if operation = 0x21 ∨ operation = 0x23 then LogicalOp.band
      else if operation = 0x09 ∨ operation = 0x0b then LogicalOp.bor else LogicalOp.bxor
    return if operation = 0x21 ∨ operation = 0x09 ∨ operation = 0x31 then
      .logicalReg64 logical (rexModRMRM opcode modrm) (rexModRMReg opcode modrm)
      else .logicalReg64 logical (rexModRMReg opcode modrm) (rexModRMRM opcode modrm)
  else if operation = 0x83 then
    if opcode ≠ 0x48 ∧ opcode ≠ 0x49 then throw .unsupportedEncoding
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
    if modrm.toNat / 8 % 8 = 7 then
      return .cmpImm64 (rexModRMRM opcode modrm) (← fetchByte state.memory (state.rip + 3))
    else if opcode = 0x48 ∧ modrm.toNat / 8 % 8 = 0 then
      return .addImm64 (modRMRM modrm) (← fetchByte state.memory (state.rip + 3))
    else throw .unsupportedEncoding
  else if opcode ≠ 0x48 then throw .unsupportedEncoding
  else if operation = 0x85 ∨ operation = 0x39 then
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
    return if operation = 0x85 then .test64 (modRMRM modrm) (modRMReg modrm)
      else .cmp64 (modRMRM modrm) (modRMReg modrm)
  else if operation = 0xff then
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
    if modrm.toNat / 8 % 8 = 0 then return .inc64 (modRMRM modrm)
    else if modrm.toNat / 8 % 8 = 1 then return .dec64 (modRMRM modrm)
    else throw .unsupportedEncoding
  else throw .unsupportedEncoding

/-- Remaining unprefixed memory and short-branch dispatch, after the enclosing
legacy-first decoder has authenticated and classified the first byte. This
helper retains exact suffix fetches and the caller's fallback error. -/
def decodeTailAt (state : State) (opcode : Byte) (oldError : Error) : Except Error Instruction := do
  if opcode = 0x03 then
    let modrm ← fetchByte state.memory (state.rip + 1)
    return .addMem32 (modRMReg modrm) (← decodeAddressAt state modrm)
  else if opcode = 0x89 ∨ opcode = 0x8b then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm.toNat / 64 = 3 then
      return if opcode = 0x89 then .movReg32 (modRMRM modrm) (modRMReg modrm)
        else .movReg32 (modRMReg modrm) (modRMRM modrm)
    else
      let address ← decodeAddressAt state modrm
      return if opcode = 0x89 then .storeMem32 address (modRMReg modrm)
        else .loadMem32 (modRMReg modrm) address
  else if opcode = 0x74 then
    return .je (← fetchByte state.memory (state.rip + 1))
  else if 0x70 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x7f ∧ opcode ≠ 0x75 then
    decodeJccAt state opcode
  else if opcode = 0xeb then
    return .jmp (← fetchByte state.memory (state.rip + 1))
  else throw oldError

/-- NEW subset only. SHR64 by one admits REX.W D1 /5, mod=3, length three.
REX.B extends the destination; REX.R is ignored for the opcode-extension field
and REX.X is ignored without a SIB. No other counts, widths, group selectors,
memory or extra prefixes are admitted by this family.
ROL64 by CL admits exactly 48/49 D3 /0, mod=3, length three. B extends the
destination; R/X aliases, other count sources, widths and memory forms reject.
MOV64, LEA64, ADD64, register AND/OR/XOR64, register CMOV64 and register XCHG64 admit
one REX.W prefix 48..4F, including R/B and the SIB index extension X. Register
ADD, AND/OR/XOR and CMOV ignore X. Logical instructions admit both opcode
directions with mod=3 only; memory operands and immediate forms are unsupported.
Opcode 03 additionally admits a mod=00 memory source;
opcode 01 memory destinations remain unsupported. CMOV accepts the sixteen
0F 40..4F condition codes, with R extending its destination and B its source.
Memory CMOV needs an unconditional operand-read contract and is unsupported.
LEA uses the existing mod=00 address subset or generic mod=01 signed disp8
plain/SIB forms, including no-index SIBs, to compute a value without a data
access. Memory families retain their existing mod=00 restrictions. XCHG's short form uses B to
extend its opcode register; unused R/X bits are ignored. Other 64-bit families
retain exact prefix 48.
Register CMP32 (39/3B), TEST32 (85), and CMOV32 (0F40..4F) accept no prefix
or one non-W REX40..47; R/B extend operands and X is ignored, with mod=3 only.
CMOV32 clears the high destination half even when its condition is false.
Memory-left CMP admits unprefixed 38/39 /r with `decodeAddressAt` operands;
38 admits only AL/CL/DL/BL sources. Byte-immediate CMP admits unprefixed 80 /7 ib.
Register CMP8 (38/3A), SUB32 (29/2B), and MOVZX r32,r/m8 (0F B6) accept no
prefix or one W=0 REX40..47. Byte registers4..7 require REX; unprefixed high-byte
registers reject. Memory MOVZX uses mod00 full64 R/B/X addressing and DATA1;
memory SUB and prefixed memory-left CMP remain unsupported. Memory-right CMP
uses 3A mod00, unprefixed or one non-W REX, with prestate LOW8 register left.
Unprefixed B9/BB/BC/BD complete the low-bank MOV32 immediate family through
the existing legacy MOV32 semantics; legacy B8/BA/BE/BF successes retain priority.
Register-only
MOV sign-extended imm32 admits 48/49 C7 /0 id, length seven; other C7 forms reject.
Register-only ADD32 admits 83 /0 ib and INC32 admits FF /0, unprefixed or with
exactly one 40/41 REX. ADD sign-extends the immediate at width32; both clear
the destination upper32 and INC preserves incoming CF. AND32 additionally admits
83 /4 ib with the same prefix restriction and a signed imm8. XOR32 admits
31/33 /r and OR32 admits 09/0B /r, mod=3, unprefixed or with one W=0 REX40..47 (R/B extend operands;
X is ignored). SHR32/SAR32 admit C1 /5 or /7 ib, mod=3, with the same W=0
REX scope; R/X are ignored and B extends the destination. Masked counts zero
reject; counts 1..31 retain independent AF and (for counts >1) OF. CMP64 admits 48/49 83 /7 ib, mod=3, with sign extension to 64.
Other group selectors, memory operands and unused group-1 REX.R/X bits reject.
Exact ENDBR64 is
interpreted under the named IBT-disabled target profile. NOPs are restricted
to `NopEncoding.bytes`, with complete instruction fetches and no operand read.
Register ModRM for legacy self-XOR32/TEST/CMP/INC/DEC/ADD-immediate, unprefixed MOV32, and mod=00
ordinary ADD/MOV-memory addresses.
Short conditional branches admit the unprefixed 70..7F rel8 forms. The
legacy-first decoder retains 75 as JNZ, and 74 retains the existing JE API.
SIB allows all scales, no missing index (index=4), no missing base (base=5),
and no displacement. A plain base=4 must use SIB; base=5 would be RIP-relative
and is rejected. Unsupported forms never fall through to weaker addressing. -/
def decodeNewAt (state : State) (oldError : Error) : Except Error Instruction := do
  let opcode ← fetchByte state.memory state.rip
  if 0xb0 ≤ opcode.toNat ∧ opcode.toNat ≤ 0xb7 then decodeMovImm8At state opcode 0 false
  else if opcode = 0xb9 ∨ opcode = 0xbb ∨ opcode = 0xbc ∨ opcode = 0xbd then
    decodeMovImm32At state opcode
  else if opcode = 0x80 then decodeCmpMemImm8At state
  else if opcode = 0x38 then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm.toNat / 64 = 0 then decodeCmpMemRegAt state true
    else decodeCmpReg8At state opcode 0 false
  else if opcode = 0x3a then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm.toNat / 64 = 0 then decodeCmpRegMem8At state 0 false
    else decodeCmpReg8At state opcode 0 false
  else if opcode = 0x29 ∨ opcode = 0x2b then decodeSubReg32At state opcode 0 false
  else if opcode = 0x31 ∨ opcode = 0x33 ∨ opcode = 0x09 ∨ opcode = 0x0b then decodeLogicalReg32At state opcode 0 false
  else if opcode = 0xc1 then decodeShiftRightImm32At state 0 false
  else if opcode = 0xf7 then decodeNegReg32At state 0 false
  else if opcode = 0x83 ∨ opcode = 0xff then decodeCounter32At state opcode 0 false
  else if opcode = 0x39 then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm.toNat / 64 = 0 then decodeCmpMemRegAt state false
    else decodeCompare32At state opcode 0 false
  else if opcode = 0x3b ∨ opcode = 0x85 then
    decodeCompare32At state opcode 0 false
  else if rex32Prefix opcode then decodeREX32At state opcode
  else if opcode = 0x0f then decode0F32At state
  else if opcode = 0x90 ∨ opcode = 0x66 ∨ opcode = 0xf3 then
    decodePaddingAt state opcode
  else if rexWPrefix opcode then
    decodeREXWAt state opcode
  else decodeTailAt state opcode oldError

/-- The legacy decoder is tried FIRST. Its every success embeds exactly; only
an error attempts the separate sequential subset. Unknown forms retain the
legacy error, while recognized new opcodes report their own precise failures. -/
def decodeAt (state : State) : Except Error Instruction :=
  match X86.decodeAt state with
  | .ok instruction => .ok (.legacy instruction)
  | .error fault => decodeNewAt state fault

theorem decodeAt_legacy {state : State} {instruction : X86.Instruction}
    (decoded : X86.decodeAt state = .ok instruction) :
    decodeAt state = .ok (.legacy instruction) := by
  simp only [decodeAt, decoded]

/-- Success preservation over an explicit fetch extent, without a premise on
failed fetches. In particular no following byte is needed after a final RET. -/
def SuccessfulFetchTransportWithin (extent : Nat) (source destination : State) : Prop :=
  ∀ offset, offset < extent → ∀ byte,
    fetchByte source.memory (source.rip + BitVec.ofNat 64 offset) = .ok byte →
    fetchByte destination.memory (destination.rip + BitVec.ofNat 64 offset) = .ok byte

/-- Strengthened shared API: all offsets 0..14 for the longest supported
instruction. The old nine-byte premise alone cannot transport NOP15. -/
abbrev SuccessfulFetchTransport := SuccessfulFetchTransportWithin 15

theorem SuccessfulFetchTransportWithin.restrict {small large : Nat} {source destination : State}
    (transport : SuccessfulFetchTransportWithin large source destination) (bound : small ≤ large) :
    SuccessfulFetchTransportWithin small source destination :=
  fun offset inside => transport offset (by omega)

theorem Instruction.length_pos (instruction : Instruction) : 0 < instruction.length := by
  cases instruction with
  | shiftRightImm32 _ _ _ prefixed | logicalReg32 _ _ _ prefixed | logicalImm32 _ _ _ prefixed
  | test32 _ _ prefixed | cmp32 _ _ prefixed | cmovReg32 _ _ _ prefixed
  | setcc _ _ prefixed | movImm8 _ _ prefixed
  | cmpReg8 _ _ prefixed | subReg32 _ _ prefixed | movzxReg8 _ _ prefixed | negReg32 _ prefixed
  | addImm32 _ _ prefixed | inc32 _ prefixed =>
    cases prefixed <;> simp [Instruction.length]
  | cmpRegMem8 _ address prefixed | movzxMem8 _ address prefixed => cases address <;> cases prefixed <;> simp [Instruction.length, Address.suffixBytes]
  | endbr64IbtDisabled => decide
  | nop encoding => cases encoding <;> decide
  | legacy old => cases old <;> simp [Instruction.length]
  | addMem32 destination address | loadMem32 destination address | storeMem32 address destination
  | cmpMemImm8 address immediate
  | cmpMemReg8 address source | cmpMemReg32 address source
  | lea64 destination address | loadMem64 destination address | addMem64 destination address
  | storeMem64 address destination =>
    cases address <;> simp [Instruction.length, Address.suffixBytes]
  | xorSelf32 _ | movReg32 _ _ | movReg64 _ _ | cmovReg64 _ _ _ | addReg64 _ _ | logicalReg64 _ _ _ | xchgReg64 _ _ | xchgRax64 _
  | imulReg64 _ _ | test64 _ _ | cmp64 _ _ | cmpImm64 _ _ | addImm64 _ _ | movSignImm32 _ _
  | inc64 _ | dec64 _ | bswapReg64 _ | shrOne64 _ | rolCL64 _ | je _ | jcc _ _ | jmp _ => simp [Instruction.length]

theorem Instruction.length_le_fifteen (instruction : Instruction) : instruction.length ≤ 15 := by
  cases instruction with
  | shiftRightImm32 _ _ _ prefixed | logicalReg32 _ _ _ prefixed | logicalImm32 _ _ _ prefixed
  | test32 _ _ prefixed | cmp32 _ _ prefixed | cmovReg32 _ _ _ prefixed
  | setcc _ _ prefixed | movImm8 _ _ prefixed
  | cmpReg8 _ _ prefixed | subReg32 _ _ prefixed | movzxReg8 _ _ prefixed | negReg32 _ prefixed
  | addImm32 _ _ prefixed | inc32 _ prefixed =>
    cases prefixed <;> simp [Instruction.length]
  | cmpRegMem8 _ address prefixed | movzxMem8 _ address prefixed => cases address <;> cases prefixed <;> simp [Instruction.length, Address.suffixBytes]
  | endbr64IbtDisabled => decide
  | nop encoding => cases encoding <;> decide
  | legacy old => cases old <;> simp [Instruction.length]
  | addMem32 destination address | loadMem32 destination address | storeMem32 address destination
  | cmpMemImm8 address immediate
  | cmpMemReg8 address source | cmpMemReg32 address source
  | lea64 destination address | loadMem64 destination address | addMem64 destination address
  | storeMem64 address destination =>
    cases address <;> simp [Instruction.length, Address.suffixBytes]
  | xorSelf32 _ | movReg32 _ _ | movReg64 _ _ | cmovReg64 _ _ _ | addReg64 _ _ | logicalReg64 _ _ _ | xchgReg64 _ _ | xchgRax64 _
  | imulReg64 _ _ | test64 _ _ | cmp64 _ _ | cmpImm64 _ _ | addImm64 _ _ | movSignImm32 _ _
  | inc64 _ | dec64 _ | bswapReg64 _ | shrOne64 _ | rolCL64 _ | je _ | jcc _ _ | jmp _ => simp [Instruction.length]

/-- Admission of a NEW instruction never admits it in the old sequential/TSO
profile; those clients continue to use the untouched legacy decoder. -/
theorem decodeAt_new_rejects_legacy {state : State} {instruction : Instruction}
    (decoded : decodeAt state = .ok instruction) (newInstruction : instruction.isNew = true) :
    ∃ fault, X86.decodeAt state = .error fault := by
  cases old : X86.decodeAt state with
  | error fault => exact ⟨fault, rfl⟩
  | ok legacy =>
    simp only [decodeAt, old, Except.ok.injEq] at decoded
    cases decoded
    simp [Instruction.isNew] at newInstruction

end EDSL.X86.Sequential
