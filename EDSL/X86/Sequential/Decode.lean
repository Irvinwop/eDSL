/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Model

namespace EDSL.X86.Sequential

def Instruction.length : Instruction → Nat
  | .legacy (.leaEaxRdiDisp8 _) | .legacy (.leaEaxRaxDisp8 _) | .legacy .cmpEaxZero => 3
  | .legacy .fetchAddEaxRdi => 4
  | .legacy (.mov32 _ _) => 5
  | .legacy .ret => 1
  | .legacy _ => 2
  | .xorSelf32 _ | .movReg32 _ _ | .xchgRax64 _ | .je _ | .jcc _ _ | .jmp _ => 2
  | .movReg64 _ _ | .addReg64 _ _ | .xchgReg64 _ _ | .test64 _ _ | .cmp64 _ _
  | .inc64 _ | .dec64 _ => 3
  | .addMem32 _ (.base _) | .loadMem32 _ (.base _) | .storeMem32 (.base _) _ => 2
  | .addMem32 _ (.indexed _ _ _) | .loadMem32 _ (.indexed _ _ _)
  | .storeMem32 (.indexed _ _ _) _ => 3
  | .lea64 _ (.base _) | .loadMem64 _ (.base _) | .addMem64 _ (.base _) | .storeMem64 (.base _) _ => 3
  | .lea64 _ (.indexed _ _ _) | .loadMem64 _ (.indexed _ _ _)
  | .addMem64 _ (.indexed _ _ _) | .storeMem64 (.indexed _ _ _) _ => 4
  | .addImm64 _ _ | .cmovReg64 _ _ _ => 4

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

/-- REX.W mod=00 operands. B extends the real base and X extends the SIB
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

/-- Continue after the enclosing decoder has recognized one REX.W prefix.
All addressing restrictions, ADD operand direction and register-only CMOV
checks remain explicit. -/
def decodeREXWAt (state : State) (opcode : Byte) : Except Error Instruction := do
  let operation ← fetchByte state.memory (state.rip + 1)
  if operation = 0x0f then
    let conditionOpcode ← fetchByte state.memory (state.rip + 2)
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
    return .lea64 (rexModRMReg opcode modrm) (← decodeQWordAddressAt state opcode modrm)
  else if operation = 0x01 ∨ operation = 0x03 then
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 = 3 then
      return if operation = 0x01 then .addReg64 (rexModRMRM opcode modrm) (rexModRMReg opcode modrm)
        else .addReg64 (rexModRMReg opcode modrm) (rexModRMRM opcode modrm)
    else if operation = 0x03 then
      return .addMem64 (rexModRMReg opcode modrm) (← decodeQWordAddressAt state opcode modrm)
    else throw .unsupportedEncoding
  else if opcode ≠ 0x48 then throw .unsupportedEncoding
  else if operation = 0x85 ∨ operation = 0x39 then
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
    return if operation = 0x85 then .test64 (modRMRM modrm) (modRMReg modrm)
      else .cmp64 (modRMRM modrm) (modRMReg modrm)
  else if operation = 0x83 then
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 ≠ 3 ∨ modrm.toNat / 8 % 8 ≠ 0 then throw .unsupportedEncoding
    return .addImm64 (modRMRM modrm) (← fetchByte state.memory (state.rip + 3))
  else if operation = 0xff then
    let modrm ← fetchByte state.memory (state.rip + 2)
    if modrm.toNat / 64 ≠ 3 then throw .unsupportedEncoding
    if modrm.toNat / 8 % 8 = 0 then return .inc64 (modRMRM modrm)
    else if modrm.toNat / 8 % 8 = 1 then return .dec64 (modRMRM modrm)
    else throw .unsupportedEncoding
  else throw .unsupportedEncoding

/-- NEW subset only. MOV64, LEA64, ADD64, register CMOV64 and register XCHG64 admit
one REX.W prefix 48..4F, including R/B and the SIB index extension X. Register
ADD and CMOV ignore X. Opcode 03 additionally admits a mod=00 memory source;
opcode 01 memory destinations remain unsupported. CMOV accepts the sixteen
0F 40..4F condition codes, with R extending its destination and B its source.
Memory CMOV needs an unconditional operand-read contract and is unsupported.
LEA uses the existing mod=00 address
subset to compute a value without a data access. XCHG's short form uses B to
extend its opcode register; unused R/X bits are ignored. Other 64-bit families
retain exact prefix 48.
Register ModRM for XOR/TEST/CMP/INC/DEC/ADD-immediate, unprefixed MOV32, and mod=00
ordinary ADD/MOV-memory addresses.
Short conditional branches admit the unprefixed 70..7F rel8 forms. The
legacy-first decoder retains 75 as JNZ, and 74 retains the existing JE API.
SIB allows all scales, no missing index (index=4), no missing base (base=5),
and no displacement. A plain base=4 must use SIB; base=5 would be RIP-relative
and is rejected. Unsupported forms never fall through to weaker addressing. -/
def decodeNewAt (state : State) (oldError : Error) : Except Error Instruction := do
  let opcode ← fetchByte state.memory state.rip
  if opcode = 0x31 then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm.toNat / 64 ≠ 3 ∨ modrm.toNat / 8 % 8 ≠ modrm.toNat % 8 then
      throw .unsupportedEncoding
    return .xorSelf32 (modRMRM modrm)
  else if rexWPrefix opcode then
    decodeREXWAt state opcode
  else if opcode = 0x03 then
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
    return .jcc (Condition.ofNibble ⟨opcode.toNat % 16, Nat.mod_lt _ (by decide)⟩)
      (← fetchByte state.memory (state.rip + 1))
  else if opcode = 0xeb then
    return .jmp (← fetchByte state.memory (state.rip + 1))
  else throw oldError

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

/-- Success preservation, rather than equality of a padded byte window. This
allows a one-byte RET at the very end of a finite candidate. -/
def SuccessfulFetchTransport (source destination : State) : Prop :=
  ∀ offset, offset < 5 → ∀ byte,
    fetchByte source.memory (source.rip + BitVec.ofNat 64 offset) = .ok byte →
    fetchByte destination.memory (destination.rip + BitVec.ofNat 64 offset) = .ok byte

theorem Instruction.length_pos (instruction : Instruction) : 0 < instruction.length := by
  cases instruction with
  | legacy old => cases old <;> simp [Instruction.length]
  | addMem32 destination address | loadMem32 destination address | storeMem32 address destination
  | lea64 destination address | loadMem64 destination address | addMem64 destination address
  | storeMem64 address destination =>
    cases address <;> simp [Instruction.length]
  | xorSelf32 _ | movReg32 _ _ | movReg64 _ _ | cmovReg64 _ _ _ | addReg64 _ _ | xchgReg64 _ _ | xchgRax64 _
  | test64 _ _ | cmp64 _ _ | addImm64 _ _
  | inc64 _ | dec64 _ | je _ | jcc _ _ | jmp _ => simp [Instruction.length]

theorem Instruction.length_le_five (instruction : Instruction) : instruction.length ≤ 5 := by
  cases instruction with
  | legacy old => cases old <;> simp [Instruction.length]
  | addMem32 destination address | loadMem32 destination address | storeMem32 address destination
  | lea64 destination address | loadMem64 destination address | addMem64 destination address
  | storeMem64 address destination =>
    cases address <;> simp [Instruction.length]
  | xorSelf32 _ | movReg32 _ _ | movReg64 _ _ | cmovReg64 _ _ _ | addReg64 _ _ | xchgReg64 _ _ | xchgRax64 _
  | test64 _ _ | cmp64 _ _ | addImm64 _ _
  | inc64 _ | dec64 _ | je _ | jcc _ _ | jmp _ => simp [Instruction.length]

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
