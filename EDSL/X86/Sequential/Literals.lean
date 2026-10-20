/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Decode

namespace EDSL.X86.Sequential.Literals

/-- Only typed data enters generated Lean source. Input filenames, symbol
names and arbitrary candidate text are never interpolated as declarations. -/
def register : Register → String
  | .rax => ".rax" | .rcx => ".rcx" | .rdx => ".rdx" | .rbx => ".rbx"
  | .rsp => ".rsp" | .rbp => ".rbp" | .rsi => ".rsi" | .rdi => ".rdi"
  | .r8 => ".r8" | .r9 => ".r9" | .r10 => ".r10" | .r11 => ".r11"
  | .r12 => ".r12" | .r13 => ".r13" | .r14 => ".r14" | .r15 => ".r15"

def bytes (values : List Byte) : String :=
  String.intercalate ", " (values.map fun byte => toString byte.toNat)

def address : Address → String
  | .base base => s!"(.base {register base})"
  | .indexed base index scale => s!"(.indexed {register base} {register index} {scale.val})"
  | .baseDisp8 base displacement => s!"(.baseDisp8 {register base} {displacement.toNat})"
  | .sibDisp8 base index scale displacement =>
    let indexed := match index with
      | none => "none"
      | some index => s!"(some {register index})"
    s!"(.sibDisp8 {register base} {indexed} {scale.val} {displacement.toNat})"

/-- Canonical constructor names for all architectural condition codes. -/
def condition : Condition → String
  | .overflow => ".overflow" | .notOverflow => ".notOverflow"
  | .below => ".below" | .aboveEqual => ".aboveEqual"
  | .equal => ".equal" | .notEqual => ".notEqual"
  | .belowEqual => ".belowEqual" | .above => ".above"
  | .sign => ".sign" | .notSign => ".notSign"
  | .parity => ".parity" | .notParity => ".notParity"
  | .less => ".less" | .greaterEqual => ".greaterEqual"
  | .lessEqual => ".lessEqual" | .greater => ".greater"

def legacy : X86.Instruction → String
  | .leaEaxRdiDisp8 value => s!"(.leaEaxRdiDisp8 {value.toNat})"
  | .leaEaxRaxDisp8 value => s!"(.leaEaxRaxDisp8 {value.toNat})"
  | .movEaxEdi => ".movEaxEdi" | .movEaxEsi => ".movEaxEsi"
  | .exchangeEaxRdi => ".exchangeEaxRdi" | .fetchAddEaxRdi => ".fetchAddEaxRdi"
  | .jrcxz value => s!"(.jrcxz {value.toNat})"
  | .loopRcx value => s!"(.loopRcx {value.toNat})"
  | .jnz value => s!"(.jnz {value.toNat})"
  | .cmpEaxZero => ".cmpEaxZero"
  | .loadEaxRdi => ".loadEaxRdi" | .loadEaxRsi => ".loadEaxRsi"
  | .storeEsiRdi => ".storeEsiRdi" | .storeEaxRsi => ".storeEaxRsi"
  | .mov32 destination value => s!"(.mov32 {register destination} {value.toNat})"
  | .syscall => ".syscall" | .ret => ".ret"

def instruction : Instruction → String
  | .legacy operation => s!"(.legacy {legacy operation})"
  | .test32 left right prefixed => s!"(.test32 {register left} {register right} {prefixed})"
  | .cmp32 left right prefixed => s!"(.cmp32 {register left} {register right} {prefixed})"
  | .cmpReg8 left right prefixed => s!"(.cmpReg8 {register left} {register right} {prefixed})"
  | .subReg32 destination source prefixed =>
    s!"(.subReg32 {register destination} {register source} {prefixed})"
  | .negReg32 destination prefixed => s!"(.negReg32 {register destination} {prefixed})"
  | .bswapReg64 destination => s!"(.bswapReg64 {register destination})"
  | .shrOne64 destination => s!"(.shrOne64 {register destination})"
  | .movzxReg8 destination source prefixed =>
    s!"(.movzxReg8 {register destination} {register source} {prefixed})"
  | .movzxMem8 destination operand prefixed =>
    s!"(.movzxMem8 {register destination} {address operand} {prefixed})"
  | .cmpMemImm8 operand immediate => s!"(.cmpMemImm8 {address operand} {immediate.toNat})"
  | .cmpMemReg8 operand source => s!"(.cmpMemReg8 {address operand} {register source})"
  | .cmpMemReg32 operand source => s!"(.cmpMemReg32 {address operand} {register source})"
  | .endbr64IbtDisabled => ".endbr64IbtDisabled"
  | .nop encoding =>
    let name := match encoding with
      | .one => ".one" | .two => ".two" | .three => ".three" | .four => ".four" | .five => ".five"
      | .nine => ".nine"
    s!"(.nop {name})"
  | .xorSelf32 destination => s!"(.xorSelf32 {register destination})"
  | .test64 left right => s!"(.test64 {register left} {register right})"
  | .cmp64 left right => s!"(.cmp64 {register left} {register right})"
  | .addMem32 destination operand => s!"(.addMem32 {register destination} {address operand})"
  | .addMem64 destination operand => s!"(.addMem64 {register destination} {address operand})"
  | .movReg32 destination source => s!"(.movReg32 {register destination} {register source})"
  | .movReg64 destination source => s!"(.movReg64 {register destination} {register source})"
  | .movSignImm32 destination immediate => s!"(.movSignImm32 {register destination} {immediate.toNat})"
  | .cmovReg64 predicate destination source =>
    s!"(.cmovReg64 {condition predicate} {register destination} {register source})"
  | .cmovReg32 predicate destination source prefixed =>
    s!"(.cmovReg32 {condition predicate} {register destination} {register source} {prefixed})"
  | .lea64 destination operand => s!"(.lea64 {register destination} {address operand})"
  | .addReg64 destination source => s!"(.addReg64 {register destination} {register source})"
  | .logicalReg64 operation destination source =>
    let logical := match operation with
      | .band => ".band" | .bor => ".bor" | .bxor => ".bxor"
    s!"(.logicalReg64 {logical} {register destination} {register source})"
  | .xchgReg64 left right => s!"(.xchgReg64 {register left} {register right})"
  | .xchgRax64 other => s!"(.xchgRax64 {register other})"
  | .loadMem32 destination operand => s!"(.loadMem32 {register destination} {address operand})"
  | .storeMem32 operand source => s!"(.storeMem32 {address operand} {register source})"
  | .loadMem64 destination operand => s!"(.loadMem64 {register destination} {address operand})"
  | .storeMem64 operand source => s!"(.storeMem64 {address operand} {register source})"
  | .addImm64 destination value => s!"(.addImm64 {register destination} {value.toNat})"
  | .addImm32 destination value prefixed => s!"(.addImm32 {register destination} {value.toNat} {prefixed})"
  | .inc32 destination prefixed => s!"(.inc32 {register destination} {prefixed})"
  | .inc64 destination => s!"(.inc64 {register destination})"
  | .dec64 destination => s!"(.dec64 {register destination})"
  | .je value => s!"(.je {value.toNat})"
  | .jcc status value => s!"(.jcc {condition status} {value.toNat})"
  | .jmp value => s!"(.jmp {value.toNat})"

end EDSL.X86.Sequential.Literals
