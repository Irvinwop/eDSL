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
  | .xorSelf32 destination => s!"(.xorSelf32 {register destination})"
  | .test64 left right => s!"(.test64 {register left} {register right})"
  | .cmp64 left right => s!"(.cmp64 {register left} {register right})"
  | .addMem32 destination operand => s!"(.addMem32 {register destination} {address operand})"
  | .movReg32 destination source => s!"(.movReg32 {register destination} {register source})"
  | .movReg64 destination source => s!"(.movReg64 {register destination} {register source})"
  | .lea64 destination operand => s!"(.lea64 {register destination} {address operand})"
  | .addReg64 destination source => s!"(.addReg64 {register destination} {register source})"
  | .xchgReg64 left right => s!"(.xchgReg64 {register left} {register right})"
  | .xchgRax64 other => s!"(.xchgRax64 {register other})"
  | .loadMem32 destination operand => s!"(.loadMem32 {register destination} {address operand})"
  | .storeMem32 operand source => s!"(.storeMem32 {address operand} {register source})"
  | .loadMem64 destination operand => s!"(.loadMem64 {register destination} {address operand})"
  | .storeMem64 operand source => s!"(.storeMem64 {address operand} {register source})"
  | .addImm64 destination value => s!"(.addImm64 {register destination} {value.toNat})"
  | .inc64 destination => s!"(.inc64 {register destination})"
  | .dec64 destination => s!"(.dec64 {register destination})"
  | .je value => s!"(.je {value.toNat})"
  | .jmp value => s!"(.jmp {value.toNat})"

end EDSL.X86.Sequential.Literals
