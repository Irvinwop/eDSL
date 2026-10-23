/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.native.UnaryReplay

set_option autoImplicit false

namespace EDSL.Tests.SequentialUnary
open X86 X86.Sequential UnaryReplay

private def entry (code : List Byte) (destination : Register := .rax)
    (input : Word := 0xdeadbeef00000001) (flags : Word := 0x602)
    (rip : Word := codeBase) : State where
  registers := fun r => if r = destination then input else modelCanary r
  rip := rip
  flags := flags
  memory := replayMemory code rip

/- These literal encodings and constructor results are independently stated.
They cover /3 ModRM.r/m and opcode.rd through both register banks, especially
RSP/R12 and RBP/R13. No production encoder supplies an expectation. -/
private def plainNeg : List (List Byte × Sequential.Instruction) := [
  ([0xf7,0xd8],.negReg32 .rax false), ([0xf7,0xd9],.negReg32 .rcx false),
  ([0xf7,0xda],.negReg32 .rdx false), ([0xf7,0xdb],.negReg32 .rbx false),
  ([0xf7,0xdc],.negReg32 .rsp false), ([0xf7,0xdd],.negReg32 .rbp false),
  ([0xf7,0xde],.negReg32 .rsi false), ([0xf7,0xdf],.negReg32 .rdi false)]

private def prefixedNeg : List (List Byte × Sequential.Instruction) := [
  ([0x40,0xf7,0xd8],.negReg32 .rax true), ([0x40,0xf7,0xd9],.negReg32 .rcx true),
  ([0x40,0xf7,0xda],.negReg32 .rdx true), ([0x40,0xf7,0xdb],.negReg32 .rbx true),
  ([0x40,0xf7,0xdc],.negReg32 .rsp true), ([0x40,0xf7,0xdd],.negReg32 .rbp true),
  ([0x40,0xf7,0xde],.negReg32 .rsi true), ([0x40,0xf7,0xdf],.negReg32 .rdi true)]

private def extendedNeg : List (List Byte × Sequential.Instruction) := [
  ([0x41,0xf7,0xd8],.negReg32 .r8 true), ([0x41,0xf7,0xd9],.negReg32 .r9 true),
  ([0x41,0xf7,0xda],.negReg32 .r10 true), ([0x41,0xf7,0xdb],.negReg32 .r11 true),
  ([0x41,0xf7,0xdc],.negReg32 .r12 true), ([0x41,0xf7,0xdd],.negReg32 .r13 true),
  ([0x41,0xf7,0xde],.negReg32 .r14 true), ([0x41,0xf7,0xdf],.negReg32 .r15 true)]

private def lowSwap : List (List Byte × Sequential.Instruction) := [
  ([0x48,0x0f,0xc8],.bswapReg64 .rax), ([0x48,0x0f,0xc9],.bswapReg64 .rcx),
  ([0x48,0x0f,0xca],.bswapReg64 .rdx), ([0x48,0x0f,0xcb],.bswapReg64 .rbx),
  ([0x48,0x0f,0xcc],.bswapReg64 .rsp), ([0x48,0x0f,0xcd],.bswapReg64 .rbp),
  ([0x48,0x0f,0xce],.bswapReg64 .rsi), ([0x48,0x0f,0xcf],.bswapReg64 .rdi)]

private def highSwap : List (List Byte × Sequential.Instruction) := [
  ([0x49,0x0f,0xc8],.bswapReg64 .r8), ([0x49,0x0f,0xc9],.bswapReg64 .r9),
  ([0x49,0x0f,0xca],.bswapReg64 .r10), ([0x49,0x0f,0xcb],.bswapReg64 .r11),
  ([0x49,0x0f,0xcc],.bswapReg64 .r12), ([0x49,0x0f,0xcd],.bswapReg64 .r13),
  ([0x49,0x0f,0xce],.bswapReg64 .r14), ([0x49,0x0f,0xcf],.bswapReg64 .r15)]

private def decoded (form : List Byte × Sequential.Instruction) : Bool :=
  match Sequential.decodeAt (entry form.1) with
  | .error _ => false
  | .ok actual => decide (actual = form.2) && actual.length == form.1.length &&
    actual.isNew && !actual.isLocked && !actual.choosesAF &&
    actual.operandReads (entry form.1) == [] &&
    actual.storeIntent (entry form.1) == none && actual.storeIntent64 (entry form.1) == none

theorem decode_plain_neg : plainNeg.all decoded = true := by decide +kernel
theorem decode_prefixed_neg : prefixedNeg.all decoded = true := by decide +kernel
theorem decode_extended_neg : extendedNeg.all decoded = true := by decide +kernel
theorem decode_low_swap : lowSwap.all decoded = true := by decide +kernel
theorem decode_high_swap : highSwap.all decoded = true := by decide +kernel

private def destination : Sequential.Instruction → Register
  | .negReg32 r _ | .bswapReg64 r => r
  | _ => .rax

/-- Independently stated complete result projection: full64 destination,
all fifteen other GPRs, exact flags/RIP, no operand reads, and RAM samples.
Unmapped/noncanonical GPR contents (including RSP) are not dereferenced. -/
private def outcome (code : List Byte) (d : Register) (input output beforeFlags afterFlags : Word)
    (rip : Word := codeBase) : Bool :=
  let initial := entry code d input beforeFlags rip
  [false,true].all fun af => match Sequential.step af initial with
    | .error _ => false
    | .ok observation => match observation.result with
      | .next final =>
        final.flags == afterFlags && final.rip == rip + BitVec.ofNat 64 code.length &&
        observation.reads == [] &&
        allRegisters.all (fun r => final.registers r == if r = d then output else modelCanary r) &&
        ([0,rip-1,rip,rip+1,rip+2,rip+3,0x7fffffffffff,0x800000000000,
          0xffff800000000000,0xffffffffffffffff] : List Word).all (fun a =>
          final.memory.read a == initial.memory.read a &&
          final.memory.writable a == initial.memory.writable a &&
          final.memory.executable a == initial.memory.executable a)
      | _ => false

private def negOne (form : List Byte × Sequential.Instruction) : Bool :=
  outcome form.1 (destination form.2) 0xdeadbeef00000001 0xffffffff
    0xfedcba9800070ed7 0xfedcba9800070697

private def swapAsymmetric (form : List Byte × Sequential.Instruction) : Bool :=
  outcome form.1 (destination form.2) 0x0123456789abcdef 0xefcdab8967452301
    0xfedcba9800070ed7 0xfedcba9800070ed7

/- RF/VM/DF/AC/debug/high/reserved bits here are arbitrary modeled frame
challenges, not PUSHFQ observations or physically admitted entry profiles. -/
theorem plain_neg_full_state : plainNeg.all negOne = true := by decide +kernel
theorem prefixed_neg_full_state : prefixedNeg.all negOne = true := by decide +kernel
theorem extended_neg_full_state : extendedNeg.all negOne = true := by decide +kernel
theorem low_swap_full_state : lowSwap.all swapAsymmetric = true := by decide +kernel
theorem high_swap_full_state : highSwap.all swapAsymmetric = true := by decide +kernel

/-- Fixed flags distinguish CF/OF/AF/ZF/SF/PF, low-nibble and parity edges,
the signed minimum, and dirty upper halves. AF choices cannot change NEG. -/
theorem neg_flag_and_zero_extension_edges :
    ([(0xdeadbeef00000000,0,0x646), (0xdeadbeef00000001,0xffffffff,0x697),
      (0xffffffff80000000,0x80000000,0xe87), (0x800000007fffffff,0x80000001,0x693),
      (0xffffffffffffffff,1,0x613), (0xaabbccdd00000010,0xfffffff0,0x687),
      (0x55aa55aafffffff0,0x10,0x603), (0xaabbccdd00000011,0xffffffef,0x693),
      (0x55aa55aaffffffef,0x11,0x617), (0x1234567889abcdef,0x76543211,0x617)] :
      List (Word × Word × Word)).all (fun (input,output,flags) =>
        outcome [0x41,0xf7,0xdf] .r15 input output 0x602 flags) = true := by decide +kernel

/-- Byte positions cross low32/high32; every old flag survives. These include
RSP as an ordinary GPR and values that are not canonical memory addresses. -/
theorem swap_fullwidth_edges :
    ([(1,0x0100000000000000), (0x8000000000000000,0x80),
      (0x00000000ffffffff,0xffffffff00000000), (0xffffffff00000000,0x00000000ffffffff),
      (0x0000000100000000,0x0000000001000000), (0x0123456767452301,0x0123456767452301)] :
      List (Word × Word)).all (fun (input,output) =>
        outcome [0x48,0x0f,0xcc] .rsp input output 0xffffffffffffffff 0xffffffffffffffff) = true :=
  by decide +kernel

private def fault {α : Type} (result : Except Error α) (expected : Error) : Bool :=
  match result with | .error actual => actual == expected | .ok _ => false

private def rejects (code : List Byte) (expected : Error := .unsupportedEncoding) : Bool :=
  let initial := entry code
  fault (Sequential.decodeAt initial) expected &&
    [false,true].all (fun af => fault (Sequential.step af initial) expected)

/-- /3 is required, mod=11 is required even with mapped operands. Reject
memory/SIB/disp forms and every other group-3 extension rather than running a
register NEG, NOT, multiply or a narrower/wider operation. -/
theorem neg_modrm_and_rex_negatives :
    ([[0xf7,0x18], [0xf7,0x1c,0x24], [0xf7,0x58,0], [0xf7,0x98,0,0,0,0],
      [0x41,0xf7,0x18], [0x40,0xf7,0x1d,0,0,0,0],
      [0xf7,0xc0,1,0,0,0], [0xf7,0xc8], [0xf7,0xd0], [0xf7,0xe0],
      [0xf7,0xe8], [0xf7,0xf0], [0xf7,0xf8],
      [0x42,0xf7,0xd8], [0x43,0xf7,0xd8], [0x44,0xf7,0xd8],
      [0x45,0xf7,0xd8], [0x46,0xf7,0xd8], [0x47,0xf7,0xd8],
      [0x48,0xf7,0xd8], [0x49,0xf7,0xd8], [0x4f,0xf7,0xd8],
      [0x40,0x41,0xf7,0xd8], [0x41,0x40,0xf7,0xd8], [0x66,0xf7,0xd8],
      [0xf0,0xf7,0xd8], [0xf3,0xf7,0xd8]] : List (List Byte)).all
      (fun code => rejects code) = true := by decide +kernel

/-- BSWAP uses opcode.rd and REX.B, never REX.R. No-W/16-bit/byte widths,
extra/repeated prefixes and noncanonical REX.R/X aliases stay unsupported. -/
theorem swap_width_prefix_bank_negatives :
    ([[0x0f,0xc8], [0x40,0x0f,0xc8], [0x41,0x0f,0xc8], [0x66,0x0f,0xc8],
      [0x4a,0x0f,0xc8], [0x4b,0x0f,0xc8], [0x4c,0x0f,0xc8],
      [0x4d,0x0f,0xc8], [0x4e,0x0f,0xc8], [0x4f,0x0f,0xc8],
      [0x48,0x48,0x0f,0xc8], [0x49,0x48,0x0f,0xc8],
      [0x66,0x48,0x0f,0xc8], [0xf0,0x48,0x0f,0xc8], [0xf3,0x48,0x0f,0xc8],
      [0x48,0x0f,0xc7], [0x49,0x0f,0xd0]] : List (List Byte)).all
      (fun code => rejects code) = true := by decide +kernel

/-- F6 is recognized by TEST-low8, but its unmodeled byte-NEG /3 selector
rejects as an unsupported encoding. Unknown lead prefixes retain the legacy
opcode error; none may decode as LOW32 NEG or full64 BSWAP. -/
theorem unknown_prefix_and_byte_width_negatives :
    rejects [0xf6,0xd8] .unsupportedEncoding = true ∧
    rejects [0x67,0xf7,0xd8] (.unsupportedOpcode 0x67) = true ∧
    rejects [0xf2,0xf7,0xd8] (.unsupportedOpcode 0xf2) = true ∧
    rejects [0x2e,0x48,0x0f,0xc8] (.unsupportedOpcode 0x2e) = true := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

private def fetchFailures (code : List Byte) : Bool :=
  let initial := entry code
  (List.range code.length).all fun i =>
    let address := initial.rip + BitVec.ofNat 64 i
    let missing := { initial with memory := { initial.memory with
      read := fun a => if a = address then none else initial.memory.read a } }
    let denied := { initial with memory := { initial.memory with
      executable := fun a => if a = address then false else initial.memory.executable a } }
    [missing,denied].all fun state =>
      fault (Sequential.decodeAt state) (.inaccessibleInstruction address) &&
      [false,true].all (fun af => fault (Sequential.step af state) (.inaccessibleInstruction address))

theorem every_instruction_byte_authenticated :
    ([[0xf7,0xd8], [0x40,0xf7,0xdc], [0x41,0xf7,0xdf],
      [0x48,0x0f,0xcc], [0x49,0x0f,0xcf]] : List (List Byte)).all fetchFailures = true :=
  by decide +kernel

theorem truncated_prefix_opcode_modrm :
    rejects [] (.inaccessibleInstruction codeBase) = true ∧
    rejects [0xf7] (.inaccessibleInstruction (codeBase+1)) = true ∧
    rejects [0x40,0xf7] (.inaccessibleInstruction (codeBase+2)) = true ∧
    rejects [0x41] (.inaccessibleInstruction (codeBase+1)) = true ∧
    rejects [0x48,0x0f] (.inaccessibleInstruction (codeBase+2)) = true ∧
    rejects [0x49] (.inaccessibleInstruction (codeBase+1)) = true := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,by decide +kernel⟩

/-- Fetches stop at the canonical hole. An instruction entirely in the upper
canonical range may wrap its fallthrough RIP; no imaginary stack/data access
is introduced for RSP. These are explicit abstract-model behavior checks. -/
theorem canonical_fetch_and_rip_edges :
    ([([0xf7,0xd8],0x7fffffffffff), ([0x41,0xf7,0xdc],0x7ffffffffffe),
      ([0x49,0x0f,0xcf],0x7ffffffffffe)] : List (List Byte × Word)).all
      (fun (code,rip) => [false,true].all (fun af => fault
        (Sequential.step af (entry code .rax 1 0x602 rip))
        (.inaccessibleInstruction 0x800000000000))) = true ∧
    outcome [0x40,0xf7,0xdc] .rsp 0x8000000000000001 0xffffffff 0x602 0x697
      0xfffffffffffffffd = true ∧
    outcome [0x49,0x0f,0xcc] .r12 0x0123456789abcdef 0xefcdab8967452301 0x602 0x602
      0x7ffffffffffd = true := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

end EDSL.Tests.SequentialUnary

#audit_edsl
