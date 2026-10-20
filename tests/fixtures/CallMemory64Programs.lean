/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemory64.Contract
import EDSL.X86.CallReturn

set_option warningAsError true

namespace EDSL.CallMemory64.Compiler
open X86

/-- Complete separately compiled and linked GNU23 text windows, including the
trailing helper. Both caller entries are offset zero. -/
inductive Profile where
  | gccSeparate | clangSeparate
  deriving DecidableEq, Repr

def bytes : Profile → List Byte
  | .gccSeparate => [0x50,0xe8,0x05,0x00,0x00,0x00,0x5a,0x48,0xff,0xc0,0xc3,
      0x48,0x89,0x37,0x48,0x8b,0x07,0xc3]
  | .clangSeparate => [0x50,0xe8,0x05,0x00,0x00,0x00,0x48,0xff,0xc0,0x59,0xc3,
      0x48,0x89,0x37,0x48,0x8b,0x07,0xc3]

def program (profile : Profile) : Program := ⟨bytes profile, 0⟩

def popDestination : Profile → Register
  | .gccSeparate => .rdx
  | .clangSeparate => .rcx

inductive Node where
  | push | call | store | load | innerRet | increment | pop | ret
  deriving DecidableEq, Repr

def offset : Profile → Node → Nat
  | _, .push => 0
  | _, .call => 1
  | _, .store => 11
  | _, .load => 14
  | _, .innerRet => 17
  | .gccSeparate, .increment => 7
  | .gccSeparate, .pop => 6
  | .clangSeparate, .increment => 6
  | .clangSeparate, .pop => 9
  | _, .ret => 10

def address : Sequential.Address := .base .rdi

def instruction (profile : Profile) : Node → CallReturn.Instruction
  | .push => .push64 .rax false
  | .call => .callRelative32 5
  | .store => .sequential (.storeMem64 address .rsi)
  | .load => .sequential (.loadMem64 .rax address)
  | .innerRet | .ret => .sequential (.legacy .ret)
  | .increment => .sequential (.inc64 .rax)
  | .pop => .pop64 (popDestination profile) false

theorem inside (profile : Profile) (node : Node) :
    offset profile node < (bytes profile).length := by
  cases profile <;> cases node <;> decide

theorem static_decode (profile : Profile) (node : Node) :
    CallReturn.decodeAt (Sequential.codeState (bytes profile) (offset profile node)) =
      .ok (instruction profile node) := by
  cases profile <;> cases node <;> rfl

theorem decode {profile : Profile} {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes profile)) (node : Node)
    (pc : state.rip = base + BitVec.ofNat 64 (offset profile node)) :
    CallReturn.decodeAt state = .ok (instruction profile node) :=
  CallReturn.decodeAt_code code (by cases profile <;> decide) (inside profile node)
    state rfl pc (static_decode profile node)

end EDSL.CallMemory64.Compiler
