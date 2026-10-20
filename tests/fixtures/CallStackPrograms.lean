/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Contract
import EDSL.X86.CallReturn

set_option warningAsError true

namespace EDSL.CallStack.Compiler
open X86

/-- Four whole final-linked GNU23 compiler text windows. `same` includes the
helper before the selected caller entry; `separate` includes the trailing helper. -/
inductive Profile where
  | gccSame | gccSeparate | clangSame | clangSeparate
  deriving DecidableEq, Repr

def bytes : Profile → List Byte
  | .gccSame => [0x48,0x8d,0x47,0x01,0xc3,0xe8,0xf6,0xff,0xff,0xff,0x48,0xff,0xc0,0xc3]
  | .gccSeparate => [0x50,0xe8,0x05,0x00,0x00,0x00,0x5a,0x48,0xff,0xc0,0xc3,0x48,0x8d,0x47,0x01,0xc3]
  | .clangSame => [0x48,0x8d,0x47,0x01,0xc3,0x50,0xe8,0xf5,0xff,0xff,0xff,0x48,0xff,0xc0,0x59,0xc3]
  | .clangSeparate => [0x50,0xe8,0x05,0x00,0x00,0x00,0x48,0xff,0xc0,0x59,0xc3,0x48,0x8d,0x47,0x01,0xc3]

def entry : Profile → Nat
  | .gccSame | .clangSame => 5
  | _ => 0

def program (profile : Profile) : Program := ⟨bytes profile, entry profile⟩

def padded : Profile → Bool
  | .gccSame => false
  | _ => true

def popDestination : Profile → Register
  | .gccSeparate => .rdx
  | _ => .rcx

def displacement : Profile → BitVec 32
  | .gccSame => 0xfffffff6
  | .clangSame => 0xfffffff5
  | _ => 5

inductive Node where
  | push | call | helper | innerRet | increment | pop | ret
  deriving DecidableEq, Repr

def active (profile : Profile) : Node → Bool
  | .push | .pop => padded profile
  | _ => true

def offset : Profile → Node → Nat
  | .gccSame, .call => 5
  | .gccSame, .helper => 0
  | .gccSame, .innerRet => 4
  | .gccSame, .increment => 10
  | .gccSame, .ret => 13
  | .gccSame, _ => 0
  | .gccSeparate, .push => 0
  | .gccSeparate, .call => 1
  | .gccSeparate, .helper => 11
  | .gccSeparate, .innerRet => 15
  | .gccSeparate, .increment => 7
  | .gccSeparate, .pop => 6
  | .gccSeparate, .ret => 10
  | .clangSame, .push => 5
  | .clangSame, .call => 6
  | .clangSame, .helper => 0
  | .clangSame, .innerRet => 4
  | .clangSame, .increment => 11
  | .clangSame, .pop => 14
  | .clangSame, .ret => 15
  | .clangSeparate, .push => 0
  | .clangSeparate, .call => 1
  | .clangSeparate, .helper => 11
  | .clangSeparate, .innerRet => 15
  | .clangSeparate, .increment => 6
  | .clangSeparate, .pop => 9
  | .clangSeparate, .ret => 10

def instruction (profile : Profile) : Node → CallReturn.Instruction
  | .push => .push64 .rax false
  | .call => .callRelative32 (displacement profile)
  | .helper => .leaDisp8 .rax (.plain .rdi) 1
  | .innerRet | .ret => .sequential (.legacy .ret)
  | .increment => .sequential (.inc64 .rax)
  | .pop => .pop64 (popDestination profile) false

theorem inside (profile : Profile) (node : Node) : offset profile node < (bytes profile).length := by
  cases profile <;> cases node <;> decide

theorem static_decode (profile : Profile) (node : Node) (present : active profile node = true) :
    CallReturn.decodeAt (Sequential.codeState (bytes profile) (offset profile node)) =
      .ok (instruction profile node) := by
  cases profile <;> cases node <;> (first | rfl | cases present)

/-- Bind every instruction, including both RETs and the helper, to the exact
current executable window. No first-RET truncation or entry-prefix omission. -/
theorem decode {profile : Profile} {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes profile)) (node : Node)
    (present : active profile node = true)
    (pc : state.rip = base + BitVec.ofNat 64 (offset profile node)) :
    CallReturn.decodeAt state = .ok (instruction profile node) :=
  CallReturn.decodeAt_code code (by cases profile <;> decide) (inside profile node)
    state rfl pc (static_decode profile node present)

end EDSL.CallStack.Compiler
