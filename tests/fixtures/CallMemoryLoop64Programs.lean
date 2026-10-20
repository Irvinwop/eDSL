/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemoryLoop64.Contract
import EDSL.X86.CallReturn
import EDSL.CallStack.Certificates

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.Compiler
open X86 OS

/-- Complete separately compiled and linked texts, retaining the helper beyond
caller RET. This module proves decoding/coverage, not functional correctness. -/
inductive Profile where
  | gccSeparate | clangSeparate
  deriving DecidableEq, Repr

def bytes : Profile → List Byte
  | .gccSeparate =>
    [0x55,0x48,0x89,0xfd,0x53,0x48,0x89,0xd3,0x51,0x48,0x85,0xdb,0x74,0x11,
     0x48,0x89,0xef,0x48,0xff,0xcb,0xe8,0x0d,0,0,0,0x48,0x8d,0x70,1,0xeb,0xea,
     0x5a,0x48,0x89,0xf0,0x5b,0x5d,0xc3,0x48,0x89,0x37,0x48,0x8b,7,0xc3]
  | .clangSeparate =>
    [0x48,0x89,0xf0,0x48,0x85,0xd2,0x74,0x24,0x41,0x56,0x53,0x50,0x48,0x89,
     0xd3,0x49,0x89,0xfe,0x4c,0x89,0xf7,0x48,0x89,0xc6,0xe8,0x10,0,0,0,0x48,
     0xff,0xc0,0x48,0xff,0xcb,0x75,0xed,0x48,0x83,0xc4,8,0x5b,0x41,0x5e,0xc3,
     0x48,0x89,0x37,0x48,0x8b,7,0xc3]

def program (profile : Profile) : Program := ⟨bytes profile, 0⟩

/-- The expected operations and offsets are read independently from the owned
compiler disassemblies. Every reached prefix/immediate belongs to its site. -/
def sites : Profile → List (Nat × CallReturn.Instruction)
  | .gccSeparate =>
    [(0,.push64 .rbp false), (1,.sequential (.movReg64 .rbp .rdi)),
     (4,.push64 .rbx false), (5,.sequential (.movReg64 .rbx .rdx)),
     (8,.push64 .rcx false), (9,.sequential (.test64 .rbx .rbx)),
     (12,.sequential (.je 0x11)), (14,.sequential (.movReg64 .rdi .rbp)),
     (17,.sequential (.dec64 .rbx)), (20,.callRelative32 13),
     (25,.leaDisp8 .rsi (.plain .rax) 1), (29,.sequential (.jmp 0xea)),
     (31,.pop64 .rdx false), (32,.sequential (.movReg64 .rax .rsi)),
     (35,.pop64 .rbx false), (36,.pop64 .rbp false), (37,.sequential (.legacy .ret)),
     (38,.sequential (.storeMem64 (.base .rdi) .rsi)),
     (41,.sequential (.loadMem64 .rax (.base .rdi))), (44,.sequential (.legacy .ret))]
  | .clangSeparate =>
    [(0,.sequential (.movReg64 .rax .rsi)), (3,.sequential (.test64 .rdx .rdx)),
     (6,.sequential (.je 0x24)), (8,.push64 .r14 true), (10,.push64 .rbx false),
     (11,.push64 .rax false), (12,.sequential (.movReg64 .rbx .rdx)),
     (15,.sequential (.movReg64 .r14 .rdi)), (18,.sequential (.movReg64 .rdi .r14)),
     (21,.sequential (.movReg64 .rsi .rax)), (24,.callRelative32 16),
     (29,.sequential (.inc64 .rax)), (32,.sequential (.dec64 .rbx)),
     (35,.sequential (.legacy (.jnz 0xed))), (37,.sequential (.addImm64 .rsp 8)),
     (41,.pop64 .rbx false), (42,.pop64 .r14 true), (44,.sequential (.legacy .ret)),
     (45,.sequential (.storeMem64 (.base .rdi) .rsi)),
     (48,.sequential (.loadMem64 .rax (.base .rdi))), (51,.sequential (.legacy .ret))]

theorem positive (profile : Profile) : 0 < (bytes profile).length := by
  cases profile <;> decide

theorem bounded (profile : Profile) : (bytes profile).length ≤ 4096 := by
  cases profile <;> decide

theorem decode_bound (profile : Profile) : (bytes profile).length ≤ 64 := by
  cases profile <;> decide

theorem static_sites (profile : Profile) : (sites profile).all (fun site =>
    decide ((CallReturn.decodeAt (Sequential.codeState (bytes profile) site.1)).toOption = some site.2 ∧
      site.1 + site.2.length ≤ (bytes profile).length)) = true := by
  cases profile <;> decide +kernel

theorem static_decode {profile : Profile} {site : Nat × CallReturn.Instruction}
    (member : site ∈ sites profile) :
    CallReturn.decodeAt (Sequential.codeState (bytes profile) site.1) = .ok site.2 ∧
      site.1 + site.2.length ≤ (bytes profile).length := by
  obtain ⟨decoded, bound⟩ := of_decide_eq_true
    (List.all_eq_true.mp (static_sites profile) site member)
  refine ⟨?_, bound⟩
  cases actual : CallReturn.decodeAt (Sequential.codeState (bytes profile) site.1) with
  | error fault => simp only [actual, Except.toOption, reduceCtorEq] at decoded
  | ok instruction =>
    simp only [actual, Except.toOption, Option.some.injEq] at decoded
    exact congrArg Except.ok decoded

theorem inside {profile : Profile} {site : Nat × CallReturn.Instruction}
    (member : site ∈ sites profile) : site.1 < (bytes profile).length := by
  have bound := (static_decode member).2
  have nonempty := CallReturn.Instruction.length_pos site.2
  omega

theorem decode {profile : Profile} {site : Nat × CallReturn.Instruction} {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes profile)) (member : site ∈ sites profile)
    (pc : state.rip = base + BitVec.ofNat 64 site.1) :
    CallReturn.decodeAt state = .ok site.2 :=
  CallReturn.decodeAt_code code (decode_bound profile) (inside member) state rfl pc (static_decode member).1

theorem fetchWithin {profile : Profile} {site : Nat × CallReturn.Instruction}
    {frame : StackFrame.Descriptor} {state : State}
    (code : CodeAt state.memory frame.call.code (bytes profile))
    (same : frame.call.bytes = bytes profile) (member : site ∈ sites profile)
    (pc : state.rip = frame.call.code + BitVec.ofNat 64 site.1) : CallStack.FetchWithin frame state := by
  apply CallStack.Certificates.fetchWithin_of_code (by simpa only [same] using code)
    (by rw [same]; exact decode_bound profile) (by rw [same]; exact inside member) pc
  · simpa only [same] using (static_decode member).1
  · rw [same]
    exact (static_decode member).2

end EDSL.CallMemoryLoop64.Compiler
