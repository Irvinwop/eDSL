/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemoryLoop64.Admission
import EDSL.CallStack.Certificates

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.ClosedForm
open X86 OS

/-- Compile-only GNU23 -Os probe profiles; neither profile contains a helper.
The public fixture is bound afresh to compiler artifacts by the root runner. -/
inductive Profile where
  | gcc | clang
  deriving DecidableEq, Repr

def bytes : Profile → List Byte
  | .gcc =>
    [0x48,0x8d,0x04,0x16,0x48,0x85,0xd2,0x74,0x07,
     0x48,0x8d,0x50,0xff,0x48,0x89,0x17,0xc3]
  | .clang =>
    [0x48,0x89,0xf0,0x48,0x01,0xd0,0x48,0x85,0xd2,0x74,0x07,
     0x48,0x8d,0x48,0xff,0x48,0x89,0x0f,0xc3]

def program (profile : Profile) : Program := ⟨bytes profile, 0⟩

/-- Expected operations from the two actual compiler disassemblies. The
decoder below checks every instruction, prefix, SIB, displacement and extent. -/
def sites : Profile → List (Nat × CallReturn.Instruction)
  | .gcc =>
    [(0,.sequential (.lea64 .rax (.indexed .rsi .rdx 0))),
     (4,.sequential (.test64 .rdx .rdx)), (7,.sequential (.je 7)),
     (9,.leaDisp8 .rdx (.plain .rax) 0xff),
     (13,.sequential (.storeMem64 (.base .rdi) .rdx)),
     (16,.sequential (.legacy .ret))]
  | .clang =>
    [(0,.sequential (.movReg64 .rax .rsi)), (3,.sequential (.addReg64 .rax .rdx)),
     (6,.sequential (.test64 .rdx .rdx)), (9,.sequential (.je 7)),
     (11,.leaDisp8 .rcx (.plain .rax) 0xff),
     (15,.sequential (.storeMem64 (.base .rdi) .rcx)),
     (18,.sequential (.legacy .ret))]

def testOffset : Profile → Nat | .gcc => 4 | .clang => 6
def guardOffset : Profile → Nat | .gcc => 7 | .clang => 9
def predOffset : Profile → Nat | .gcc => 9 | .clang => 11
def storeOffset : Profile → Nat | .gcc => 13 | .clang => 15
def retOffset : Profile → Nat | .gcc => 16 | .clang => 18
def scratch : Profile → Register | .gcc => .rdx | .clang => .rcx
def frontCost : Profile → Nat | .gcc => 2 | .clang => 3

/-- Exact instruction costs are conclusions of the constructed execution,
separate from the fixed independent semantic contract and admission. -/
def cost (profile : Profile) (count : Word) : Nat :=
  frontCost profile + if count = 0 then 2 else 4

theorem positive (profile : Profile) : 0 < (bytes profile).length := by
  cases profile <;> decide

theorem decode_bound (profile : Profile) : (bytes profile).length ≤ 64 := by
  cases profile <;> decide

theorem bounded (profile : Profile) : (bytes profile).length ≤ 4096 :=
  Nat.le_trans (decode_bound profile) (by decide)

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
  CallReturn.decodeAt_code code (decode_bound profile) (inside member) state rfl pc
    (static_decode member).1

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

end EDSL.CallMemoryLoop64.ClosedForm
