/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Buffer
import EDSL.X86.SyscallReturn
import EDSL.OS.Linux.Write
import EDSL.Examples.Compiler.Exit

namespace EDSL.Examples.Compiler.WriteExit
open X86

def payload : List Byte := [0x4f, 0x4b, 0x0a]
def bufferAddress : Word := 0x400022
def entryAddress : Word := 0x400000

def entryInstructions : List Byte :=
  [0xbf, 1, 0, 0, 0, 0xbe, 0x22, 0, 0x40, 0, 0xba, 3, 0, 0, 0,
   0xb8, 1, 0, 0, 0, 0x0f, 0x05]

def bytes : List Byte := entryInstructions ++ Exit42.bytes ++ payload

/-- Independent request-state contract; memory is read by the OS contract. -/
def callState (initial : State) : State :=
  { initial with
    registers := fun register => if register = .rax then 1
      else if register = .rdi then 1
      else if register = .rsi then bufferAddress
      else if register = .rdx then 3 else initial.registers register
    rip := initial.rip + 20 }

def request (initial : State) : SyscallRequest :=
  ⟨callState initial, initial.rip + 22⟩

theorem actual_bytes_invoke (initial : State)
    (code : CodeAt initial.memory initial.rip bytes) :
    runToSyscall 5 initial = .ok ⟨request initial, 5⟩ := by
  have b0 := code.2 0 191 (by decide)
  have b1 := code.2 1 1 (by decide)
  have b2 := code.2 2 0 (by decide)
  have b3 := code.2 3 0 (by decide)
  have b4 := code.2 4 0 (by decide)
  have b5 := code.2 5 190 (by decide)
  have b6 := code.2 6 34 (by decide)
  have b7 := code.2 7 0 (by decide)
  have b8 := code.2 8 64 (by decide)
  have b9 := code.2 9 0 (by decide)
  have b10 := code.2 10 186 (by decide)
  have b11 := code.2 11 3 (by decide)
  have b12 := code.2 12 0 (by decide)
  have b13 := code.2 13 0 (by decide)
  have b14 := code.2 14 0 (by decide)
  have b15 := code.2 15 184 (by decide)
  have b16 := code.2 16 1 (by decide)
  have b17 := code.2 17 0 (by decide)
  have b18 := code.2 18 0 (by decide)
  have b19 := code.2 19 0 (by decide)
  have b20 := code.2 20 15 (by decide)
  have b21 := code.2 21 5 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21
  simp [runToSyscall, step, decodeAt, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, executeMov32, State.writeRegister,
    BitVec.add_assoc, request, callState, bufferAddress, joinDWord]
  funext register
  cases register <;> rfl

theorem reaches_write (initial : State) (code : CodeAt initial.memory initial.rip bytes) :
    Invokes initial (request initial) 5 ∧ ¬ Diverges initial ∧
    ∀ other count, Invokes initial other count → other = request initial ∧ count = 5 := by
  have invocation := runToSyscall_sound (actual_bytes_invoke initial code)
  exact ⟨invocation, invocation.no_user_divergence, fun _ _ other => other.deterministic invocation⟩

theorem request_supported (initial : State) :
    OS.LinuxWrite.supported (request initial) payload ∧
    (request initial).argument .first = 1 ∧
    (request initial).argument .second = bufferAddress := by
  simp [OS.LinuxWrite.supported, request, callState, SyscallRequest.number,
    SyscallRequest.argument, payload]

theorem exit_window (initial : State) (code : CodeAt initial.memory initial.rip bytes) :
    CodeAt initial.memory (initial.rip + 22) Exit42.bytes := by
  apply code.window 22 (by decide)
  · have bound := code.1
    change initial.rip.toNat + 37 ≤ 2^64 at bound
    omega
  · intro index byte present
    match index with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 =>
      simp [Exit42.bytes] at present
      subst byte
      rfl
    | index + 12 => simp [Exit42.bytes] at present

theorem payload_readable (initial : State) (code : CodeAt initial.memory initial.rip bytes)
    (fixed : initial.rip = entryAddress) :
    BufferAt initial.memory bufferAddress payload := by
  have data : CodeAt initial.memory (initial.rip + 34) payload := by
    apply code.window 34 (by decide)
    · have bound := code.1
      change initial.rip.toNat + 37 ≤ 2^64 at bound
      omega
    · intro index byte present
      match index with
      | 0 | 1 | 2 =>
        simp [payload] at present
        subst byte
        rfl
      | index + 3 => simp [payload] at present
  have address : initial.rip + 34 = bufferAddress := by rw [fixed]; rfl
  rw [address] at data
  exact data.readable

/-- Every admitted raw result, including partial success and errors, resumes
at checked exit bytes. No flags or RCX/R11 value is assumed after return. -/
theorem exits_after_write (initial after : State) (outcome : OS.LinuxWrite.Outcome)
    (code : CodeAt initial.memory initial.rip bytes)
    (returned : Returns (request initial) (OS.LinuxWrite.rawResult outcome) after) :
    Invokes after (Exit42.request after) 3 ∧ ¬ Diverges after ∧
    OS.LinuxExit.supported (Exit42.request after) ∧
    OS.LinuxExit.status (Exit42.request after) = 42 := by
  have window := exit_window initial code
  have afterCode : CodeAt after.memory after.rip Exit42.bytes := by
    rw [returned.memory, returned.continuation]
    exact window
  have invocation := Exit42.reaches_request after afterCode
  exact ⟨invocation.1, invocation.2.1, Exit42.request_supported after, Exit42.requested_status after⟩

end EDSL.Examples.Compiler.WriteExit
