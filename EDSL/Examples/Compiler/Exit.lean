/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Invocation
import EDSL.OS.Linux.Exit

namespace EDSL.Examples.Compiler.Exit42
open X86

def bytes : List Byte := [0xbf, 42, 0, 0, 0, 0xb8, 60, 0, 0, 0, 0x0f, 0x05]

/-- Independent call-site register contract; no caller stack is read. -/
def callState (initial : State) : State :=
  { initial with
    registers := fun register => if register = .rax then 60
      else if register = .rdi then 42 else initial.registers register
    rip := initial.rip + 10 }

def request (initial : State) : SyscallRequest := ⟨callState initial, initial.rip + 12⟩

theorem moves_match (initial : State) :
    executeMov32 (executeMov32 initial .rdi 42) .rax 60 = callState initial := by
  simp [executeMov32, State.writeRegister, callState, BitVec.add_assoc]

theorem actual_bytes_invoke (initial : State)
    (code : CodeAt initial.memory initial.rip bytes) :
    runToSyscall 3 initial = .ok ⟨request initial, 3⟩ := by
  have b0 := code.2 0 0xbf (by decide)
  have b1 := code.2 1 42 (by decide)
  have b2 := code.2 2 0 (by decide)
  have b3 := code.2 3 0 (by decide)
  have b4 := code.2 4 0 (by decide)
  have b5 := code.2 5 0xb8 (by decide)
  have b6 := code.2 6 60 (by decide)
  have b7 := code.2 7 0 (by decide)
  have b8 := code.2 8 0 (by decide)
  have b9 := code.2 9 0 (by decide)
  have b10 := code.2 10 0x0f (by decide)
  have b11 := code.2 11 0x05 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  simp [runToSyscall, step, decodeAt, b0, b1, b2, b3, b4, b5, b6, b7, b8,
    b9, b10, b11, executeMov32, State.writeRegister, BitVec.add_assoc, request, callState, joinDWord]

theorem reaches_request (initial : State) (code : CodeAt initial.memory initial.rip bytes) :
    Invokes initial (request initial) 3 ∧ ¬ Diverges initial ∧
    ∀ other count, Invokes initial other count → other = request initial ∧ count = 3 := by
  have invocation := runToSyscall_sound (actual_bytes_invoke initial code)
  exact ⟨invocation, invocation.no_user_divergence, fun _ _ other => other.deterministic invocation⟩

theorem request_supported (initial : State) : OS.LinuxExit.supported (request initial) := by
  simp [OS.LinuxExit.supported, SyscallRequest.number, request, callState]

theorem requested_status (initial : State) : OS.LinuxExit.status (request initial) = 42 := by
  simp [OS.LinuxExit.status, SyscallRequest.argument, request, callState]

/-- Every candidate in the supported ISA that requests raw exit60/status42
from zero RAX/RDI needs at least three user instructions, counting SYSCALL.
This is neither an all-x86 optimum nor a bound on kernel work or elapsed time. -/
theorem zero_register_lower_bound {initial : State} {call : SyscallRequest} {count : Nat}
    (execution : Invokes initial call count)
    (initialNumber : initial.registers .rax = 0)
    (initialArgument : initial.registers .rdi = 0)
    (allowed : OS.LinuxExit.supported call)
    (result : OS.LinuxExit.status call = 42) : 3 ≤ count := by
  apply execution.changing_two_registers_costs_three
  · intro unchanged
    simp [OS.LinuxExit.supported, SyscallRequest.number, unchanged, initialNumber] at allowed
  · intro unchanged
    simp [OS.LinuxExit.status, SyscallRequest.argument, unchanged, initialArgument] at result

/-- All completed kernel traces agree; eventual completion separately requires
weak progress of the abstract cleanup action. No kernel implementation is proved. -/
theorem kernel_results (initial : State) (trace : Nat → OS.LinuxExit.Phase)
    (execution : OS.LinuxExit.Trace (request initial) trace) :
    (∀ index status, trace index = .exited status → status = 42) ∧
    (OS.LinuxExit.Fair trace → ∃ index, trace index = .exited 42) := by
  constructor
  · intro index status exited
    exact (OS.LinuxExit.exited_status _ _ execution index status exited).trans (requested_status initial)
  · intro fair
    simpa only [requested_status] using OS.LinuxExit.fair_eventually_exits _ _ execution fair

end EDSL.Examples.Compiler.Exit42
