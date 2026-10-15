/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Syscall

namespace EDSL.X86

/-- Explicit Linux x86-64 return-to-userspace contract for a syscall that leaves
userspace memory unchanged, initially intended for the modeled write subset.

This contract assumes no asynchronous interference. It is not a specification
of every syscall, privileged entry/return instructions, or a kernel proof.
Flags, RCX and R11 are deliberately unconstrained: callers may not rely on their
values after return. The return value is its raw 64-bit register representation.
-/
def Returns (request : SyscallRequest) (value : Word) (after : State) : Prop :=
  after.rip = request.continuation ∧
  after.registers .rax = value ∧
  after.memory = request.user.memory ∧
  ∀ register, register ≠ .rax → register ≠ .rcx → register ≠ .r11 →
    after.registers register = request.user.registers register

/-- Construct an admitted return state. The explicit arguments for the flags,
RCX and R11 make their lack of a promised value visible to consumers. -/
def resume (request : SyscallRequest) (value flags rcx r11 : Word) : State :=
  { registers := fun register =>
      if register = .rax then value
      else if register = .rcx then rcx
      else if register = .r11 then r11
      else request.user.registers register
    rip := request.continuation
    flags := flags
    memory := request.user.memory }

theorem resume_returns (request : SyscallRequest) (value flags rcx r11 : Word) :
    Returns request value (resume request value flags rcx r11) := by
  refine ⟨rfl, by simp [resume], rfl, ?_⟩
  intro register notRax notRcx notR11
  simp [resume, notRax, notRcx, notR11]

/-- The return contract admits a state for every raw result value. This is
contract consistency, not a claim that a real kernel completes the syscall. -/
theorem returns_nonempty (request : SyscallRequest) (value : Word) :
    ∃ after, Returns request value after :=
  ⟨resume request value 0 0 0, resume_returns request value 0 0 0⟩

namespace Returns

theorem continuation {request : SyscallRequest} {value : Word} {after : State}
    (returned : Returns request value after) : after.rip = request.continuation :=
  returned.1

theorem result {request : SyscallRequest} {value : Word} {after : State}
    (returned : Returns request value after) : after.registers .rax = value :=
  returned.2.1

theorem memory {request : SyscallRequest} {value : Word} {after : State}
    (returned : Returns request value after) : after.memory = request.user.memory :=
  returned.2.2.1

theorem register {request : SyscallRequest} {value : Word} {after : State}
    (returned : Returns request value after) (register : Register)
    (notRax : register ≠ .rax) (notRcx : register ≠ .rcx) (notR11 : register ≠ .r11) :
    after.registers register = request.user.registers register :=
  returned.2.2.2 register notRax notRcx notR11

/-- Exact executable-byte evidence survives every admitted return, including
returns that choose different flags, RCX or R11 values. -/
theorem preserves_code {request : SyscallRequest} {value : Word} {after : State}
    (returned : Returns request value after) {base : Word} {bytes : List Byte}
    (code : CodeAt request.user.memory base bytes) : CodeAt after.memory base bytes := by
  rw [returned.memory]
  exact code

end Returns

end EDSL.X86
