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

/-- Return-to-userspace contract using the memory supplied at resumption.
Concurrent execution may have changed that memory since the request. This
contract specifies only the returning thread's register state and retains
`current` exactly, including its byte contents and permissions. The caller is
responsible for supplying the actual current memory and any required code
evidence. Flags, RCX and R11 remain unconstrained, as in `Returns`.
-/
def ReturnsAt (request : SyscallRequest) (current : Memory) (raw : Word)
    (after : State) : Prop :=
  after.rip = request.continuation ∧
  after.registers .rax = raw ∧
  after.memory = current ∧
  ∀ register, register ≠ .rax → register ≠ .rcx → register ≠ .r11 →
    after.registers register = request.user.registers register

/-- Construct a return state with the supplied current memory and arbitrary
flags, RCX and R11. The raw result occupies the full 64-bit RAX register. -/
def resumeAt (request : SyscallRequest) (current : Memory)
    (raw flags rcx r11 : Word) : State :=
  { registers := fun register =>
      if register = .rax then raw
      else if register = .rcx then rcx
      else if register = .r11 then r11
      else request.user.registers register
    rip := request.continuation
    flags := flags
    memory := current }

theorem resumeAt_returnsAt (request : SyscallRequest) (current : Memory)
    (raw flags rcx r11 : Word) :
    ReturnsAt request current raw (resumeAt request current raw flags rcx r11) := by
  refine ⟨rfl, by simp [resumeAt], rfl, ?_⟩
  intro register notRax notRcx notR11
  simp [resumeAt, notRax, notRcx, notR11]

/-- Consistency for every current memory and raw result, without a claim that
a real kernel or scheduler completes the syscall. -/
theorem returnsAt_nonempty (request : SyscallRequest) (current : Memory) (raw : Word) :
    ∃ after, ReturnsAt request current raw after :=
  ⟨resumeAt request current raw 0 0 0, resumeAt_returnsAt request current raw 0 0 0⟩

namespace ReturnsAt

theorem continuation {request : SyscallRequest} {current : Memory} {raw : Word} {after : State}
    (returned : ReturnsAt request current raw after) : after.rip = request.continuation :=
  returned.1

theorem result {request : SyscallRequest} {current : Memory} {raw : Word} {after : State}
    (returned : ReturnsAt request current raw after) : after.registers .rax = raw :=
  returned.2.1

theorem memory {request : SyscallRequest} {current : Memory} {raw : Word} {after : State}
    (returned : ReturnsAt request current raw after) : after.memory = current :=
  returned.2.2.1

theorem register {request : SyscallRequest} {current : Memory} {raw : Word} {after : State}
    (returned : ReturnsAt request current raw after) (register : Register)
    (notRax : register ≠ .rax) (notRcx : register ≠ .rcx) (notR11 : register ≠ .r11) :
    after.registers register = request.user.registers register :=
  returned.2.2.2 register notRax notRcx notR11

/-- Executable-byte evidence from the current memory survives resumption.
Evidence from request entry alone does not establish this premise. -/
theorem preserves_code {request : SyscallRequest} {current : Memory} {raw : Word} {after : State}
    (returned : ReturnsAt request current raw after) {base : Word} {bytes : List Byte}
    (code : CodeAt current base bytes) : CodeAt after.memory base bytes := by
  rw [returned.memory]
  exact code

/-- Every admitted return is exactly the constructor applied to that state's
flags, RCX and R11; all fields of `State` are accounted for. -/
theorem eq_resumeAt {request : SyscallRequest} {current : Memory} {raw : Word} {after : State}
    (returned : ReturnsAt request current raw after) :
    after = resumeAt request current raw after.flags
      (after.registers .rcx) (after.registers .r11) := by
  have registers : after.registers =
      (resumeAt request current raw after.flags
        (after.registers .rcx) (after.registers .r11)).registers := by
    funext register
    by_cases isRax : register = .rax
    · subst register
      simpa [resumeAt] using returned.result
    · by_cases isRcx : register = .rcx
      · subst register
        simp [resumeAt]
      · by_cases isR11 : register = .r11
        · subst register
          simp [resumeAt]
        · simpa [resumeAt, isRax, isRcx, isR11] using
            returned.register register isRax isRcx isR11
  cases after
  simp only [resumeAt, State.mk.injEq]
  exact ⟨registers, returned.continuation, True.intro, returned.memory⟩

end ReturnsAt

/-- The existing memory-unchanged contract is precisely the entry-memory
instance of the concurrent-memory return contract. -/
theorem returnsAt_entryMemory_iff_returns (request : SyscallRequest) (raw : Word)
    (after : State) :
    ReturnsAt request request.user.memory raw after ↔ Returns request raw after :=
  Iff.rfl

theorem resume_eq_resumeAt (request : SyscallRequest) (raw flags rcx r11 : Word) :
    resume request raw flags rcx r11 =
      resumeAt request request.user.memory raw flags rcx r11 := rfl

/-- Exact full-state characterization, using the admitted state's own freely
chosen flags, RCX and R11. -/
theorem returnsAt_iff_eq_resumeAt (request : SyscallRequest) (current : Memory)
    (raw : Word) (after : State) :
    ReturnsAt request current raw after ↔
      after = resumeAt request current raw after.flags
        (after.registers .rcx) (after.registers .r11) := by
  constructor
  · exact ReturnsAt.eq_resumeAt
  · intro equal
    rw [equal]
    exact resumeAt_returnsAt request current raw _ _ _

/-- Flags, RCX and R11 are the only choices in the complete return state. -/
theorem returnsAt_iff_exists_resumeAt (request : SyscallRequest) (current : Memory)
    (raw : Word) (after : State) :
    ReturnsAt request current raw after ↔
      ∃ flags rcx r11, after = resumeAt request current raw flags rcx r11 := by
  constructor
  · intro returned
    exact ⟨after.flags, after.registers .rcx, after.registers .r11, returned.eq_resumeAt⟩
  · rintro ⟨flags, rcx, r11, rfl⟩
    exact resumeAt_returnsAt request current raw flags rcx r11

end EDSL.X86
