/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Buffer
import EDSL.X86.Invocation
import EDSL.X86.SyscallReturn

namespace EDSL.Examples.FutexStubs
open X86

/-- Two exact userspace function profiles. Kernel service is specified elsewhere. -/
inductive Profile where
  | wait | wakeOne
  deriving DecidableEq, Repr

def Profile.bytes : Profile → List Byte
  | .wait => [0xb8, 202, 0, 0, 0, 0xbe, 128, 0, 0, 0, 0x0f, 0x05, 0xc3]
  | .wakeOne => [0xb8, 202, 0, 0, 0, 0xbe, 129, 0, 0, 0, 0xba, 1, 0, 0, 0, 0x0f, 0x05, 0xc3]

def Profile.entryCost : Profile → Nat
  | .wait => 3
  | .wakeOne => 4

def Profile.completedCost : Profile → Nat
  | .wait => 4
  | .wakeOne => 5

def Profile.continuationOffset : Profile → Nat
  | .wait => 12
  | .wakeOne => 17

def Profile.operation : Profile → Word
  | .wait => 128
  | .wakeOne => 129

/-- An independently stated call-site register contract, retaining every
register that these byte sequences do not write. MOV32 clears high halves. -/
def callState (profile : Profile) (initial : State) : State :=
  { initial with
    registers := fun register => if register = .rax then 202
      else if register = .rsi then profile.operation
      else if profile = .wakeOne ∧ register = .rdx then 1
      else initial.registers register
    rip := initial.rip + BitVec.ofNat 64 (profile.continuationOffset - 2) }

def request (profile : Profile) (initial : State) : SyscallRequest :=
  ⟨callState profile initial, initial.rip + BitVec.ofNat 64 profile.continuationOffset⟩

/-- The narrow canonical ABI requires explicit unused zeros and a full-width
address. WAIT's expected value must already be zero extended by the caller. -/
def CanonicalArguments (profile : Profile) (initial : State) (word : Word)
    (expected : BitVec 32) : Prop :=
  initial.registers .rdi = word ∧
  (profile = .wait → initial.registers .rdx = expected.setWidth 64) ∧
  initial.registers .r10 = 0 ∧ initial.registers .r8 = 0 ∧ initial.registers .r9 = 0

def CanonicalRequest (profile : Profile) (call : SyscallRequest) (word : Word)
    (expected : BitVec 32) : Prop :=
  call.user.registers .rax = 202 ∧ call.number = 202 ∧
  call.argument .first = word ∧ call.argument .second = profile.operation ∧
  call.argument .third = (if profile = .wait then expected.setWidth 64 else 1) ∧
  call.argument .fourth = 0 ∧ call.argument .fifth = 0 ∧ call.argument .sixth = 0

private theorem wait_bytes_invoke (initial : State)
    (code : CodeAt initial.memory initial.rip Profile.wait.bytes) :
    runToSyscall 3 initial = .ok ⟨request .wait initial, 3⟩ := by
  have b0 := code.2 0 0xb8 (by decide)
  have b1 := code.2 1 202 (by decide)
  have b2 := code.2 2 0 (by decide)
  have b3 := code.2 3 0 (by decide)
  have b4 := code.2 4 0 (by decide)
  have b5 := code.2 5 0xbe (by decide)
  have b6 := code.2 6 128 (by decide)
  have b7 := code.2 7 0 (by decide)
  have b8 := code.2 8 0 (by decide)
  have b9 := code.2 9 0 (by decide)
  have b10 := code.2 10 0x0f (by decide)
  have b11 := code.2 11 0x05 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  simp [runToSyscall, step, decodeAt, b0, b1, b2, b3, b4, b5, b6, b7, b8,
    b9, b10, b11, executeMov32, State.writeRegister, BitVec.add_assoc, request,
    callState, Profile.continuationOffset, Profile.operation, joinDWord]
  funext register
  cases register <;> rfl

private theorem wake_bytes_invoke (initial : State)
    (code : CodeAt initial.memory initial.rip Profile.wakeOne.bytes) :
    runToSyscall 4 initial = .ok ⟨request .wakeOne initial, 4⟩ := by
  have b0 := code.2 0 0xb8 (by decide)
  have b1 := code.2 1 202 (by decide)
  have b2 := code.2 2 0 (by decide)
  have b3 := code.2 3 0 (by decide)
  have b4 := code.2 4 0 (by decide)
  have b5 := code.2 5 0xbe (by decide)
  have b6 := code.2 6 129 (by decide)
  have b7 := code.2 7 0 (by decide)
  have b8 := code.2 8 0 (by decide)
  have b9 := code.2 9 0 (by decide)
  have b10 := code.2 10 0xba (by decide)
  have b11 := code.2 11 1 (by decide)
  have b12 := code.2 12 0 (by decide)
  have b13 := code.2 13 0 (by decide)
  have b14 := code.2 14 0 (by decide)
  have b15 := code.2 15 0x0f (by decide)
  have b16 := code.2 16 0x05 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
  simp [runToSyscall, step, decodeAt, b0, b1, b2, b3, b4, b5, b6, b7, b8,
    b9, b10, b11, b12, b13, b14, b15, b16, executeMov32, State.writeRegister,
    BitVec.add_assoc, request, callState, Profile.continuationOffset, Profile.operation, joinDWord]
  funext register
  cases register <;> rfl

theorem actual_bytes_invoke (profile : Profile) (initial : State)
    (code : CodeAt initial.memory initial.rip profile.bytes) :
    runToSyscall profile.entryCost initial = .ok ⟨request profile initial, profile.entryCost⟩ := by
  cases profile
  · exact wait_bytes_invoke initial code
  · exact wake_bytes_invoke initial code

theorem reaches_request (profile : Profile) (initial : State)
    (code : CodeAt initial.memory initial.rip profile.bytes) :
    Invokes initial (request profile initial) profile.entryCost ∧ ¬ Diverges initial ∧
    ∀ other count, Invokes initial other count →
      other = request profile initial ∧ count = profile.entryCost := by
  have invocation := runToSyscall_sound (actual_bytes_invoke profile initial code)
  exact ⟨invocation, invocation.no_user_divergence, fun _ _ other => other.deterministic invocation⟩

theorem request_canonical (profile : Profile) (initial : State) (word : Word)
    (expected : BitVec 32) (arguments : CanonicalArguments profile initial word expected) :
    CanonicalRequest profile (request profile initial) word expected := by
  rcases arguments with ⟨address, value, fourth, fifth, sixth⟩
  cases profile <;>
    simp [CanonicalRequest, request, callState, Profile.operation, SyscallRequest.number,
      SyscallRequest.argument, address, value, fourth, fifth, sixth]

/-- Post-RET state: only RSP and RIP change from the admitted return state. -/
def returnFinal (after : State) (target : Word) : State :=
  { after with
    registers := fun register =>
      if register = .rsp then after.registers .rsp + 8 else after.registers register
    rip := target }

private theorem ret_window (profile : Profile) (initial : State) (current : Memory)
    (code : CodeAt current initial.rip profile.bytes) :
    CodeAt current (request profile initial).continuation [0xc3] := by
  change CodeAt current (initial.rip + BitVec.ofNat 64 profile.continuationOffset) [0xc3]
  cases profile with
  | wait =>
    apply code.window 12 (by decide)
    · have bound := code.1
      change initial.rip.toNat + 13 ≤ 2^64 at bound
      omega
    · intro index byte present
      cases index with
      | zero => simpa [Profile.bytes] using present
      | succ index => simp at present
  | wakeOne =>
    apply code.window 17 (by decide)
    · have bound := code.1
      change initial.rip.toNat + 18 ≤ 2^64 at bound
      omega
    · intro index byte present
      cases index with
      | zero => simpa [Profile.bytes] using present
      | succ index => simp at present

/-- Every admitted service result, including full-width negative errno values,
returns through the actual RET in current RAM. This does not assert that a
kernel services a request, that zero implies acquisition, or that a wait ends. -/
theorem returns_correct (profile : Profile) (initial after : State) (current : Memory)
    (raw target : Word)
    (code : CodeAt current initial.rip profile.bytes)
    (returned : ReturnsAt (request profile initial) current raw after)
    (stack : readWord current (initial.registers .rsp) = .ok target)
    (returnValid : canonical target = true) :
    Executes after (returnFinal after target) 1 ∧ ¬ Diverges after ∧
    (∀ final count, Executes after final count → final = returnFinal after target ∧ count = 1) ∧
    (returnFinal after target).registers .rax = raw ∧
    (returnFinal after target).registers .rsp = initial.registers .rsp + 8 ∧
    (returnFinal after target).memory = current ∧
    profile.entryCost + 1 = profile.completedCost := by
  have rsp : after.registers .rsp = initial.registers .rsp := by
    simpa [request, callState] using returned.register .rsp (by decide) (by decide) (by decide)
  have afterCode : CodeAt after.memory after.rip [0xc3] := by
    rw [returned.memory, returned.continuation]
    exact ret_window profile initial current code
  have b0 := afterCode.2 0 0xc3 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0
  have actual : run 1 after = .ok ⟨returnFinal after target, 1⟩ := by
    have afterStack : readWord after.memory (after.registers .rsp) = .ok target := by
      rw [returned.memory, rsp]
      exact stack
    simp [run, step, decodeAt, b0, executeRet, afterStack, returnValid, returnFinal,
      State.writeRegister]
  have execution := run_sound actual
  refine ⟨execution, execution.no_divergence, fun _ _ other => other.deterministic execution,
    ?_, ?_, returned.memory, ?_⟩
  · simpa [returnFinal] using returned.result
  · simp [returnFinal, rsp]
  · cases profile <;> rfl

end EDSL.Examples.FutexStubs
