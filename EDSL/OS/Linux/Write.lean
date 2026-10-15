/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Syscall

namespace EDSL.OS.LinuxWrite
open X86

/-- Positive raw Linux errno range. This is the userspace return encoding,
not libc's separate `errno` storage. -/
structure Errno where
  code : Nat
  positive : 0 < code
  bounded : code ≤ 4095
  deriving DecidableEq

inductive Outcome where
  | accepted (count : Nat)
  | failed (error : Errno)
  deriving DecidableEq

/-- A return may report any prefix length, including zero, or a raw error.
No full-write or progress guarantee follows from this contract. -/
def Permitted (payload : List Byte) : Outcome → Prop
  | .accepted count => count ≤ payload.length
  | .failed _ => True

instance (payload : List Byte) (outcome : Outcome) : Decidable (Permitted payload outcome) :=
  match outcome with
  | .accepted count => inferInstanceAs (Decidable (count ≤ payload.length))
  | .failed _ => isTrue trivial

def emitted (payload : List Byte) : Outcome → List Byte
  | .accepted count => payload.take count
  | .failed _ => []

def rawResult : Outcome → Word
  | .accepted count => BitVec.ofNat 64 count
  | .failed error => -(BitVec.ofNat 64 error.code)

/-- Raw write dispatch and a bounded byte count. The caller separately binds
the buffer to readable memory and the descriptor to the admitted sink. -/
def supported (request : SyscallRequest) (payload : List Byte) : Prop :=
  request.number = 1 ∧
    request.argument .third = BitVec.ofNat 64 payload.length ∧ payload.length ≤ 4096

theorem emitted_prefix (payload : List Byte) (outcome : Outcome) :
    List.IsPrefix (emitted payload outcome) payload := by
  cases outcome with
  | accepted count => exact ⟨payload.drop count, List.take_append_drop count payload⟩
  | failed _ => exact ⟨payload, rfl⟩

theorem emitted_length_le (payload : List Byte) (outcome : Outcome) :
    (emitted payload outcome).length ≤ payload.length := by
  cases outcome with
  | accepted count => exact List.length_take_le' count payload
  | failed _ => exact Nat.zero_le _

theorem accepted_length (payload : List Byte) (count : Nat)
    (allowed : Permitted payload (.accepted count)) :
    (emitted payload (.accepted count)).length = count := by
  exact List.length_take_of_le allowed

theorem full_success (payload : List Byte) :
    emitted payload (.accepted payload.length) = payload := by
  simp [emitted]

theorem error_emits_nothing (payload : List Byte) (error : Errno) :
    emitted payload (.failed error) = [] := rfl

theorem accepted_result (payload : List Byte) (count : Nat)
    (bounded : payload.length ≤ 4096) (allowed : Permitted payload (.accepted count)) :
    (rawResult (.accepted count)).toNat = count := by
  have countBound : count < 2^64 := by
    change count ≤ payload.length at allowed
    omega
  simp [rawResult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound]

/-- Every raw error is the signed negative errno, without the libc conversion. -/
theorem failed_result (error : Errno) :
    (rawResult (.failed error)).toInt = -(error.code : Int) := by
  have bound := error.bounded
  have codeBound : error.code < 2^64 := by omega
  have valueNat : (BitVec.ofNat 64 error.code).toNat = error.code := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt codeBound]
  have small : 2 * (BitVec.ofNat 64 error.code).toNat < 2^64 := by
    rw [valueNat]
    omega
  rw [rawResult, BitVec.toInt_neg_eq_of_msb
    (BitVec.msb_eq_false_iff_two_mul_lt.mpr small),
    BitVec.toInt_eq_toNat_of_lt small, valueNat]

theorem failed_result_negative (error : Errno) :
    (rawResult (.failed error)).toInt < 0 := by
  rw [failed_result]
  have := error.positive
  omega

def eintr : Errno := ⟨4, by decide, by decide⟩
def eagain : Errno := ⟨11, by decide, by decide⟩

theorem raw_eintr : (rawResult (.failed eintr)).toInt = -4 := by decide
theorem raw_eagain : (rawResult (.failed eagain)).toInt = -11 := by decide

theorem eintr_is_not_libc_failure : (rawResult (.failed eintr)).toInt ≠ -1 := by decide
theorem eagain_is_not_libc_failure : (rawResult (.failed eagain)).toInt ≠ -1 := by decide

/-- Observable operation phases for one externally owned, stable byte-stream
sink, with no concurrent writers or descriptor mutation. A successful prefix
append is observed only after return: intermediate visibility and atomicity of
the real write are not modeled. Regular files, direct I/O, devices, durability,
descriptor lookup, kernel execution and resource cleanup are outside this
contract. A failed operation emits nothing in this admitted sink profile. -/
inductive Phase where
  | pending
  | done (outcome : Outcome)
  deriving DecidableEq

inductive Step (payload : List Byte) : Phase → Phase → Prop where
  | wait : Step payload .pending .pending
  | finish {outcome} (allowed : Permitted payload outcome) :
      Step payload .pending (.done outcome)
  | stopped {outcome} : Step payload (.done outcome) (.done outcome)

/-- Finite transition closure; it includes waiting and does not require return. -/
inductive Execution (payload : List Byte) : Phase → Phase → Prop where
  | refl {phase} : Execution payload phase phase
  | next {before middle after} (first : Step payload before middle)
      (rest : Execution payload middle after) : Execution payload before after

def observable (payload : List Byte) : Phase → List Byte
  | .pending => []
  | .done outcome => emitted payload outcome

def Trace (payload : List Byte) (trace : Nat → Phase) : Prop :=
  trace 0 = .pending ∧ ∀ index, Step payload (trace index) (trace (index + 1))

theorem Step.preserves (payload : List Byte) {before after : Phase}
    (transition : Step payload before after)
    (invariant : before = .pending ∨
      ∃ outcome, Permitted payload outcome ∧ before = .done outcome) :
    after = .pending ∨ ∃ outcome, Permitted payload outcome ∧ after = .done outcome := by
  cases transition with
  | wait => exact Or.inl rfl
  | finish allowed => exact Or.inr ⟨_, allowed, rfl⟩
  | stopped => exact invariant

theorem Execution.preserves (payload : List Byte) {before after : Phase}
    (execution : Execution payload before after)
    (invariant : before = .pending ∨
      ∃ outcome, Permitted payload outcome ∧ before = .done outcome) :
    after = .pending ∨ ∃ outcome, Permitted payload outcome ∧ after = .done outcome := by
  induction execution with
  | refl => exact invariant
  | next first _ induction => exact induction (Step.preserves payload first invariant)

theorem execution_result (payload : List Byte) (outcome : Outcome)
    (execution : Execution payload .pending (.done outcome)) : Permitted payload outcome := by
  rcases Execution.preserves payload execution (Or.inl rfl) with impossible | ⟨result, allowed, same⟩
  · cases impossible
  · exact (Phase.done.inj same).symm ▸ allowed

theorem trace_state (payload : List Byte) (trace : Nat → Phase)
    (execution : Trace payload trace) (index : Nat) :
    trace index = .pending ∨
      ∃ outcome, Permitted payload outcome ∧ trace index = .done outcome := by
  induction index with
  | zero => exact Or.inl execution.1
  | succ index induction => exact Step.preserves payload (execution.2 index) induction

theorem done_permitted (payload : List Byte) (trace : Nat → Phase)
    (execution : Trace payload trace) (index : Nat) (outcome : Outcome)
    (returned : trace index = .done outcome) : Permitted payload outcome := by
  rcases trace_state payload trace execution index with pending | ⟨result, allowed, same⟩
  · rw [returned] at pending
    cases pending
  · exact (Phase.done.inj (returned.symm.trans same)).symm ▸ allowed

theorem observable_prefix (payload : List Byte) (phase : Phase) :
    List.IsPrefix (observable payload phase) payload := by
  cases phase with
  | pending => exact ⟨payload, rfl⟩
  | done outcome => exact emitted_prefix payload outcome

theorem completed_safety (payload : List Byte) (trace : Nat → Phase)
    (execution : Trace payload trace) (index : Nat) (outcome : Outcome)
    (returned : trace index = .done outcome) :
    Permitted payload outcome ∧
      observable payload (trace index) = emitted payload outcome ∧
      List.IsPrefix (observable payload (trace index)) payload ∧
      (observable payload (trace index)).length ≤ payload.length := by
  refine ⟨done_permitted payload trace execution index outcome returned, ?_⟩
  rw [returned]
  exact ⟨rfl, emitted_prefix payload outcome, emitted_length_le payload outcome⟩

/-- Arbitrary waiting is admitted, so return is never concluded unconditionally. -/
theorem indefinite_wait (payload : List Byte) : Trace payload (fun _ => .pending) :=
  ⟨rfl, fun _ => .wait⟩

def immediate (outcome : Outcome) : Nat → Phase
  | 0 => .pending
  | _ + 1 => .done outcome

/-- Each permitted partial success or error has an actual admitted trace. -/
theorem immediate_admitted (payload : List Byte) (outcome : Outcome)
    (allowed : Permitted payload outcome) : Trace payload (immediate outcome) := by
  refine ⟨rfl, ?_⟩
  intro index
  cases index with
  | zero => exact .finish allowed
  | succ _ => exact .stopped

theorem every_outcome_possible (payload : List Byte) (outcome : Outcome)
    (allowed : Permitted payload outcome) :
    ∃ trace, Trace payload trace ∧ trace 1 = .done outcome :=
  ⟨immediate outcome, immediate_admitted payload outcome allowed, rfl⟩

end EDSL.OS.LinuxWrite
