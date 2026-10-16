/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Decode

namespace EDSL.X86.Sequential

private def SuccessRefines (source destination : Except Error α) : Prop :=
  ∀ value, source = .ok value → destination = .ok value

private theorem SuccessRefines.refl (result : Except Error α) : SuccessRefines result result :=
  fun _ success => success

private theorem SuccessRefines.bind {source destination : Except Error α}
    {left right : α → Except Error β} (first : SuccessRefines source destination)
    (rest : ∀ value, SuccessRefines (left value) (right value)) :
    SuccessRefines (source >>= left) (destination >>= right) := by
  intro value success
  cases fetched : source with
  | error fault => simp only [fetched, error_bind, reduceCtorEq] at success
  | ok byte =>
    rw [first byte fetched, ok_bind]
    exact rest byte value (by simpa only [fetched, ok_bind] using success)

private theorem SuccessRefines.ite (condition : Prop) [Decidable condition]
    {a b c d : Except Error α} (yes : SuccessRefines a b) (no : SuccessRefines c d) :
    SuccessRefines (if condition then a else c) (if condition then b else d) := by
  split <;> assumption

/-- Local transport of the unmodified legacy decoder. Only successful fetches
are transported; an inaccessible byte after the decoded instruction is irrelevant. -/
theorem legacy_decodeAt_transport {source destination : State} {instruction : X86.Instruction}
    (transport : SuccessfulFetchTransport source destination)
    (decoded : X86.decodeAt source = .ok instruction) :
    X86.decodeAt destination = .ok instruction := by
  have t0 := transport 0 (by decide)
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  simp only [BitVec.add_zero] at t0
  have refinement : SuccessRefines (X86.decodeAt source) (X86.decodeAt destination) := by
    unfold X86.decodeAt
    repeat first
      | exact SuccessRefines.refl _
      | exact t0
      | exact t1
      | exact t2
      | exact t3
      | exact t4
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value
  exact refinement instruction decoded

/-- The new decoder has the same success-preserving property when its fallback
error is fixed. That error cannot itself yield a successful instruction. -/
theorem decodeNewAt_transport {source destination : State} {instruction : Instruction} (fault : Error)
    (transport : SuccessfulFetchTransport source destination)
    (decoded : decodeNewAt source fault = .ok instruction) :
    decodeNewAt destination fault = .ok instruction := by
  have t0 := transport 0 (by decide)
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  simp only [BitVec.add_zero] at t0
  have refinement : SuccessRefines (decodeNewAt source fault) (decodeNewAt destination fault) := by
    unfold decodeNewAt
    repeat first
      | exact SuccessRefines.refl _
      | exact t0
      | exact t1
      | exact t2
      | exact t3
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value
  exact refinement instruction decoded

private def NewOpcode (opcode : Byte) : Prop :=
  opcode = 0x31 ∨ opcode = 0x48 ∨ opcode = 0x03 ∨ opcode = 0x74 ∨ opcode = 0xeb

private theorem decodeNewAt_opcode {state : State} {instruction : Instruction} {fault : Error}
    (decoded : decodeNewAt state fault = .ok instruction) :
    ∃ opcode, fetchByte state.memory state.rip = .ok opcode ∧ NewOpcode opcode := by
  cases fetched : fetchByte state.memory state.rip with
  | error error => simp only [decodeNewAt, fetched, error_bind, reduceCtorEq] at decoded
  | ok opcode =>
    refine ⟨opcode, rfl, ?_⟩
    by_cases supported : NewOpcode opcode
    · exact supported
    · simp only [NewOpcode, not_or] at supported
      rcases supported with ⟨h31, h48, h03, h74, heb⟩
      simp only [decodeNewAt, fetched, ok_bind, ite_eq_right h31, ite_eq_right h48, ite_eq_right h03,
        ite_eq_right h74, ite_eq_right heb, throw_error, reduceCtorEq] at decoded

private theorem old_rejects_new_opcode {state : State} {opcode : Byte}
    (fetched : fetchByte state.memory state.rip = .ok opcode) (newOpcode : NewOpcode opcode) :
    X86.decodeAt state = .error (.unsupportedOpcode opcode) := by
  rcases newOpcode with rfl | rfl | rfl | rfl | rfl <;> simp [X86.decodeAt, fetched]

private theorem decodeNewAt_fallback_irrelevant {state : State} {opcode : Byte}
    (fetched : fetchByte state.memory state.rip = .ok opcode) (newOpcode : NewOpcode opcode)
    (left right : Error) : decodeNewAt state left = decodeNewAt state right := by
  rcases newOpcode with rfl | rfl | rfl | rfl | rfl <;> simp [decodeNewAt, fetched]

/-- Transfer ANY successful decode to any memory/base preserving its successful
fetches at offsets below five. No equality, readability, or permission premise
is imposed on unsuccessful source fetches, including bytes beyond a final RET. -/
theorem decodeAt_transport {source destination : State} {instruction : Instruction}
    (transport : SuccessfulFetchTransport source destination)
    (decoded : decodeAt source = .ok instruction) :
    decodeAt destination = .ok instruction := by
  cases old : X86.decodeAt source with
  | ok legacy =>
    have embedded : Instruction.legacy legacy = instruction := by
      simpa only [decodeAt, old, Except.ok.injEq] using decoded
    rw [←embedded]
    exact decodeAt_legacy (legacy_decodeAt_transport transport old)
  | error fault =>
    have newly : decodeNewAt source fault = .ok instruction := by
      simpa only [decodeAt, old] using decoded
    obtain ⟨opcode, fetched, newOpcode⟩ := decodeNewAt_opcode newly
    have destinationFetch : fetchByte destination.memory destination.rip = .ok opcode := by
      have moved := transport 0 (by decide) opcode (by simpa only [BitVec.add_zero] using fetched)
      simpa only [BitVec.add_zero] using moved
    have oldDestination := old_rejects_new_opcode destinationFetch newOpcode
    have moved := decodeNewAt_transport fault transport newly
    rw [decodeAt, oldDestination]
    change decodeNewAt destination (.unsupportedOpcode opcode) = .ok instruction
    rw [←decodeNewAt_fallback_irrelevant destinationFetch newOpcode fault (.unsupportedOpcode opcode)]
    exact moved

end EDSL.X86.Sequential
