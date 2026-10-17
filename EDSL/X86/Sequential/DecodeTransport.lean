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

private theorem decodeAddressAt_refines {source destination : State} (modrm : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeAddressAt source modrm) (decodeAddressAt destination modrm) := by
  have t2 := transport 2 (by decide)
  unfold decodeAddressAt
  repeat first
    | exact SuccessRefines.refl _
    | exact t2
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

private theorem decodeQWordAddressAt_refines {source destination : State} (rex modrm : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeQWordAddressAt source rex modrm) (decodeQWordAddressAt destination rex modrm) := by
  have t3 := transport 3 (by decide)
  unfold decodeQWordAddressAt
  repeat first
    | exact SuccessRefines.refl _
    | exact t3
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

private theorem decodeREXWAt_refines {source destination : State} (rex : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeREXWAt source rex) (decodeREXWAt destination rex) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  unfold decodeREXWAt
  repeat first
    | exact SuccessRefines.refl _
    | exact t1
    | exact t2
    | exact t3
    | exact decodeQWordAddressAt_refines _ _ transport
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

/-- New decoding, including LEA's SIB fetch, both register ADD directions,
CMOV's condition opcode and register operands, and short Jcc displacements,
preserves success under the same fetch transport. A fixed fallback error
cannot itself yield a successful instruction. -/
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
      | exact decodeAddressAt_refines _ transport
      | exact decodeREXWAt_refines _ transport
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value
  exact refinement instruction decoded

private def NewJccOpcode (opcode : Byte) : Prop :=
  0x70 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x7f ∧ opcode ≠ 0x75#8

/-- Opcode 75 belongs to the legacy decoder, so it is deliberately excluded
from the new-opcode disjointness argument. Opcode 74 keeps its JE constructor. -/
private theorem newJccOpcode_cases : ∀ opcode : Byte, NewJccOpcode opcode ↔
    opcode = 0x70 ∨ opcode = 0x71 ∨ opcode = 0x72 ∨ opcode = 0x73 ∨
    opcode = 0x74 ∨ opcode = 0x76 ∨ opcode = 0x77 ∨ opcode = 0x78 ∨
    opcode = 0x79 ∨ opcode = 0x7a ∨ opcode = 0x7b ∨ opcode = 0x7c ∨
    opcode = 0x7d ∨ opcode = 0x7e ∨ opcode = 0x7f := by
  intro opcode
  simp only [NewJccOpcode, BitVec.toNat_eq, BitVec.toNat_ne, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

private def NewOpcode (opcode : Byte) : Prop :=
  opcode = 0x31#8 ∨ opcode = 0x03#8 ∨ opcode = 0x74#8 ∨ opcode = 0xeb#8 ∨
    rexWPrefix opcode = true ∨ NewJccOpcode opcode

private def MovOpcode (opcode : Byte) : Prop := opcode = 0x89#8 ∨ opcode = 0x8b#8

private theorem decodeNewAt_opcode {state : State} {instruction : Instruction} {fault : Error}
    (decoded : decodeNewAt state fault = .ok instruction) :
    ∃ opcode, fetchByte state.memory state.rip = .ok opcode ∧
      (NewOpcode opcode ∨ MovOpcode opcode) := by
  cases fetched : fetchByte state.memory state.rip with
  | error error => simp only [decodeNewAt, fetched, error_bind, reduceCtorEq] at decoded
  | ok opcode =>
    refine ⟨opcode, rfl, ?_⟩
    by_cases supported : NewOpcode opcode ∨ MovOpcode opcode
    · exact supported
    · simp only [NewOpcode, MovOpcode, not_or] at supported
      rcases supported with ⟨⟨h31, h03, h74, heb, hrex, hjcc⟩, h89, h8b⟩
      rw [rexWPrefix_eq_true] at hrex
      change ¬(0x70 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x7f ∧ opcode ≠ 0x75#8) at hjcc
      simp [decodeNewAt, fetched, h31, h03, h74, heb, hrex, h89, h8b, hjcc] at decoded

private theorem old_rejects_new_opcode {state : State} {opcode : Byte}
    (fetched : fetchByte state.memory state.rip = .ok opcode) (newOpcode : NewOpcode opcode) :
    X86.decodeAt state = .error (.unsupportedOpcode opcode) := by
  rcases newOpcode with rfl | rfl | rfl | rfl | rex | jcc
  · simp [X86.decodeAt, fetched]
  · simp [X86.decodeAt, fetched]
  · simp [X86.decodeAt, fetched]
  · simp [X86.decodeAt, fetched]
  · rcases (rexWPrefix_eq_true _).mp rex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [X86.decodeAt, fetched]
  · rcases (newJccOpcode_cases opcode).mp jcc with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [X86.decodeAt, fetched]

private theorem decodeNewAt_fallback_irrelevant {state : State} {opcode : Byte}
    (fetched : fetchByte state.memory state.rip = .ok opcode)
    (newOpcode : NewOpcode opcode ∨ MovOpcode opcode)
    (left right : Error) : decodeNewAt state left = decodeNewAt state right := by
  rcases newOpcode with old | mov
  · rcases old with rfl | rfl | rfl | rfl | rex | jcc
    · simp [decodeNewAt, fetched]
    · simp [decodeNewAt, fetched]
    · simp [decodeNewAt, fetched]
    · simp [decodeNewAt, fetched]
    · rcases (rexWPrefix_eq_true _).mp rex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [decodeNewAt, fetched]
    · rcases (newJccOpcode_cases opcode).mp jcc with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [decodeNewAt, fetched]
  · rcases mov with rfl | rfl <;> simp [decodeNewAt, fetched]

/-- The overlapping MOV opcodes need their actual ModRM byte, rather than an
opcode-only legacy-rejection argument. Successful new decoding supplies it. -/
private theorem decodeNewAt_mov_modrm {state : State} {opcode : Byte}
    {instruction : Instruction} {fault : Error}
    (decoded : decodeNewAt state fault = .ok instruction)
    (fetched : fetchByte state.memory state.rip = .ok opcode) (mov : MovOpcode opcode) :
    ∃ modrm, fetchByte state.memory (state.rip + 1#64) = .ok modrm := by
  rcases mov with rfl | rfl
  all_goals
    cases fetchedModrm : fetchByte state.memory (state.rip + 1#64) with
    | error error => simp [decodeNewAt, fetched, fetchedModrm] at decoded
    | ok modrm => exact ⟨modrm, rfl⟩

private theorem legacy_mov_decode_congr {source destination : State} {opcode modrm : Byte}
    (mov : MovOpcode opcode)
    (sourceOpcode : fetchByte source.memory source.rip = .ok opcode)
    (destinationOpcode : fetchByte destination.memory destination.rip = .ok opcode)
    (sourceModrm : fetchByte source.memory (source.rip + 1#64) = .ok modrm)
    (destinationModrm : fetchByte destination.memory (destination.rip + 1#64) = .ok modrm) :
    X86.decodeAt destination = X86.decodeAt source := by
  rcases mov with rfl | rfl <;>
    simp [X86.decodeAt, sourceOpcode, destinationOpcode, sourceModrm, destinationModrm]

/-- Transfer ANY successful decode to any memory/base preserving its successful
fetches at offsets below five. The legacy-first selection remains unchanged,
including legacy LEA successes. No equality, readability, or permission premise
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
    have oldDestination : ∃ destinationFault, X86.decodeAt destination = .error destinationFault := by
      rcases newOpcode with disjoint | mov
      · exact ⟨_, old_rejects_new_opcode destinationFetch disjoint⟩
      · obtain ⟨modrm, fetchedModrm⟩ := decodeNewAt_mov_modrm newly fetched mov
        have destinationModrm := transport 1 (by decide) modrm fetchedModrm
        exact ⟨fault, (legacy_mov_decode_congr mov fetched destinationFetch
          fetchedModrm destinationModrm).trans old⟩
    obtain ⟨destinationFault, oldDestination⟩ := oldDestination
    have moved := decodeNewAt_transport fault transport newly
    rw [decodeAt, oldDestination]
    change decodeNewAt destination destinationFault = .ok instruction
    rw [←decodeNewAt_fallback_irrelevant destinationFetch newOpcode fault destinationFault]
    exact moved

end EDSL.X86.Sequential
