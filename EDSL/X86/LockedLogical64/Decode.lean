/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedLogical64.Model

namespace EDSL.X86.LockedLogical64

/-- Exact LOCK OR qword [RDI],RSI or near RET only. Every admitted byte is
actually fetched with execute permission. No prefix normalization, legacy
fallback, register form, immediate or smaller memory width is supported. -/
def decodeAt (state : State) : Except Error Instruction := do
  let opcode ← fetchByte state.memory state.rip
  if opcode = 0xc3 then return .ret
  else if opcode = 0xf0 then
    if state.rip.toNat + 3 ≥ 2^64 then throw (.inaccessibleInstruction state.rip)
    let rex ← fetchByte state.memory (state.rip + 1)
    if rex ≠ 0x48 then throw .unsupportedEncoding
    let operation ← fetchByte state.memory (state.rip + 2)
    if operation ≠ 0x09 then throw .unsupportedEncoding
    let modrm ← fetchByte state.memory (state.rip + 3)
    if modrm ≠ 0x37 then throw .unsupportedEncoding
    return .orRdiRsi
  else throw .unsupportedEncoding

theorem decodeAt_of_code {state : State} (instruction : Instruction)
    (code : CodeAt state.memory state.rip instruction.bytes) :
    decodeAt state = .ok instruction := by
  cases instruction with
  | ret =>
    have b0 := code.2 0 0xc3 (by rfl)
    simp only [BitVec.add_zero] at b0
    simp [decodeAt, b0]
  | orRdiRsi =>
    have b0 := code.2 0 0xf0 (by rfl)
    have b1 := code.2 1 0x48 (by rfl)
    have b2 := code.2 2 0x09 (by rfl)
    have b3 := code.2 3 0x37 (by rfl)
    simp only [BitVec.add_zero] at b0
    have bound : ¬ state.rip.toNat + 3 ≥ 2^64 := by
      have := code.1
      change state.rip.toNat + 4 ≤ 2^64 at this
      omega
    simp [decodeAt, b0, bound, b1, b2, b3]

/-- Successful decoding certifies precisely the admitted instruction bytes. -/
theorem decodeAt_code {state : State} {instruction : Instruction}
    (decoded : decodeAt state = .ok instruction) :
    CodeAt state.memory state.rip instruction.bytes := by
  cases b0 : fetchByte state.memory state.rip with
  | error fault => simp_all [decodeAt, BitVec.ofNat_eq_ofNat]
  | ok opcode =>
    by_cases ret : opcode = 0xc3
    · subst opcode
      simp_all [decodeAt, BitVec.ofNat_eq_ofNat]
      subst instruction
      refine ⟨?_, ?_⟩
      · have := state.rip.isLt
        change state.rip.toNat + 1 ≤ 2^64
        omega
      · intro offset byte atOffset
        cases offset with
        | zero =>
          simp [Instruction.bytes] at atOffset
          subst byte
          simpa only [BitVec.add_zero] using b0
        | succ offset => simp [Instruction.bytes] at atOffset
    · by_cases locked : opcode = 0xf0
      · subst opcode
        by_cases wrap : state.rip.toNat + 3 ≥ 2^64
        · simp_all [decodeAt, BitVec.ofNat_eq_ofNat]
        · cases b1 : fetchByte state.memory (state.rip + 1) with
          | error fault => simp_all [decodeAt, BitVec.ofNat_eq_ofNat]
          | ok rex =>
            by_cases rexValid : rex = 0x48
            · subst rex
              cases b2 : fetchByte state.memory (state.rip + 2) with
              | error fault => simp_all [decodeAt, BitVec.ofNat_eq_ofNat]
              | ok operation =>
                by_cases opValid : operation = 0x09
                · subst operation
                  cases b3 : fetchByte state.memory (state.rip + 3) with
                  | error fault => simp_all [decodeAt, BitVec.ofNat_eq_ofNat]
                  | ok modrm =>
                    by_cases modValid : modrm = 0x37
                    · subst modrm
                      simp_all [decodeAt, BitVec.ofNat_eq_ofNat]
                      subst instruction
                      refine ⟨by change state.rip.toNat + 4 ≤ 2^64; omega, ?_⟩
                      intro offset byte atOffset
                      match offset with
                      | 0 | 1 | 2 | 3 =>
                        simp [Instruction.bytes] at atOffset
                        subst byte
                        simpa only [BitVec.add_zero] using (by assumption)
                      | offset + 4 => simp [Instruction.bytes] at atOffset
                    · simp_all [decodeAt, BitVec.ofNat_eq_ofNat]
                · simp_all [decodeAt, BitVec.ofNat_eq_ofNat]
            · simp_all [decodeAt, BitVec.ofNat_eq_ofNat]
      · simp_all [decodeAt, BitVec.ofNat_eq_ofNat]

/-- Only successful fetches are transported, so a final one-byte RET needs
no padding or fetch of an inaccessible following byte. -/
def SuccessfulFetchTransport (source destination : State) : Prop :=
  ∀ offset, offset < 4 → ∀ byte,
    fetchByte source.memory (source.rip + BitVec.ofNat 64 offset) = .ok byte →
    fetchByte destination.memory (destination.rip + BitVec.ofNat 64 offset) = .ok byte

theorem decodeAt_transport {source destination : State} {instruction : Instruction}
    (sameRip : source.rip = destination.rip)
    (transport : SuccessfulFetchTransport source destination)
    (decoded : decodeAt source = .ok instruction) :
    decodeAt destination = .ok instruction := by
  have code := decodeAt_code decoded
  apply decodeAt_of_code instruction
  refine ⟨by simpa only [sameRip] using code.1, ?_⟩
  intro offset byte atOffset
  obtain ⟨bound, _⟩ := List.getElem_of_getElem? atOffset
  have lengthBound : instruction.bytes.length ≤ 4 := by cases instruction <;> decide
  exact transport offset (by omega) byte (code.2 offset byte atOffset)

/-- Any abstract RMW preserves every disjoint executable instruction window. -/
theorem decodeAt_preserved_by_rmw {source : State} {memory : Memory}
    {event : AtomicEvent64} {instruction : Instruction}
    (transition : RMWTransition64 source.memory event memory)
    (decoded : decodeAt source = .ok instruction)
    (disjoint : QWordDisjoint event.address source.rip instruction.length) :
    decodeAt { source with memory := memory } = .ok instruction := by
  apply decodeAt_of_code instruction
  exact transition.preserves_code _ _ (decodeAt_code decoded) disjoint

end EDSL.X86.LockedLogical64
