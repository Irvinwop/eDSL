/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Decode

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

variable {α β : Type}

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
theorem legacy_decodeAt_transport_short {source destination : State} {instruction : X86.Instruction}
    (transport : SuccessfulFetchTransportWithin 9 source destination)
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
      | with_reducible exact SuccessRefines.refl _
      | exact t0
      | exact t1
      | exact t2
      | exact t3
      | exact t4
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value
  exact refinement instruction decoded

theorem legacy_decodeAt_transport {source destination : State} {instruction : X86.Instruction}
    (transport : SuccessfulFetchTransport source destination)
    (decoded : X86.decodeAt source = .ok instruction) :
    X86.decodeAt destination = .ok instruction :=
  legacy_decodeAt_transport_short (transport.restrict (by decide : 9 ≤ 15)) decoded

private theorem decodeAddressAt_refines {source destination : State} (modrm : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeAddressAt source modrm) (decodeAddressAt destination modrm) := by
  have t2 := transport 2 (by decide)
  unfold decodeAddressAt
  repeat first
    | with_reducible exact SuccessRefines.refl _
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
    | with_reducible exact SuccessRefines.refl _
    | exact t3
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

private theorem decodeCmpMemImm8At_refines {source destination : State}
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCmpMemImm8At source) (decodeCmpMemImm8At destination) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  unfold decodeCmpMemImm8At
  apply SuccessRefines.bind t1
  intro modrm
  apply SuccessRefines.ite
  · exact SuccessRefines.refl _
  · apply SuccessRefines.bind (decodeAddressAt_refines _ transport)
    intro address
    cases address <;> simp only [Address.suffixBytes] <;>
      apply SuccessRefines.bind (by assumption) <;>
      intro immediate <;> exact SuccessRefines.refl _

private theorem decodeCmpRegMem8At_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCmpRegMem8At source rex prefixed)
      (decodeCmpRegMem8At destination rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeCmpRegMem8At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | with_reducible exact decodeAddressAt_refines _ transport
      | with_reducible exact decodeQWordAddressAt_refines _ _ transport
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

private theorem decodeMovImm32At_refines {source destination : State} (opcode : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeMovImm32At source opcode) (decodeMovImm32At destination opcode) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  unfold decodeMovImm32At
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t1
    | exact t2
    | exact t3
    | exact t4
    | apply SuccessRefines.bind
    | intro value

private theorem decodeCmpMemRegAt_refines {source destination : State} (byteWidth : Bool)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCmpMemRegAt source byteWidth) (decodeCmpMemRegAt destination byteWidth) := by
  have t1 := transport 1 (by decide)
  unfold decodeCmpMemRegAt
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t1
    | exact decodeAddressAt_refines _ transport
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

private theorem decodeMovSignImm32At_refines {source destination : State} (rex : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeMovSignImm32At source rex) (decodeMovSignImm32At destination rex) := by
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  have t5 := transport 5 (by decide)
  have t6 := transport 6 (by decide)
  unfold decodeMovSignImm32At
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t2
    | exact t3
    | exact t4
    | exact t5
    | exact t6
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

private theorem decodeDisp8AddressAt_refines {source destination : State} (rex modrm : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeDisp8AddressAt source rex modrm)
      (decodeDisp8AddressAt destination rex modrm) := by
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  unfold decodeDisp8AddressAt
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t3
    | exact t4
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

private theorem decodeLogicalReg32At_refines {source destination : State} (opcode rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeLogicalReg32At source opcode rex prefixed)
      (decodeLogicalReg32At destination opcode rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeLogicalReg32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

private theorem decodeShiftRightImm32At_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeShiftRightImm32At source rex prefixed)
      (decodeShiftRightImm32At destination rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  cases prefixed <;> unfold decodeShiftRightImm32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | exact t3
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

private theorem decodeCounter32At_refines {source destination : State} (opcode rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCounter32At source opcode rex prefixed)
      (decodeCounter32At destination opcode rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  cases prefixed <;> unfold decodeCounter32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
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
    | with_reducible exact SuccessRefines.refl _
    | exact t1
    | exact t2
    | exact t3
    | exact decodeMovSignImm32At_refines _ transport
    | exact decodeQWordAddressAt_refines _ _ transport
    | exact decodeDisp8AddressAt_refines _ _ transport
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

private theorem decodeCompare32At_refines {source destination : State} (opcode rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCompare32At source opcode rex prefixed)
      (decodeCompare32At destination opcode rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeCompare32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

private theorem decodeCmov32At_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCmov32At source rex prefixed)
      (decodeCmov32At destination rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  cases prefixed <;> unfold decodeCmov32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | exact t3
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

private theorem decodeSetccAt_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeSetccAt source rex prefixed)
      (decodeSetccAt destination rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  cases prefixed <;> unfold decodeSetccAt <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | exact t3
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

private theorem decodeMovImm8At_refines {source destination : State} (opcode rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeMovImm8At source opcode rex prefixed)
      (decodeMovImm8At destination opcode rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeMovImm8At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

private theorem decodeCmpReg8At_refines {source destination : State} (opcode rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCmpReg8At source opcode rex prefixed)
      (decodeCmpReg8At destination opcode rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeCmpReg8At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

private theorem decodeSubReg32At_refines {source destination : State} (opcode rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeSubReg32At source opcode rex prefixed)
      (decodeSubReg32At destination opcode rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeSubReg32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

private theorem decodeNegReg32At_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeNegReg32At source rex prefixed)
      (decodeNegReg32At destination rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeNegReg32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

private theorem decodeMovzxAddressAt_refines {source destination : State} (rex modrm : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeMovzxAddressAt source rex modrm prefixed)
      (decodeMovzxAddressAt destination rex modrm prefixed) := by
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  cases prefixed <;> unfold decodeMovzxAddressAt <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t3
      | exact t4
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

private theorem decodeMovzx8At_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeMovzx8At source rex prefixed)
      (decodeMovzx8At destination rex prefixed) := by
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  cases prefixed <;> unfold decodeMovzx8At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t2
      | exact t3
      | with_reducible exact decodeMovzxAddressAt_refines _ _ _ transport
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

private theorem decode0FREX32At_refines {source destination : State} (rex : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decode0FREX32At source rex) (decode0FREX32At destination rex) := by
  have t2 := transport 2 (by decide)
  unfold decode0FREX32At
  apply SuccessRefines.bind t2
  intro second
  apply SuccessRefines.ite
  · exact decodeMovzx8At_refines rex true transport
  · apply SuccessRefines.ite
    · exact decodeSetccAt_refines rex true transport
    · exact decodeCmov32At_refines rex true transport

private theorem decodeREX32At_refines {source destination : State} (rex : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeREX32At source rex) (decodeREX32At destination rex) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  unfold decodeREX32At
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t1
    | exact t2
    | with_reducible exact decodeMovImm8At_refines _ _ _ transport
    | with_reducible exact decode0FREX32At_refines _ transport
    | with_reducible exact decodeCmpRegMem8At_refines _ _ transport
    | with_reducible exact decodeCmpReg8At_refines _ _ _ transport
    | with_reducible exact decodeSubReg32At_refines _ _ _ transport
    | with_reducible exact decodeLogicalReg32At_refines _ _ _ transport
    | with_reducible exact decodeShiftRightImm32At_refines _ _ transport
    | with_reducible exact decodeNegReg32At_refines _ _ transport
    | with_reducible exact decodeCounter32At_refines _ _ _ transport
    | with_reducible exact decodeCompare32At_refines _ _ _ transport
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

private theorem fetchExactAt_refines {source destination : State} (bytes : List Byte)
    (transport : SuccessfulFetchTransport source destination) (offset : Nat)
    (bound : offset + bytes.length ≤ 15) :
    SuccessRefines (fetchExactAt source offset bytes) (fetchExactAt destination offset bytes) := by
  induction bytes generalizing offset with
  | nil => exact SuccessRefines.refl _
  | cons expected rest ih =>
    unfold fetchExactAt
    apply SuccessRefines.bind (transport offset (by simp only [List.length_cons] at bound; omega))
    intro actual
    apply SuccessRefines.ite
    · exact ih (offset + 1) (by simp only [List.length_cons] at bound; omega)
    · exact SuccessRefines.refl _

private theorem decodePaddingAt_refines {source destination : State} (opcode : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodePaddingAt source opcode) (decodePaddingAt destination opcode) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  have exactSix := fetchExactAt_refines [0, 0] transport 4 (by decide)
  have exactNine := fetchExactAt_refines [0, 0, 0, 0, 0] transport 4 (by decide)
  have exactFifteen := fetchExactAt_refines
    [0x66, 0x66, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0] transport 2 (by decide)
  unfold decodePaddingAt
  apply SuccessRefines.ite
  · exact SuccessRefines.refl _
  · apply SuccessRefines.bind t1
    intro second
    apply SuccessRefines.ite
    · apply SuccessRefines.ite
      · exact SuccessRefines.refl _
      · apply SuccessRefines.ite
        · apply SuccessRefines.bind exactFifteen
          intro completed
          exact SuccessRefines.refl _
        · repeat first
            | exact t2
            | exact t3
            | exact exactSix
            | exact exactNine
            | with_reducible exact SuccessRefines.refl _
            | apply SuccessRefines.ite
            | apply SuccessRefines.bind
            | intro value
    · repeat first
        | exact t2
        | exact t3
        | exact t4
        | with_reducible exact SuccessRefines.refl _
        | apply SuccessRefines.ite
        | apply SuccessRefines.bind
        | intro value

private theorem decode0F32At_refines {source destination : State}
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decode0F32At source) (decode0F32At destination) := by
  have t1 := transport 1 (by decide)
  unfold decode0F32At
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t1
    | with_reducible exact decodeCmov32At_refines _ _ transport
    | with_reducible exact decodeSetccAt_refines _ _ transport
    | with_reducible exact decodeMovzx8At_refines _ _ transport
    | with_reducible exact decodePaddingAt_refines _ transport
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

private theorem decodeTailAt_refines {source destination : State} (opcode : Byte) (fault : Error)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeTailAt source opcode fault) (decodeTailAt destination opcode fault) := by
  have t1 := transport 1 (by decide)
  unfold decodeTailAt
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t1
    | with_reducible exact decodeAddressAt_refines _ transport
    | with_reducible exact (show SuccessRefines (decodeJccAt source _) (decodeJccAt destination _) from by
        unfold decodeJccAt
        apply SuccessRefines.bind t1
        intro displacement
        exact SuccessRefines.refl _)
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

/-- New decoding, including LEA/ADD's SIB fetch, both register ADD directions,
CMOV's condition opcode and register operands, and short Jcc displacements,
preserves success under the same fetch transport. A fixed fallback error
cannot itself yield a successful instruction. -/
theorem decodeNewAt_transport {source destination : State} {instruction : Instruction} (fault : Error)
    (transport : SuccessfulFetchTransport source destination)
    (decoded : decodeNewAt source fault = .ok instruction) :
    decodeNewAt destination fault = .ok instruction := by
  have t0 := transport 0 (by decide)
  have t1 := transport 1 (by decide)
  simp only [BitVec.add_zero] at t0
  have refinement : SuccessRefines (decodeNewAt source fault) (decodeNewAt destination fault) := by
    unfold decodeNewAt
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t0
      | exact t1
      | with_reducible exact (show SuccessRefines (decodeJccAt source _) (decodeJccAt destination _) from by
          unfold decodeJccAt
          apply SuccessRefines.bind t1
          intro displacement
          exact SuccessRefines.refl _)
      | with_reducible exact decodeTailAt_refines _ _ transport
      | with_reducible exact decodeAddressAt_refines _ transport
      | with_reducible exact decodeCmpMemImm8At_refines transport
      | with_reducible exact decodeCmpMemRegAt_refines _ transport
      | with_reducible exact decodeCmpRegMem8At_refines _ _ transport
      | with_reducible exact decodeREXWAt_refines _ transport
      | with_reducible exact decodeREX32At_refines _ transport
      | with_reducible exact decodeCompare32At_refines _ _ _ transport
      | with_reducible exact decodeMovImm8At_refines _ _ _ transport
      | with_reducible exact decodeMovImm32At_refines _ transport
      | with_reducible exact decodeCmpReg8At_refines _ _ _ transport
      | with_reducible exact decodeSubReg32At_refines _ _ _ transport
      | with_reducible exact decodeLogicalReg32At_refines _ _ _ transport
      | with_reducible exact decodeShiftRightImm32At_refines _ _ transport
      | with_reducible exact decodeNegReg32At_refines _ _ transport
      | with_reducible exact decodeCounter32At_refines _ _ _ transport
      | with_reducible exact decode0F32At_refines transport
      | with_reducible exact decodePaddingAt_refines _ transport
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

private def BatchOpcode (opcode : Byte) : Prop :=
  (0xb0 ≤ opcode.toNat ∧ opcode.toNat ≤ 0xb7) ∨
  opcode = 0x33#8 ∨ opcode = 0x80#8 ∨ opcode = 0x38#8 ∨ opcode = 0x3a#8 ∨ opcode = 0x29#8 ∨ opcode = 0x2b#8 ∨
    opcode = 0x09#8 ∨ opcode = 0x0b#8 ∨ opcode = 0xc1#8 ∨
    opcode = 0xf7#8 ∨ opcode = 0xff#8 ∨
    (opcode = 0x39#8 ∨ opcode = 0x3b#8 ∨ opcode = 0x85#8) ∨
    rex32Prefix opcode = true ∨
    (opcode = 0x90#8 ∨ opcode = 0x66#8 ∨ opcode = 0xf3#8)

private theorem batchOpcode_cases (opcode : Byte) : BatchOpcode opcode ↔
    opcode = 0xb0 ∨ opcode = 0xb1 ∨ opcode = 0xb2 ∨ opcode = 0xb3 ∨
    opcode = 0xb4 ∨ opcode = 0xb5 ∨ opcode = 0xb6 ∨ opcode = 0xb7 ∨
    opcode = 0x33 ∨ opcode = 0x80 ∨ opcode = 0x38 ∨ opcode = 0x3a ∨ opcode = 0x29 ∨ opcode = 0x2b ∨
    opcode = 0x09 ∨ opcode = 0x0b ∨ opcode = 0xc1 ∨
    opcode = 0xf7 ∨ opcode = 0xff ∨
    opcode = 0x39 ∨ opcode = 0x3b ∨ opcode = 0x85 ∨
    opcode = 0x40 ∨ opcode = 0x41 ∨ opcode = 0x42 ∨ opcode = 0x43 ∨
    opcode = 0x44 ∨ opcode = 0x45 ∨ opcode = 0x46 ∨ opcode = 0x47 ∨
    opcode = 0x90 ∨ opcode = 0x66 ∨ opcode = 0xf3 := by
  have byteCases : (0xb0 ≤ opcode.toNat ∧ opcode.toNat ≤ 0xb7) ↔
      opcode = 0xb0 ∨ opcode = 0xb1 ∨ opcode = 0xb2 ∨ opcode = 0xb3 ∨
      opcode = 0xb4 ∨ opcode = 0xb5 ∨ opcode = 0xb6 ∨ opcode = 0xb7 := by
    simp only [BitVec.toNat_eq, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod]
    omega
  simp only [BatchOpcode, byteCases, rex32Prefix_eq_true, or_assoc, BitVec.ofNat_eq_ofNat]

private def MissingMovImm32Opcode (opcode : Byte) : Prop :=
  opcode = 0xb9#8 ∨ opcode = 0xbb#8 ∨ opcode = 0xbc#8 ∨ opcode = 0xbd#8

private def NewOpcode (opcode : Byte) : Prop :=
  MissingMovImm32Opcode opcode ∨ opcode = 0x31#8 ∨ opcode = 0x03#8 ∨ opcode = 0x74#8 ∨ opcode = 0xeb#8 ∨
    rexWPrefix opcode = true ∨ NewJccOpcode opcode ∨ BatchOpcode opcode

private def SharedOpcode (opcode : Byte) : Prop := opcode = 0x89#8 ∨ opcode = 0x8b#8 ∨ opcode = 0x0f#8 ∨ opcode = 0x83#8

private theorem decodeNewAt_opcode {state : State} {instruction : Instruction} {fault : Error}
    (decoded : decodeNewAt state fault = .ok instruction) :
    ∃ opcode, fetchByte state.memory state.rip = .ok opcode ∧
      (NewOpcode opcode ∨ SharedOpcode opcode) := by
  cases fetched : fetchByte state.memory state.rip with
  | error error => simp only [decodeNewAt, fetched, error_bind, reduceCtorEq] at decoded
  | ok opcode =>
    refine ⟨opcode, rfl, ?_⟩
    by_cases supported : NewOpcode opcode ∨ SharedOpcode opcode
    · exact supported
    · simp only [NewOpcode, SharedOpcode, not_or] at supported
      rcases supported with ⟨⟨hMissing, h31, h03, h74, heb, hrex, hjcc, hbatch⟩, h89, h8b, h0f, h83⟩
      simp only [MissingMovImm32Opcode, not_or] at hMissing
      rcases hMissing with ⟨hb9,hbb,hbc,hbd⟩
      rw [rexWPrefix_eq_true] at hrex
      simp only [BatchOpcode, not_or] at hbatch
      rcases hbatch with ⟨himm8, h33, h80, h38, h3a, h29, h2b, h09, h0b, hc1, hf7, hff, ⟨h39, h3b, h85⟩, h32, h90, h66, hf3⟩
      rw [rex32Prefix_eq_true] at h32
      change ¬(0x70 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x7f ∧ opcode ≠ 0x75#8) at hjcc
      simp [decodeNewAt, decodeTailAt, fetched, himm8, h33, h80, h38, h3a, h29, h2b, h09, h0b, hc1, hf7, hff, h39, h3b, h85, h32, h90, h66, hf3, h0f, h83,
        hb9, hbb, hbc, hbd, h31, h03, h74, heb, hrex, h89, h8b, hjcc] at decoded

private theorem old_rejects_new_opcode {state : State} {opcode : Byte}
    (fetched : fetchByte state.memory state.rip = .ok opcode) (newOpcode : NewOpcode opcode) :
    X86.decodeAt state = .error (.unsupportedOpcode opcode) := by
  rcases newOpcode with missing | rfl | rfl | rfl | rfl | rex | jcc | batch
  · rcases missing with rfl | rfl | rfl | rfl <;> simp [X86.decodeAt, fetched]
  · simp [X86.decodeAt, fetched]
  · simp [X86.decodeAt, fetched]
  · simp [X86.decodeAt, fetched]
  · simp [X86.decodeAt, fetched]
  · rcases (rexWPrefix_eq_true _).mp rex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [X86.decodeAt, fetched]
  · rcases (newJccOpcode_cases opcode).mp jcc with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [X86.decodeAt, fetched]
  · rcases (batchOpcode_cases opcode).mp batch with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [X86.decodeAt, fetched]

private theorem decodeNewAt_fallback_irrelevant {state : State} {opcode : Byte}
    (fetched : fetchByte state.memory state.rip = .ok opcode)
    (newOpcode : NewOpcode opcode ∨ SharedOpcode opcode)
    (left right : Error) : decodeNewAt state left = decodeNewAt state right := by
  simp only [decodeNewAt, fetched, ok_bind]
  rcases newOpcode with old | mov
  · rcases old with missing | rfl | rfl | rfl | rfl | rex | jcc | batch
    · rcases missing with rfl | rfl | rfl | rfl <;> rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rcases (rexWPrefix_eq_true _).mp rex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rcases (newJccOpcode_cases opcode).mp jcc with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rcases (batchOpcode_cases opcode).mp batch with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rcases mov with rfl | rfl | rfl | rfl <;> rfl

/-- MOV overlaps the legacy ModRM cases, and 0F overlaps SYSCALL. Their
second byte, supplied by successful new decoding, selects the legacy result. -/
private theorem decodeNewAt_shared_second {state : State} {opcode : Byte}
    {instruction : Instruction} {fault : Error}
    (decoded : decodeNewAt state fault = .ok instruction)
    (fetched : fetchByte state.memory state.rip = .ok opcode) (mov : SharedOpcode opcode) :
    ∃ modrm, fetchByte state.memory (state.rip + 1#64) = .ok modrm ∧
      (opcode = 0x83#8 → modrm ≠ 0xf8#8) := by
  rcases mov with rfl | rfl | rfl | rfl
  all_goals
    cases fetchedModrm : fetchByte state.memory (state.rip + 1#64) with
    | error error => simp [decodeNewAt, decodeTailAt, decode0F32At, decodeCounter32At, fetched, fetchedModrm] at decoded
    | ok modrm =>
      refine ⟨modrm, rfl, ?_⟩
      intro same
      first
      | solve | cases same
      | intro bad
        subst modrm
        simp [decodeNewAt, decodeCounter32At, fetched, fetchedModrm] at decoded

private theorem legacy_shared_decode_congr {source destination : State} {opcode modrm : Byte}
    (mov : SharedOpcode opcode)
    (sourceOpcode : fetchByte source.memory source.rip = .ok opcode)
    (destinationOpcode : fetchByte destination.memory destination.rip = .ok opcode)
    (sourceModrm : fetchByte source.memory (source.rip + 1#64) = .ok modrm)
    (destinationModrm : fetchByte destination.memory (destination.rip + 1#64) = .ok modrm)
    (notCmp : opcode = 0x83#8 → modrm ≠ 0xf8#8) :
    X86.decodeAt destination = X86.decodeAt source := by
  rcases mov with rfl | rfl | rfl | rfl
  · simp [X86.decodeAt, sourceOpcode, destinationOpcode, sourceModrm, destinationModrm]
  · simp [X86.decodeAt, sourceOpcode, destinationOpcode, sourceModrm, destinationModrm]
  · simp [X86.decodeAt, sourceOpcode, destinationOpcode, sourceModrm, destinationModrm]
  · simp [X86.decodeAt, sourceOpcode, destinationOpcode, sourceModrm, destinationModrm, notCmp rfl]

/-- Transfer ANY successful decode to any memory/base preserving its successful
fetches at offsets below fifteen. The legacy-first selection remains unchanged,
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
      · obtain ⟨modrm, fetchedModrm, notCmp⟩ := decodeNewAt_shared_second newly fetched mov
        have destinationModrm := transport 1 (by decide) modrm fetchedModrm
        exact ⟨fault, (legacy_shared_decode_congr mov fetched destinationFetch
          fetchedModrm destinationModrm notCmp).trans old⟩
    obtain ⟨destinationFault, oldDestination⟩ := oldDestination
    have moved := decodeNewAt_transport fault transport newly
    rw [decodeAt, oldDestination]
    change decodeNewAt destination destinationFault = .ok instruction
    rw [←decodeNewAt_fallback_irrelevant destinationFetch newOpcode fault destinationFault]
    exact moved

end EDSL.X86.Sequential
