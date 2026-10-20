/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ByteOrder

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.Sequential

/-!
Register-only NEG32 and BSWAP64 for the local sequential model. The target
is `targetProfile`, with the existing four-level address/fetch rules and CET
disabled. Instructions operate on all sixteen modeled GPRs, including RSP;
no operand-address canonicality, stack validity or DATA permission is needed.
Actual instruction fetches still require their existing permissions.

Architecture references checked: Intel SDM Vol.2 NEG (F7 /3),
https://cdrdv2-public.intel.com/789581/325383-sdm-vol-2abcd.pdf ; Intel SDM
BSWAP and the correction from REX.R to REX.B in
https://cdrdv2-public.intel.com/819710/252046-sdm-change-document.pdf .
The zero extension rule is Intel SDM Vol.1 §3.4.1.1:
https://cdrdv2-public.intel.com/843820/325462-sdm-vol-1-2abcd-3abcd-4-1.pdf .
The supported encodings are deliberately narrower than the architecture:
NEG has no prefix or one 40/41 byte; BSWAP has exactly 48/49. Other widths,
memory, LOCK and additional prefixes reject. These proofs describe the local
model, not physical CPU/OS refinement, debug state, asynchronous effects or
concurrent execution. Preserved abstract flags do not assert what PUSHFQ can
observe (in particular its RF/VM masking).
-/

theorem step_negReg32 {state : State} {destination : Register} {prefixed : Bool}
    (decoded : decodeAt state = .ok (.negReg32 destination prefixed)) (af : Bool) :
    step af state = .ok ⟨.next { state.writeRegister destination
      ((-((state.registers destination).setWidth 32)).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 (Instruction.negReg32 destination prefixed).length
      flags := cmpFlags32 state.flags 0 ((state.registers destination).setWidth 32) }, []⟩ := by
  rw [step_eq_execute af decoded, execute_negReg32]

theorem step_bswapReg64 {state : State} {destination : Register}
    (decoded : decodeAt state = .ok (.bswapReg64 destination)) (af : Bool) :
    step af state = .ok ⟨.next { state.writeRegister destination
      (WordMath.byteSwap64 (state.registers destination)) with rip := state.rip + 3 }, []⟩ := by
  rw [step_eq_execute af decoded, execute_bswapReg64]

/-- Independent unsigned modular negation and complete state frames. The old
destination is read before the write, with no exception for the stack GPR. -/
theorem execute_negReg32_context (state : State) (destination : Register) (prefixed af : Bool) :
    ∃ final, execute state (.negReg32 destination prefixed) af = .ok ⟨.next final, []⟩ ∧
      (final.registers destination).toNat =
        (4294967296 - (state.registers destination).toNat % 4294967296) % 4294967296 ∧
      (final.registers destination).toNat < 2^32 ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧
      final.flags = cmpFlags32 state.flags 0 ((state.registers destination).setWidth 32) ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      final.rip = state.rip + BitVec.ofNat 64 (if prefixed then 3 else 2) := by
  refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, cmpFlags32_preserves .., rfl⟩
  · simp only [State.writeRegister, ↓reduceIte,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), WordMath.neg32_toNat]
    rfl
  · simp only [State.writeRegister, ↓reduceIte,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
    exact (-((state.registers destination).setWidth 32)).isLt
  · intro register other
    simp [State.writeRegister, other]

/-- Signed negation, including the sole signed-overflow operand. Narrowing the
zero-extended result back to low32 retains exactly its signed modular result. -/
theorem execute_negReg32_signed {state final : State} {destination : Register}
    {prefixed af : Bool} {reads : List Read}
    (success : execute state (.negReg32 destination prefixed) af = .ok ⟨.next final, reads⟩) :
    ((final.registers destination).setWidth 32).toInt =
      if ((state.registers destination).setWidth 32).toInt = -2147483648 then
        ((state.registers destination).setWidth 32).toInt
      else -((state.registers destination).setWidth 32).toInt := by
  cases success
  simpa [State.writeRegister] using WordMath.neg32_toInt ((state.registers destination).setWidth 32)

/-- The six independently specified NEG flags. AF is a defined low-nibble
borrow, CF records a nonzero original operand, and OF is true only for INT_MIN. -/
theorem execute_negReg32_flags {state final : State} {destination : Register}
    {prefixed af : Bool} {reads : List Read}
    (success : execute state (.negReg32 destination prefixed) af = .ok ⟨.next final, reads⟩) :
    let value := (state.registers destination).setWidth 32
    (final.flags.getLsbD 0 = true ↔ value ≠ 0) ∧
    final.flags.getLsbD 2 = evenParity ((-value).setWidth 8) ∧
    (final.flags.getLsbD 4 = true ↔ value.toNat % 16 ≠ 0) ∧
    final.flags.getLsbD 6 = (value == 0) ∧
    final.flags.getLsbD 7 = (-value).msb ∧
    (final.flags.getLsbD 11 = true ↔ value.toInt = -2147483648) := by
  cases success
  exact ⟨cmpFlags32_neg_carry ..,
    by simpa using (cmpFlags32_bits state.flags 0 ((state.registers destination).setWidth 32)).2.1,
    cmpFlags32_neg_auxiliary ..,
    by simpa [Bool.beq_eq_decide_eq, eq_comm] using cmpFlags32_zero state.flags 0 ((state.registers destination).setWidth 32),
    by simpa using (cmpFlags32_bits state.flags 0 ((state.registers destination).setWidth 32)).2.2.2.2.1,
    cmpFlags32_neg_overflow ..⟩

/-- Independent base-256 contract from WordMath, together with the full register,
memory, permission, flag, read and PC frames. Byte reversal is on the old full64
value, not on a low32 approximation or an updated destination. -/
theorem execute_bswapReg64_context (state : State) (destination : Register) (af : Bool) :
    ∃ final, execute state (.bswapReg64 destination) af = .ok ⟨.next final, []⟩ ∧
      WordMath.ByteReverse64 (state.registers destination) (final.registers destination) ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧ final.rip = state.rip + 3 := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · simpa [State.writeRegister] using WordMath.byteSwap64_contract (state.registers destination)
  · intro register other
    simp [State.writeRegister, other]

theorem execute_negReg32_af_independent (state : State) (destination : Register)
    (prefixed left right : Bool) :
    execute state (.negReg32 destination prefixed) left =
      execute state (.negReg32 destination prefixed) right :=
  execute_af_independent state _ left right rfl

theorem execute_bswapReg64_af_independent (state : State) (destination : Register)
    (left right : Bool) :
    execute state (.bswapReg64 destination) left = execute state (.bswapReg64 destination) right :=
  execute_af_independent state _ left right rfl

namespace Literals

private def unaryRegisterCode : Register → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3
  | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

private def unaryCandidate : Instruction → Option (List Byte)
  | .negReg32 destination prefixed =>
    let code := unaryRegisterCode destination
    if !prefixed ∧ 8 ≤ code then none
    else some ((if prefixed then [BitVec.ofNat 8 (0x40 + code / 8)] else []) ++
      [0xf7, BitVec.ofNat 8 (0xd8 + code % 8)])
  | .bswapReg64 destination =>
    let code := unaryRegisterCode destination
    some [BitVec.ofNat 8 (0x48 + code / 8), 0x0f, BitVec.ofNat 8 (0xc8 + code % 8)]
  | _ => none

/-- Emit only exact same-constructor bytes admitted by the production decoder,
with a matching length. High-bank unprefixed NEG and other families return none. -/
def unaryEncoding (instruction : Instruction) : Option (List Byte) :=
  match unaryCandidate instruction with
  | none => none
  | some bytes =>
    match decodeAt (codeState bytes 0) with
    | .ok decoded =>
      if decoded = instruction ∧ bytes.length = instruction.length then some bytes else none
    | .error _ => none

theorem unaryEncoding_decoded {instruction : Instruction} {bytes : List Byte}
    (encoded : unaryEncoding instruction = some bytes) :
    decodeAt (codeState bytes 0) = .ok instruction ∧ bytes.length = instruction.length := by
  unfold unaryEncoding at encoded
  cases candidate : unaryCandidate instruction with
  | none => simp [candidate] at encoded
  | some values =>
    simp only [candidate] at encoded
    cases decoded : decodeAt (codeState values 0) with
    | error fault => simp [decoded] at encoded
    | ok actual =>
      simp only [decoded] at encoded
      split at encoded
      next checked =>
        cases encoded
        exact ⟨by rw [decoded, checked.1], checked.2⟩
      next => cases encoded

/-- Every GPR has a canonical prefixed NEG32 encoding, including RSP. -/
theorem unaryEncoding_negReg32_complete (destination : Register) :
    ∃ bytes, unaryEncoding (.negReg32 destination true) = some bytes := by
  cases destination <;> exact ⟨_, rfl⟩

/-- Without REX, precisely the original eight GPRs have a NEG32 encoding.
The upper bank cannot be silently truncated to its low-bank counterpart. -/
theorem unaryEncoding_negReg32_unprefixed_iff (destination : Register) :
    (∃ bytes, unaryEncoding (.negReg32 destination false) = some bytes) ↔
      destination ∈ ([.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi] : List Register) := by
  cases destination <;> simp [unaryEncoding, unaryCandidate, unaryRegisterCode] <;> exact ⟨_, rfl⟩

/-- Every GPR has a canonical BSWAP64 encoding. In particular R8..R15 use
49 (REX.B), not 4C (REX.R). -/
theorem unaryEncoding_bswapReg64_complete (destination : Register) :
    ∃ bytes, unaryEncoding (.bswapReg64 destination) = some bytes := by
  cases destination <;> exact ⟨_, rfl⟩

end Literals
end EDSL.X86.Sequential
