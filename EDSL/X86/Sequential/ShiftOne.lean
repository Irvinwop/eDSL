/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine
import EDSL.X86.CallReturn.Machine

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.Sequential

/-!
Full64 register SHR with the implicit count one, under `targetProfile`.
Exactly one REX.W and D1 /5 with mod=3 are supported. B extends r/m;
R is ignored for the group selector and X is unused without a SIB. Other
counts, widths, memory forms and extra prefixes are unsupported.

Reference: Intel SDM Vol.2, SAL/SAR/SHL/SHR and §2.2.1 REX prefixes:
https://cdrdv2-public.intel.com/789581/325383-sdm-vol-2abcd.pdf .
These are conditional local-machine semantics, without physical CPU/OS,
debug/asynchronous or concurrent refinement. Preserving abstract RF/VM does
not assert their observation through PUSHFQ. The target assumes 64-bit mode
and CET/IBT/shadow stacks disabled. RSP is an ordinary GPR here; it is never
dereferenced. No operand canonicality, DATA mapping or stack premise is needed.
-/

/-- Three successful executable fetches suffice. No access beyond the ModRM
byte, operand read, input-value or undefined-flag premise is required. -/
theorem decodeAt_shrOne64 {state : State} {rex modrm : Byte}
    (rexW : rexWPrefix rex = true)
    (f0 : fetchByte state.memory state.rip = .ok rex)
    (f1 : fetchByte state.memory (state.rip + 1) = .ok 0xd1)
    (f2 : fetchByte state.memory (state.rip + 2) = .ok modrm)
    (registerMode : modrm.toNat / 64 = 3) (group : modrm.toNat / 8 % 8 = 5) :
    decodeAt state = .ok (.shrOne64 (rexModRMRM rex modrm)) := by
  have decoded : decodeREXWAt state rex = .ok (.shrOne64 (rexModRMRM rex modrm)) := by
    unfold decodeREXWAt
    rw [f1, ok_bind]
    simp only [↓reduceIte]
    rw [f2, ok_bind]
    simp [registerMode, group]
  rcases (rexWPrefix_eq_true _).mp rexW with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa [decodeAt, X86.decodeAt, decodeNewAt, f0] using decoded

theorem step_shrOne64 {state : State} {destination : Register}
    (decoded : decodeAt state = .ok (.shrOne64 destination)) (af : Bool) :
    step af state = .ok ⟨.next {
      state.writeRegister destination (state.registers destination >>> 1) with
      rip := state.rip + 3,
      flags := shrOneFlags64 state.flags (state.registers destination) af }, []⟩ := by
  rw [step_eq_execute af decoded, execute_shrOne64]

theorem shrOneFlags64_carry (old value : Word) (af : Bool) :
    (shrOneFlags64 old value af).getLsbD 0 = true ↔ value.toNat % 2 = 1 := by
  rw [(shrOneFlags64_bits ..).1]
  simp [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]

theorem shrOneFlags64_overflow (old value : Word) (af : Bool) :
    (shrOneFlags64 old value af).getLsbD 11 = true ↔ 2^63 ≤ value.toNat := by
  rw [(shrOneFlags64_bits ..).2.2.2.2.2, BitVec.msb_eq_decide, decide_eq_true_eq]

theorem shrOneFlags64_sign (old value : Word) (af : Bool) :
    (shrOneFlags64 old value af).getLsbD 7 = false := by
  rw [(shrOneFlags64_bits ..).2.2.2.2.1]
  simp

theorem shrOneFlags64_zero (old value : Word) (af : Bool) :
    (shrOneFlags64 old value af).getLsbD 6 = true ↔ value.toNat < 2 := by
  rw [(shrOneFlags64_bits ..).2.2.2.1, beq_iff_eq, BitVec.toNat_eq]
  change value.toNat >>> 1 = 0 ↔ value.toNat < 2
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- Independent unsigned division by two, complete RAM/permission equality,
all fifteen other GPRs, every nonarithmetic flag, and the precise fallthrough.
The old destination supplies both the result and the flag operands. -/
theorem execute_shrOne64_context (state : State) (destination : Register) (af : Bool) :
    ∃ final, execute state (.shrOne64 destination) af = .ok ⟨.next final, []⟩ ∧
      final.registers destination = state.registers destination >>> 1 ∧
      (final.registers destination).toNat = (state.registers destination).toNat / 2 ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧
      final.flags = shrOneFlags64 state.flags (state.registers destination) af ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      final.rip = state.rip + 3 := by
  refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, shrOneFlags64_preserves .., rfl⟩
  · simp [State.writeRegister]
  · simp [State.writeRegister, Nat.shiftRight_eq_div_pow]
  · intro register different
    simp [State.writeRegister, different]

theorem execute_shrOne64_flags {state final : State} {destination : Register}
    {af : Bool} {reads : List Read}
    (actual : execute state (.shrOne64 destination) af = .ok ⟨.next final, reads⟩) :
    let value := state.registers destination
    (final.flags.getLsbD 0 = true ↔ value.toNat % 2 = 1) ∧
    final.flags.getLsbD 2 = evenParity ((value >>> 1).setWidth 8) ∧
    final.flags.getLsbD 4 = af ∧
    (final.flags.getLsbD 6 = true ↔ value.toNat < 2) ∧
    final.flags.getLsbD 7 = false ∧
    (final.flags.getLsbD 11 = true ↔ 2^63 ≤ value.toNat) := by
  cases actual
  exact ⟨shrOneFlags64_carry .., (shrOneFlags64_bits ..).2.1,
    (shrOneFlags64_bits ..).2.2.1, shrOneFlags64_zero ..,
    shrOneFlags64_sign .., shrOneFlags64_overflow ..⟩

/-- Both choices execute without any operand access or store and produce a
plain next-state observation. This excludes atomic/syscall/return outcomes. -/
theorem shrOne64_effects (state : State) (destination : Register) :
    (Instruction.shrOne64 destination).operandReads state = [] ∧
    (Instruction.shrOne64 destination).storeIntent state = none ∧
    (Instruction.shrOne64 destination).storeIntent64 state = none ∧
    (Instruction.shrOne64 destination).isLocked = false ∧
    (Instruction.shrOne64 destination).choosesAF = true ∧
    ∀ af, ∃ final, execute state (.shrOne64 destination) af = .ok ⟨.next final, []⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => ⟨_, rfl⟩⟩

/-- Universal AF choice frame: states, complete RAM and observations agree
outside AF. The AF bits themselves equal their independent choices. -/
theorem execute_shrOne64_choices (state : State) (destination : Register) (left right : Bool) :
    ∃ first second,
      execute state (.shrOne64 destination) left = .ok ⟨.next first, []⟩ ∧
      execute state (.shrOne64 destination) right = .ok ⟨.next second, []⟩ ∧
      first.registers = second.registers ∧ first.memory = second.memory ∧ first.rip = second.rip ∧
      first.flags &&& ~~~(0x10 : Word) = second.flags &&& ~~~(0x10 : Word) ∧
      first.flags.getLsbD 4 = left ∧ second.flags.getLsbD 4 = right :=
  ⟨_, _, rfl, rfl, rfl, rfl, rfl, shrOneFlags64_choices ..,
    (shrOneFlags64_bits ..).2.2.1, (shrOneFlags64_bits ..).2.2.1⟩

/-- A defined-flags/frame observation has the exact witness given by its AF.
Both model choices remain admitted; no claim about physical AF variability. -/
theorem shrOneFlags64_observed_witness {old value actual : Word}
    (admitted : ShrOneFlags64Admissible old value actual) :
    actual = shrOneFlags64 old value (actual.getLsbD 4) := by
  obtain ⟨af, matching⟩ := (shrOneFlags64_admissible_iff ..).mp admitted
  have bit : actual.getLsbD 4 = af := by
    rw [matching]
    exact (shrOneFlags64_bits ..).2.2.1
  rw [bit]
  exact matching

end EDSL.X86.Sequential

namespace EDSL.X86.CallReturn

/-- The shared CallReturn profile uses the same complete execution observation;
SHR does not acquire a stack read/write by being lifted into that profile. -/
theorem execute_shrOne64 (state : State) (destination : Register) (af : Bool) :
    execute state (liftSequential (.shrOne64 destination)) af =
      .ok ⟨.next { state.writeRegister destination (state.registers destination >>> 1) with
        rip := state.rip + 3,
        flags := Sequential.shrOneFlags64 state.flags (state.registers destination) af }, []⟩ := by
  rw [execute_liftSequential, Sequential.execute_shrOne64]

end EDSL.X86.CallReturn
