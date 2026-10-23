/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.AddRMW64.Effects
import EDSL.X86.LockedAdd64.Machine

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.AddRMW64

theorem afterRmw_xadd (state : State) (old : LockedAdd64.Instruction)
    (memory : Memory) (event : FetchAddEvent64) :
    afterRmw state (.xadd old) memory event = LockedAdd64.afterAdd state old memory event := rfl

/-- Equality of the entire Except result, including every primitive/data-gate
error. There is no restriction on the legacy REX, source, base aliases or RSP. -/
theorem execute_xadd (state : State) (old : LockedAdd64.Instruction) :
    execute state (.xadd old) = LockedAdd64.execute state old := rfl

/-- Tagged successful decoding equivalence, not global decoder equality. -/
theorem decodeAt_xadd_iff (state : State) (old : LockedAdd64.Instruction) :
    decodeAt state = .ok (.xadd old) ↔ LockedAdd64.decodeAt state = .ok old :=
  (decodeAt_iff_code (.xadd old) state).trans (LockedAdd64.decodeAt_iff_code old state).symm

/-- For the XADD escape byte, the final selected decoder is precisely the
unchanged eager five-byte decoder, including its fetch/error ordering. -/
theorem decodeAt_xadd_branch (state : State)
    (probe : fetchByte state.memory (state.rip + 2) = .ok 0x0f) :
    decodeAt state = (do return .xadd (← LockedAdd64.decodeAt state)) := by
  change fetchByte state.memory (state.rip + 2#64) = .ok 0x0f#8 at probe
  simp only [decodeAt, BitVec.ofNat_eq_ofNat, probe]
  rfl

/-- Under actual old decoding, steps agree even if executing the operand
fails. Successful old decoding is not a premise of execute_xadd. -/
theorem step_xadd {state : State} {old : LockedAdd64.Instruction}
    (decoded : LockedAdd64.decodeAt state = .ok old) :
    step state = LockedAdd64.step state := by
  rw [step_eq_execute ((decodeAt_xadd_iff state old).mpr decoded),
    LockedAdd64.step_eq_execute decoded]
  exact execute_xadd state old

theorem effect_xadd_iff (initial : State) (old : LockedAdd64.Instruction)
    (event : FetchAddEvent64) (final : State) :
    Effect initial (.xadd old) event final ↔ LockedAdd64.Effect initial old event final := by
  constructor
  · intro effect
    exact ⟨effect.primitive, effect.dataOnly, effect.registers, effect.rip, effect.flags⟩
  · intro effect
    exact ⟨effect.primitive, effect.dataOnly, effect.registers, effect.rip, effect.flags⟩

/-- Recover every legacy effect method without changing its type or contract. -/
theorem Effect.xadd {initial final : State} {old : LockedAdd64.Instruction} {event : FetchAddEvent64}
    (effect : Effect initial (.xadd old) event final) : LockedAdd64.Effect initial old event final :=
  (effect_xadd_iff initial old event final).mp effect

theorem Effect.xadd_flag_bits {initial final : State} {old : LockedAdd64.Instruction}
    {event : FetchAddEvent64} (effect : Effect initial (.xadd old) event final) :
    final.flags.getLsbD 0 = event.event.before.uaddOverflow event.delta ∧
    final.flags.getLsbD 2 = evenParity (event.event.after.setWidth 8) ∧
    final.flags.getLsbD 4 = (event.event.before.setWidth 4).uaddOverflow (event.delta.setWidth 4) ∧
    final.flags.getLsbD 6 = (event.event.after == 0) ∧
    final.flags.getLsbD 7 = event.event.after.msb ∧
    final.flags.getLsbD 11 = event.event.before.saddOverflow event.delta := effect.xadd.flag_bits

theorem Effect.xadd_carry {initial final : State} {old : LockedAdd64.Instruction}
    {event : FetchAddEvent64} (effect : Effect initial (.xadd old) event final) :
    final.flags.getLsbD 0 = true ↔ 2^64 ≤ event.event.before.toNat + event.delta.toNat := effect.xadd.carry

theorem Effect.xadd_overflow {initial final : State} {old : LockedAdd64.Instruction}
    {event : FetchAddEvent64} (effect : Effect initial (.xadd old) event final) :
    final.flags.getLsbD 11 = true ↔
      event.event.before.toInt + event.delta.toInt < -(2^63 : Int) ∨
      2^63 ≤ event.event.before.toInt + event.delta.toInt := effect.xadd.overflow

end EDSL.X86.AddRMW64
