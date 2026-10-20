/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine
import EDSL.X86.Sequential.ConditionFlags
import EDSL.X86.CallReturn.Machine

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.Sequential

/-!
Reusable low32 logical and signed-imm8 CMP rules, under `targetProfile`.
These rules describe arbitrary machine states and registers, without a
program-specific transition system or a DATA/stack accessibility premise.
The decoder admits XOR32 (31/33), AND32 (83 /4 ib), CMP64 (48/49 83 /7 ib)
and exactly 66 0F 1F 44 00 00 as NOP6. Other constructed logical operations
have semantics but acquire no additional supported byte encodings.

Architecture references are the Intel SDM AND/XOR/CMP/NOP entries and REX
prefix section already used by the sequential backend. Physical CPU/OS,
asynchronous and concurrent refinement remain external obligations.
-/

theorem execute_logicalReg32 (state : State) (operation : LogicalOp)
    (destination source : Register) (prefixed af : Bool) :
    execute state (.logicalReg32 operation destination source prefixed) af =
      .ok ⟨.next { state.writeRegister destination
        ((operation.eval ((state.registers destination).setWidth 32)
          ((state.registers source).setWidth 32)).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (if prefixed then 3 else 2)
        flags := logicalFlags32 state.flags
          (operation.eval ((state.registers destination).setWidth 32)
            ((state.registers source).setWidth 32)) af }, []⟩ := rfl

theorem execute_logicalImm32 (state : State) (operation : LogicalOp)
    (destination : Register) (immediate : Byte) (prefixed af : Bool) :
    execute state (.logicalImm32 operation destination immediate prefixed) af =
      .ok ⟨.next { state.writeRegister destination
        ((operation.eval ((state.registers destination).setWidth 32)
          (immediate.signExtend 32)).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (if prefixed then 4 else 3)
        flags := logicalFlags32 state.flags
          (operation.eval ((state.registers destination).setWidth 32)
            (immediate.signExtend 32)) af }, []⟩ := rfl

theorem execute_cmpImm64 (state : State) (left : Register) (immediate : Byte) (af : Bool) :
    execute state (.cmpImm64 left immediate) af =
      .ok ⟨.next { state with
        rip := state.rip + 4
        flags := cmpFlags64 state.flags (state.registers left) (immediate.signExtend 64) }, []⟩ := rfl

/-- Entire memory/permission equality, all other GPRs, zero extension and
nonarithmetic flags survive. Both operands are the original state, with no
distinct-register premise. The flag contract admits both independent AF choices. -/
theorem execute_logicalReg32_context (state : State) (operation : LogicalOp)
    (destination source : Register) (prefixed af : Bool) :
    let result := operation.eval ((state.registers destination).setWidth 32)
      ((state.registers source).setWidth 32)
    ∃ final, execute state (.logicalReg32 operation destination source prefixed) af =
        .ok ⟨.next final, []⟩ ∧
      final.registers destination = result.setWidth 64 ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧
      final.flags = logicalFlags32 state.flags result af ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      final.rip = state.rip + BitVec.ofNat 64 (if prefixed then 3 else 2) := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, logicalFlags32_preserves .., rfl⟩
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

theorem execute_logicalImm32_context (state : State) (operation : LogicalOp)
    (destination : Register) (immediate : Byte) (prefixed af : Bool) :
    let result := operation.eval ((state.registers destination).setWidth 32)
      (immediate.signExtend 32)
    ∃ final, execute state (.logicalImm32 operation destination immediate prefixed) af =
        .ok ⟨.next final, []⟩ ∧
      final.registers destination = result.setWidth 64 ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧
      final.flags = logicalFlags32 state.flags result af ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      final.rip = state.rip + BitVec.ofNat 64 (if prefixed then 4 else 3) := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, logicalFlags32_preserves .., rfl⟩
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

/-- CMP has no undefined flag choice: both AF arguments produce the same
complete state. JA is the strict unsigned order against the sign-extended byte. -/
theorem execute_cmpImm64_context (state : State) (left : Register) (immediate : Byte) :
    ∃ final, (∀ af, execute state (.cmpImm64 left immediate) af = .ok ⟨.next final, []⟩) ∧
      final.registers = state.registers ∧ final.memory = state.memory ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      Condition.holds .above final.flags =
        decide ((immediate.signExtend 64).toNat < (state.registers left).toNat) ∧
      final.rip = state.rip + 4 :=
  ⟨_, fun _ => rfl, rfl, rfl, cmpFlags64_preserves .., Condition.cmp_above .., rfl⟩

/-- A concrete flag observation determines its AF witness; this does not
assume hardware can be made to realize both undefined AF outcomes. -/
theorem logicalFlags32_observed_witness {old actual : Word} {result : BitVec 32}
    (admitted : LogicalFlagsAdmissible old actual (evenParity (result.setWidth 8))
      (result == 0) result.msb) :
    actual = logicalFlags32 old result (actual.getLsbD 4) := by
  obtain ⟨af, matching⟩ := (logicalFlags32_admissible_iff ..).mp admitted
  have bit : actual.getLsbD 4 = af := by
    rw [matching]
    exact (logicalFlags32_bits ..).2.2.1
  rw [bit]
  exact matching

end EDSL.X86.Sequential

namespace EDSL.X86.CallReturn

/-- Lifting shares the entire observation, including the empty read list;
these logical instructions cannot acquire stack or ordinary DATA effects. -/
theorem execute_logicalReg32 (state : State) (operation : Sequential.LogicalOp)
    (destination source : Register) (prefixed af : Bool) :
    execute state (liftSequential (.logicalReg32 operation destination source prefixed)) af =
      Sequential.execute state (.logicalReg32 operation destination source prefixed) af :=
  execute_liftSequential ..

theorem execute_logicalImm32 (state : State) (operation : Sequential.LogicalOp)
    (destination : Register) (immediate : Byte) (prefixed af : Bool) :
    execute state (liftSequential (.logicalImm32 operation destination immediate prefixed)) af =
      Sequential.execute state (.logicalImm32 operation destination immediate prefixed) af :=
  execute_liftSequential ..

theorem execute_cmpImm64 (state : State) (left : Register) (immediate : Byte) (af : Bool) :
    execute state (liftSequential (.cmpImm64 left immediate)) af =
      Sequential.execute state (.cmpImm64 left immediate) af := execute_liftSequential ..

end EDSL.X86.CallReturn
