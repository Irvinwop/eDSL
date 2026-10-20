/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Contract

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.PureCall
open X86

/-- Shared scratch-register frame for read-only scalar loop invariants. The
scratch set records permitted clobbers; memory and nonarithmetic flags remain
complete state equalities. This does not assert any future execution. -/
structure ScratchFrame (scratch : List Register) (initial current : State) : Prop where
  memory : current.memory = initial.memory
  flags : current.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask
  registers : ∀ register, register ∉ scratch → current.registers register = initial.registers register

theorem scratchFrame_iff (scratch : List Register) (initial current : State) :
    ScratchFrame scratch initial current ↔
      current.memory = initial.memory ∧
      current.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask ∧
      ∀ register, register ∉ scratch → current.registers register = initial.registers register := by
  constructor
  · intro frame
    exact ⟨frame.memory, frame.flags, frame.registers⟩
  · rintro ⟨memory, flags, registers⟩
    exact ⟨memory, flags, registers⟩

theorem ScratchFrame.refl (scratch : List Register) (initial : State) :
    ScratchFrame scratch initial initial := ⟨rfl, rfl, fun _ _ => rfl⟩

/-- Widen permitted clobbers only with an explicit subset proof. In particular,
callers must request the terminal RSP clobber; it is never implicit in a frame. -/
theorem ScratchFrame.weaken {scratch wider : List Register} {initial current : State}
    (frame : ScratchFrame scratch initial current) (subset : scratch ⊆ wider) :
    ScratchFrame wider initial current := by
  refine ⟨frame.memory, frame.flags, ?_⟩
  intro register outside
  exact frame.registers register (fun member => outside (subset member))

/-- A register write needs evidence that this very destination is scratch.
The proof is shared for all GPRs, without enumerating the register file. -/
theorem ScratchFrame.writeRegister {scratch : List Register} {initial current : State}
    (frame : ScratchFrame scratch initial current) (destination : Register) (value : Word)
    (member : destination ∈ scratch) :
    ScratchFrame scratch initial (current.writeRegister destination value) := by
  refine ⟨frame.memory, frame.flags, ?_⟩
  intro register outside
  have different : register ≠ destination := fun same => outside (same.symm ▸ member)
  simpa only [State.writeRegister, ite_eq_right different] using frame.registers register outside

theorem ScratchFrame.withRip {scratch : List Register} {initial current : State}
    (frame : ScratchFrame scratch initial current) (rip : Word) :
    ScratchFrame scratch initial { current with rip } :=
  ⟨frame.memory, frame.flags, frame.registers⟩

/-- Changing flags requires equality of the *full* nonarithmetic mask, including
reserved and high bits. No fact about one selected flag suffices. -/
theorem ScratchFrame.withFlags {scratch : List Register} {initial current : State}
    (frame : ScratchFrame scratch initial current) (flags : Word)
    (preserved : flags &&& ~~~arithmeticFlagMask = current.flags &&& ~~~arithmeticFlagMask) :
    ScratchFrame scratch initial { current with flags } :=
  ⟨frame.memory, preserved.trans frame.flags, frame.registers⟩

/-- Reconcile normalized production record updates with a composed frame.
Register functions and the entire memory (including both permission functions)
must agree; only RIP and arithmetic flags may differ. -/
theorem ScratchFrame.of_fields {scratch : List Register} {initial current : State}
    (frame : ScratchFrame scratch initial current) (next : State)
    (registers : next.registers = current.registers) (memory : next.memory = current.memory)
    (flags : next.flags &&& ~~~arithmeticFlagMask = current.flags &&& ~~~arithmeticFlagMask) :
    ScratchFrame scratch initial next := by
  refine ⟨memory.trans frame.memory, flags.trans frame.flags, ?_⟩
  intro register outside
  rw [registers]
  exact frame.registers register outside

theorem ScratchFrame.calleeSaved {scratch : List Register} {initial current : State}
    (frame : ScratchFrame scratch initial current)
    (disjoint : ∀ register ∈ calleeSaved, register ∉ scratch) :
    ∀ register ∈ calleeSaved, current.registers register = initial.registers register := by
  intro register saved
  exact frame.registers register (disjoint register saved)

/-- Package a terminal scratch frame and an independent result into the scalar
return contract. RET may advance RSP, so it is included in the terminal scratch
set; the exact caller RIP and RSP still have to be proved from actual execution.
This lemma supplies no execution or stack-read premise. -/
theorem ScratchFrame.post_return {spec : Spec} {input : Invocation spec}
    {scratch : List Register} {initial final : State}
    (frame : ScratchFrame (.rsp :: scratch) initial final)
    (savedProtected : ∀ register ∈ PureCall.calleeSaved, register ≠ .rsp ∧ register ∉ scratch)
    (correct : spec.result input.value (final.registers .rax))
    (returnAddress : final.rip = input.returnAddress)
    (stackPointer : final.registers .rsp = initial.registers .rsp + 8) :
    Post spec input initial final := by
  refine ⟨correct, frame.memory, returnAddress, stackPointer, ?_, frame.flags⟩
  intro register saved
  exact frame.registers register (by
    simpa only [List.mem_cons, not_or] using savedProtected register saved)

end EDSL.PureCall
