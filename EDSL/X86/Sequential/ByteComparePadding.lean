/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.CallReturn.Machine
import EDSL.X86.VCGen.Core
import EDSL.BufferCall.Resources

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.Sequential

/-- Canonical encodings round trip through the production decoder, with no
following byte in the finite code memory. No general NOP-prefix grammar is
inferred from this finite encoding family. -/
theorem NopEncoding.decode_bytes (encoding : NopEncoding) :
    decodeAt (codeState encoding.bytes 0) = .ok (.nop encoding) := by
  cases encoding <;> rfl

/-- Full register/memory frames and all six defined arithmetic flags. The
left byte and address refer to the same prestate, without alias restrictions.
Hardware correspondence assumes `targetProfile` and stable ordinary RAM;
these model theorems do not establish physical/native refinement. -/
structure ByteCompareContext (before after : State) (left : Register)
    (address : Address) (value : Byte) (prefixed : Bool) : Prop where
  loaded : readDataByte before.memory (address.eval before) = .ok value
  registers : after.registers = before.registers
  memory : after.memory = before.memory
  rip : after.rip = before.rip +
    BitVec.ofNat 64 (Instruction.cmpRegMem8 left address prefixed).length
  otherFlags : after.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask
  cf : after.flags.getLsbD 0 = true ↔ (before.registers left).toNat % 256 < value.toNat
  pf : after.flags.getLsbD 2 = evenParity ((before.registers left).setWidth 8 - value)
  af : after.flags.getLsbD 4 = true ↔ (before.registers left).toNat % 16 < value.toNat % 16
  zf : after.flags.getLsbD 6 = ((before.registers left).setWidth 8 == value)
  sf : after.flags.getLsbD 7 = ((before.registers left).setWidth 8 - value).msb
  of : after.flags.getLsbD 11 = true ↔
    ((before.registers left).setWidth 8).toInt - value.toInt < -(128 : Int) ∨
      128 ≤ ((before.registers left).setWidth 8).toInt - value.toInt

/-- One common result for every choice, with the actual DATA1 read. No
assumption about the old arithmetic/nonarithmetic flags or GPR banks occurs. -/
theorem execute_cmpRegMem8_contract (before : State) (left : Register) (address : Address)
    (prefixed : Bool) (value : Byte)
    (loaded : readDataByte before.memory (address.eval before) = .ok value) :
    ∃ after, (∀ choice, execute before (.cmpRegMem8 left address prefixed) choice =
      .ok ⟨.next after, [⟨.data,address.eval before,1⟩]⟩) ∧
      ByteCompareContext before after left address value prefixed := by
  refine ⟨{ before with
      rip := before.rip + BitVec.ofNat 64 (Instruction.cmpRegMem8 left address prefixed).length
      flags := cmpFlags8 before.flags ((before.registers left).setWidth 8) value }, ?_, ?_⟩
  · intro choice
    rw [execute_cmpRegMem8, loaded]
    rfl
  · refine {
      loaded := loaded, registers := rfl, memory := rfl, rip := rfl
      otherFlags := cmpFlags8_preserves ..
      cf := ?_, pf := (cmpFlags8_bits ..).2.1
      af := ?_, zf := cmpFlags8_zero ..
      sf := (cmpFlags8_bits ..).2.2.2.2.1, of := cmpFlags8_overflow .. }
    · simpa only [BitVec.toNat_setWidth] using
        cmpFlags8_borrow before.flags ((before.registers left).setWidth 8) value
    · simpa only [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 256)] using
        cmpFlags8_auxiliary before.flags ((before.registers left).setWidth 8) value

/-- Inversion retains actual load success and the observed read's origin;
there is no register-only or unchecked-memory fallback on a failed read. -/
theorem execute_cmpRegMem8_observed {before after : State} {left : Register} {address : Address}
    {prefixed choice : Bool} {reads : List Read}
    (actual : execute before (.cmpRegMem8 left address prefixed) choice =
      .ok ⟨.next after, reads⟩) :
    reads = [⟨.data,address.eval before,1⟩] ∧
      ∃ value, ByteCompareContext before after left address value prefixed := by
  obtain ⟨value, loaded, same⟩ := execute_cmpRegMem8_success_iff.mp actual
  obtain ⟨final, effect, context⟩ := execute_cmpRegMem8_contract before left address prefixed value loaded
  rw [effect choice] at actual
  cases actual
  exact ⟨rfl, value, context⟩

theorem step_cmpRegMem8 {before : State} {left : Register} {address : Address} {prefixed : Bool}
    (decoded : decodeAt before = .ok (.cmpRegMem8 left address prefixed)) (choice : Bool) :
    step choice before = execute before (.cmpRegMem8 left address prefixed) choice :=
  step_eq_execute choice decoded

theorem cmpRegMem8_effects (before : State) (left : Register) (address : Address) (prefixed : Bool) :
    (Instruction.cmpRegMem8 left address prefixed).operandReads before =
      [⟨.data,address.eval before,1⟩] ∧
    (Instruction.cmpRegMem8 left address prefixed).storeIntent before = none ∧
    (Instruction.cmpRegMem8 left address prefixed).storeIntent64 before = none ∧
    (Instruction.cmpRegMem8 left address prefixed).isLocked = false ∧
    (Instruction.cmpRegMem8 left address prefixed).choiceFlag before = none ∧
    CFG.readOnly (.cmpRegMem8 left address prefixed) = true := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- All NOPs, including exact NOP15, preserve the complete state except RIP.
Their memory-like suffix never evaluates an operand address or queries DATA.
This is a model theorem. Hardware correspondence requires `targetProfile`
and support of the exact repeated-prefix `fifteen` form on the selected CPU. -/
theorem execute_nop_context (before : State) (encoding : NopEncoding) :
    ∃ after, (∀ choice, execute before (.nop encoding) choice = .ok ⟨.next after,[]⟩) ∧
      after.registers = before.registers ∧ after.memory = before.memory ∧
      after.flags = before.flags ∧ after.rip = before.rip + BitVec.ofNat 64 encoding.length :=
  ⟨_, fun _ => rfl, rfl, rfl, rfl, rfl⟩

theorem execute_cmpRegMem8_choice_independent (before : State) (left : Register) (address : Address)
    (prefixed first second : Bool) :
    execute before (.cmpRegMem8 left address prefixed) first =
      execute before (.cmpRegMem8 left address prefixed) second := rfl

end EDSL.X86.Sequential

namespace EDSL.X86.CallReturn

theorem execute_cmpRegMem8 (before : State) (left : Register) (address : Sequential.Address)
    (prefixed choice : Bool) :
    execute before (liftSequential (.cmpRegMem8 left address prefixed)) choice =
      Sequential.execute before (.cmpRegMem8 left address prefixed) choice := execute_liftSequential ..

theorem execute_nop (before : State) (encoding : Sequential.NopEncoding) (choice : Bool) :
    execute before (liftSequential (.nop encoding)) choice =
      Sequential.execute before (.nop encoding) choice := execute_liftSequential ..

end EDSL.X86.CallReturn

namespace EDSL.X86.VCGen
open Sequential

/-- Production WP exposes the real read permission in the CURRENT prestate,
its actual load success, and the fallthrough continuation for all choices. -/
theorem wp_cmpRegMem8_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (before : State) (Post : Contract) (left : Register) (address : Address) (prefixed : Bool)
    (instruction : (graph.node node).instruction = .cmpRegMem8 left address prefixed) :
    wp graph base AllowedRead (fuel + 1) node before Post ↔
      ∃ value, readDataByte before.memory (address.eval before) = .ok value ∧
        AllowedRead before ⟨.data,address.eval before,1⟩ ∧
        ∃ next : graph.Index,
          let after := { before with
            rip := before.rip + BitVec.ofNat 64 (Instruction.cmpRegMem8 left address prefixed).length
            flags := cmpFlags8 before.flags ((before.registers left).setWidth 8) value }
          after.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
          wp graph base AllowedRead fuel next after
            (fun result => Post (result.prepend 1 [⟨.data,address.eval before,1⟩])) := by
  cases loaded : readDataByte before.memory (address.eval before) <;>
    simp [wp, instruction, Sequential.execute_cmpRegMem8, loaded]

theorem wp_nop_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (before : State) (Post : Contract) (encoding : NopEncoding)
    (instruction : (graph.node node).instruction = .nop encoding) :
    let after := { before with rip := before.rip + BitVec.ofNat 64 encoding.length }
    wp graph base AllowedRead (fuel + 1) node before Post ↔
      ∃ next : graph.Index,
        after.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        wp graph base AllowedRead fuel next after (fun result => Post (result.prepend 1 [])) := by
  apply wp_pure_next_iff
  intro choice
  rw [instruction]
  rfl

end EDSL.X86.VCGen

namespace EDSL.BufferCall
open X86 X86.Sequential

/-- A DATA1 comparison needs current buffer authority even when the effective
address uses RSP. The SAME complete resource world survives the comparison. -/
theorem Current.cmpRegMem8_step {spec : Spec} {resource : Resources spec} {before : State}
    {left : Register} {address : Address} {prefixed : Bool}
    (current : Current resource before)
    (decoded : Sequential.decodeAt before = .ok (.cmpRegMem8 left address prefixed))
    (footprint : DataRead (spec.buffers resource.value) ⟨.data,address.eval before,1⟩) :
    ∃ value after, (∀ choice, Sequential.step choice before =
        .ok ⟨.next after,[⟨.data,address.eval before,1⟩]⟩) ∧
      Current resource after ∧ ReadAllowed resource ⟨.data,address.eval before,1⟩ ∧
      ByteCompareContext before after left address value prefixed := by
  obtain ⟨_,_,_,_,_,_,loaded⟩ := current.contract.dataRead_bytes footprint (by decide : 0 < 1)
  have actual : ∃ value, readDataByte before.memory (address.eval before) = .ok value := by
    rw [current.coupled]
    exact ⟨_, by simpa using loaded⟩
  obtain ⟨value,loaded⟩ := actual
  obtain ⟨after,effect,context⟩ := execute_cmpRegMem8_contract before left address prefixed value loaded
  exact ⟨value,after,fun choice => (step_eq_execute choice decoded).trans (effect choice),
    current.sameMemory context.memory,
    .inr ⟨footprint,current.contract.dataRead_permission footprint⟩,context⟩

end EDSL.BufferCall

namespace EDSL.PureCall
open X86 X86.Sequential

/-- Caller STACK8 authority never authorizes this DATA1 read, including a
left/base/index RSP alias or bytes overlapping the original return slot. -/
theorem cmpRegMem8_not_rawRead (initial before : State) (address : Address) :
    ¬ RawRead initial ⟨.data,address.eval before,1⟩ := by
  simp [RawRead]

end EDSL.PureCall
