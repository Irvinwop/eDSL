/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.AddRMW64.Machine

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.AddRMW64

theorem Effect.transition {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    RMWTransition64 initial.memory event.event final.memory :=
  (fetchAddQWord_sound _ _ _ _ effect.primitive).1

theorem Effect.delta {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) : event.delta = instruction.delta initial :=
  (fetchAddQWord_sound _ _ _ _ effect.primitive).2.1

theorem Effect.address {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) : event.event.address = initial.registers instruction.base :=
  (fetchAddQWord_sound _ _ _ _ effect.primitive).2.2.1

theorem Effect.after {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) : event.event.after = event.event.before + event.delta := by
  rw [effect.delta]
  exact (fetchAddQWord_sound _ _ _ _ effect.primitive).2.2.2

theorem Effect.modular {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    event.event.after.toNat = (event.event.before.toNat + event.delta.toNat) % 2^64 := by
  rw [effect.delta]
  exact fetchAddQWord_modular _ _ _ _ effect.primitive

theorem Effect.old {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    loadQWord initial.memory event.event.address = .ok event.event.before := effect.transition.2.2.1

theorem Effect.readback {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    loadQWord final.memory event.event.address = .ok event.event.after := effect.transition.readback

theorem Effect.register_frame {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (register : Register)
    (other : instruction.oldDestination ≠ some register) :
    final.registers register = initial.registers register := by
  rw [effect.registers]
  cases destination : instruction.oldDestination with
  | none => simp [Instruction.registersAfter, destination]
  | some target =>
    have different : register ≠ target := by
      rintro rfl
      exact other destination
    simp [Instruction.registersAfter, destination, State.writeRegister, different]

theorem Effect.all_registers {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (noDestination : instruction.oldDestination = none) :
    final.registers = initial.registers := by
  rw [effect.registers]
  simp [Instruction.registersAfter, noDestination]

theorem Effect.addImm8_registers {initial final : State} {encoding : AddImm8Encoding}
    {event : FetchAddEvent64} (effect : Effect initial (.addImm8 encoding) event final) :
    final.registers = initial.registers := effect.all_registers rfl

theorem Effect.inc_registers {initial final : State} {encoding : IncEncoding}
    {event : FetchAddEvent64} (effect : Effect initial (.inc encoding) event final) :
    final.registers = initial.registers := effect.all_registers rfl

/-- Only XADD has a source receiving the old word. This includes every
legacy source, including base aliases and RSP. -/
theorem Effect.source_old {initial final : State} {old : LockedAdd64.Instruction} {event : FetchAddEvent64}
    (effect : Effect initial (.xadd old) event final) :
    final.registers old.source = event.event.before := by
  simp [effect.registers, Instruction.registersAfter, Instruction.oldDestination, State.writeRegister]

theorem Effect.permissions {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    final.memory.executable = initial.memory.executable ∧
    final.memory.writable = initial.memory.writable := effect.transition.permissions

theorem Effect.full_permissions {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (offset : Nat) (bound : offset < 8) :
    initial.memory.writable (event.event.address + BitVec.ofNat 64 offset) = true ∧
    (initial.memory.read (event.event.address + BitVec.ofNat 64 offset)).isSome = true :=
  effect.transition.full_permissions offset bound

theorem Effect.frame {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (query : Word)
    (outside : 8 ≤ (query - event.event.address).toNat) :
    final.memory.read query = initial.memory.read query := effect.transition.frame query outside

theorem Effect.preserves_code {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (base : Word) (bytes : List Byte)
    (code : CodeAt initial.memory base bytes)
    (disjoint : QWordDisjoint event.event.address base bytes.length) :
    CodeAt final.memory base bytes := effect.transition.preserves_code base bytes code disjoint

/-- The dataOnly gate separates the operand from every currently executable
byte, so clients need no separate expected-address disjointness premise. -/
theorem Effect.code_disjoint {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (base : Word) (bytes : List Byte)
    (code : CodeAt initial.memory base bytes) :
    QWordDisjoint event.event.address base bytes.length := by
  intro offset bound
  let query := base + BitVec.ofNat 64 offset
  by_cases outside : 8 ≤ (query - event.event.address).toNat
  · exact outside
  have small : (query - event.event.address).toNat < 8 := by omega
  have nonExecutable := dataOnly64_bytes initial.memory (initial.registers instruction.base)
    effect.dataOnly (query - event.event.address).toNat small
  have location : event.event.address + BitVec.ofNat 64 (query - event.event.address).toNat = query := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [← effect.address, location] at nonExecutable
  let byte := bytes[offset]'bound
  have present : bytes[offset]? = some byte := List.getElem?_eq_getElem bound
  have fetched := code.2 offset byte present
  unfold fetchByte at fetched
  split at fetched
  next allowed =>
    have executable := (Bool.and_eq_true_iff.mp allowed).2
    rw [nonExecutable] at executable
    contradiction
  next => cases fetched

theorem Effect.preserves_all_code {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (base : Word) (bytes : List Byte)
    (code : CodeAt initial.memory base bytes) : CodeAt final.memory base bytes :=
  effect.preserves_code base bytes code (effect.code_disjoint base bytes code)

theorem Effect.nonarithmetic_flags {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask := by
  rw [effect.flags]
  exact instruction.flagsAfter_preserves ..

/-- All defined flags at full64 width. Unlike the old XADD-only tuple,
this tuple explicitly selects incoming CF for INC. -/
theorem Effect.flag_bits {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    final.flags.getLsbD 0 =
      (if instruction.isInc then initial.flags.getLsbD 0 else event.event.before.uaddOverflow event.delta) ∧
    final.flags.getLsbD 2 = evenParity (event.event.after.setWidth 8) ∧
    final.flags.getLsbD 4 = (event.event.before.setWidth 4).uaddOverflow (event.delta.setWidth 4) ∧
    final.flags.getLsbD 6 = (event.event.after == 0) ∧
    final.flags.getLsbD 7 = event.event.after.msb ∧
    final.flags.getLsbD 11 = event.event.before.saddOverflow event.delta := by
  rw [effect.flags, effect.after, effect.delta]
  exact instruction.flagsAfter_bits initial event.event.before

/-- ADD/XADD only: unsigned arithmetic carry, with no analogous premise-free
claim for INC. -/
theorem Effect.add_carry {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) (adds : instruction.isInc = false) :
    final.flags.getLsbD 0 = true ↔ 2^64 ≤ event.event.before.toNat + event.delta.toNat := by
  rw [effect.flag_bits.1]
  simp [adds, BitVec.uaddOverflow]

theorem Effect.inc_carry {initial final : State} {encoding : IncEncoding} {event : FetchAddEvent64}
    (effect : Effect initial (.inc encoding) event final) :
    final.flags.getLsbD 0 = initial.flags.getLsbD 0 := by
  rw [effect.flags]
  exact Sequential.incFlags64_carry ..

theorem Effect.overflow {initial final : State} {instruction : Instruction} {event : FetchAddEvent64}
    (effect : Effect initial instruction event final) :
    final.flags.getLsbD 11 = true ↔
      event.event.before.toInt + event.delta.toInt < -(2^63 : Int) ∨
      2^63 ≤ event.event.before.toInt + event.delta.toInt := by
  rw [effect.flag_bits.2.2.2.2.2]
  simp [BitVec.saddOverflow, or_comm]

end EDSL.X86.AddRMW64
