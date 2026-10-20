/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreLoad64.Resources

set_option warningAsError true

namespace EDSL.Grading.StoreReturnValue64
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS EDSL.Grading.Trace

abbrev Input := EDSL.StoreLoad64.Input
abbrev Pre := EDSL.StoreLoad64.Pre
abbrev Resources := EDSL.StoreLoad64.Resources
abbrev ResourcePre := EDSL.StoreLoad64.ResourcePre
abbrev resourceInput := EDSL.StoreLoad64.resourceInput
abbrev calleeSaved := EDSL.StoreLoad64.calleeSaved

/-- Changing-value witnesses compare the complete mathematical 64-bit input. -/
def Useful (input : Input) : Prop := input.oldValue ≠ input.argument

/-- Independent full64 result and complete eight-byte/ABI frame. Arithmetic
flags, instruction selection, counts and read order are unconstrained. -/
structure Post (input : Input) (initial final : State) : Prop where
  result : final.registers .rax = input.argument
  value : loadQWord final.memory input.address = .ok input.argument
  outside : ∀ query, 8 ≤ (query - input.address).toNat →
    final.memory.read query = initial.memory.read query
  writable : final.memory.writable = initial.memory.writable
  executable : final.memory.executable = initial.memory.executable
  returnAddress : final.rip = input.returnAddress
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register ∈ calleeSaved, final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem post_of_strict {input initial final}
    (post : EDSL.StoreLoad64.Post input initial final) : Post input initial final :=
  ⟨post.result, post.value, post.outside, post.writable, post.executable,
    post.returnAddress, post.stackPointer, post.preserved,
    congrArg (fun flags => flags &&& ~~~arithmeticFlagMask) post.flags⟩

def FetchAllowed (base : Word) (length : Nat) (before : State)
    (instruction : Sequential.Instruction) : Prop :=
  Borrowing.Subregion ⟨before.rip, instruction.length⟩ ⟨base, length⟩

/-- Ordinary writes are governed by their entire actual footprint. A narrow
store may touch any four bytes wholly inside the owned eight-byte target. -/
inductive RawEffect (target : Word) (before : State)
    (instruction : Sequential.Instruction) : Prop where
  | readOnly (allowed : CFG.readOnly instruction = true) : RawEffect target before instruction
  | store32 {address : Word} {value : BitVec 32}
      (intent : instruction.storeIntent before = some (address, value))
      (span : Borrowing.Subregion (AddressSpace.wordRegion address) (AddressSpace.qwordRegion target)) :
      RawEffect target before instruction
  | store64 {value : Word}
      (intent : instruction.storeIntent64 before = some (target, value)) :
      RawEffect target before instruction

theorem RawEffect.store32_span {target before instruction address value}
    (effect : RawEffect target before instruction)
    (notReadOnly : CFG.readOnly instruction = false)
    (intent : instruction.storeIntent before = some (address, value))
    (noStore64 : instruction.storeIntent64 before = none) :
    Borrowing.Subregion (AddressSpace.wordRegion address) (AddressSpace.qwordRegion target) := by
  cases effect with
  | readOnly allowed => rw [notReadOnly] at allowed; cases allowed
  | store32 expected span =>
    have same := congrArg Prod.fst (Option.some.inj (expected.symm.trans intent))
    cases same
    exact span
  | store64 expected => rw [noStore64] at expected; cases expected

theorem RawEffect.store64_target {target before instruction address value}
    (effect : RawEffect target before instruction)
    (notReadOnly : CFG.readOnly instruction = false)
    (noStore32 : instruction.storeIntent before = none)
    (intent : instruction.storeIntent64 before = some (address, value)) : address = target := by
  cases effect with
  | readOnly allowed => rw [notReadOnly] at allowed; cases allowed
  | store32 expected _ => rw [noStore32] at expected; cases expected
  | store64 expected =>
    exact (congrArg Prod.fst (Option.some.inj (expected.symm.trans intent))).symm

theorem RawEffect.rejects_unsupported {target before instruction}
    (effect : RawEffect target before instruction)
    (notReadOnly : CFG.readOnly instruction = false)
    (noStore32 : instruction.storeIntent before = none)
    (noStore64 : instruction.storeIntent64 before = none) : False := by
  cases effect with
  | readOnly allowed => rw [notReadOnly] at allowed; cases allowed
  | store32 expected _ => rw [noStore32] at expected; cases expected
  | store64 expected => rw [noStore64] at expected; cases expected
/-- Raw execution checks actual readable RAM. Current loan/owner authority is
the additional obligation of the resource rules. Stack operands always use
the original complete caller slot; data operands retain their actual width. -/
def RawReadAllowed (initial : State) (read : Read) : Prop :=
  match read.kind with
  | .stack => read.address = initial.registers .rsp ∧ read.bytes = 8
  | .data => read.bytes = 4 ∨ read.bytes = 8

def rawRules (bytes : List Byte) (input : Input) (initial : State) : Rules Unit where
  Current _ _ := True
  ReadAllowed _ _ := RawReadAllowed initial
  Effect _ before instruction _ _ :=
    FetchAllowed initial.rip bytes.length before instruction ∧ RawEffect input.address before instruction

def RawPolicy (bytes : List Byte) (input : Input) (initial : State) : Prop :=
  Policy (rawRules bytes input initial) () initial

theorem RawPolicy.prefix {bytes input initial} (policy : RawPolicy bytes input initial)
    {choices before count reads} (block : Block choices initial before count reads) :
    ∃ instruction, Sequential.decodeAt before = .ok instruction ∧
      FetchAllowed initial.rip bytes.length before instruction ∧ RawEffect input.address before instruction := by
  obtain ⟨Inv, start, advance⟩ := policy
  obtain ⟨ghost, _, inside⟩ := policy_prefix_invariant advance block start
  obtain ⟨_, instruction, decoded, enabled⟩ := advance ghost before inside
  obtain ⟨_, _, _, _, effect, _⟩ := enabled false
  exact ⟨instruction, decoded, effect⟩

/-- A forbidden actual prefix cannot be repaired by later restoring memory. -/
theorem RawPolicy.rejects_instruction {bytes input initial before}
    (policy : RawPolicy bytes input initial) (reachable : Reachable initial before)
    {instruction} (decoded : Sequential.decodeAt before = .ok instruction)
    (forbidden : ¬RawEffect input.address before instruction) : False := by
  obtain ⟨_, _, _, block⟩ := reachable
  obtain ⟨expected, actual, _, effect⟩ := policy.prefix block
  have same := Except.ok.inj (actual.symm.trans decoded)
  cases same
  exact forbidden effect

end EDSL.Grading.StoreReturnValue64
