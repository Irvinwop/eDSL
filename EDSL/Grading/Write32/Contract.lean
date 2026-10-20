/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Trace
import EDSL.OS.WordStore
import EDSL.OS.Borrowing

set_option warningAsError true

namespace EDSL.Grading.Write32
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS
open EDSL.Grading.Trace

/-- Mathematical arguments independent of instruction selection. The high
32 RSI bits are arbitrary; only the low 32 bits determine the stored value.
`oldValue` makes a useful changing-value domain witness expressible. -/
structure Input where
  address : Word
  argument : Word
  oldValue : BitVec 32
  returnAddress : Word

def Useful (input : Input) : Prop := input.oldValue ≠ input.argument.setWidth 32

/-- Present-only domain: actual executable bytes, ABI inputs, complete target
permissions, real eight-byte caller slot and disjoint write footprint. There
is no decode, CFG, policy, successful-store or future-execution premise. -/
structure Pre (bytes : List Byte) (input : Input) (initial : State) : Prop where
  code : CodeAt initial.memory initial.rip bytes
  pointer : initial.registers .rdi = input.address
  source : initial.registers .rsi = input.argument
  oldValue : loadDWord initial.memory input.address = .ok input.oldValue
  writable : canStoreDWord initial.memory input.address = true
  codeDisjoint : DWordDisjoint input.address initial.rip bytes.length
  stackDisjoint : DWordDisjoint input.address (initial.registers .rsp) 8
  stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress
  returnCanonical : canonical input.returnAddress = true
  stackBound : (initial.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (initial.registers .rsp + 8) = true

/-- SysV AMD64 callee-saved general registers. RSP has its separate RET rule.
No volatile register, including RAX for this void operation, is constrained. -/
def calleeSaved : List Register := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Independent low32 mathematical store, complete outside-RAM/permission
frame, actual caller return and ABI frame. No instruction count, chosen
intermediate values, volatile-register result or arithmetic flags are fixed. -/
structure Post (input : Input) (initial final : State) : Prop where
  value : loadDWord final.memory input.address = .ok (input.argument.setWidth 32)
  outside : ∀ query, ¬(AddressSpace.wordRegion input.address).Contains query →
    final.memory.read query = initial.memory.read query
  writable : final.memory.writable = initial.memory.writable
  executable : final.memory.executable = initial.memory.executable
  returnAddress : final.rip = input.returnAddress
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register ∈ calleeSaved, final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

/-- Successful full-byte permission checking includes canonicality and
nonwrapping of the entire target, not merely a writable first byte. -/
theorem Pre.target_addressable {bytes input initial} (pre : Pre bytes input initial) :
    dwordAddressable input.address = true := (Bool.and_eq_true_iff.mp pre.writable).1

/-- Fetches stay within the admitted selected span; decoding still uses the
actual current executable RAM at every step. RET's destination is a caller
boundary and is not fetched as part of this call. -/
def FetchAllowed (base : Word) (length : Nat) (before : State)
    (instruction : Sequential.Instruction) : Prop :=
  Borrowing.Subregion ⟨before.rip, instruction.length⟩ ⟨base, length⟩

/-- Policy decision: any intermediate value may be ordinarily stored to the
fixed input target. A write to another address is disallowed even if it is
later restored. The two modeled ordinary store encodings are both allowed;
locked RMW, syscall and every other effectful instruction are excluded. -/
def RawEffect (target : Word) (before : State) (instruction : Sequential.Instruction) : Prop :=
  CFG.readOnly instruction = true ∨
    ∃ value, instruction.storeIntent before = some (target, value)

def rawRules (bytes : List Byte) (input : Input) (initial : State) : Rules Unit where
  Current _ _ := True
  ReadAllowed _ _ _ := True
  Effect _ before instruction _ _ :=
    FetchAllowed initial.rip bytes.length before instruction ∧ RawEffect input.address before instruction

/-- Raw Ghost=Unit policy uses the same actual-prefix machinery as the
resource policy. It is semantic claim evidence, never an input premise. -/
def RawPolicy (bytes : List Byte) (input : Input) (initial : State) : Prop :=
  Policy (rawRules bytes input initial) () initial

/-- A fixed-target effect cannot authorize a different decoded store. -/
theorem rawEffect_rejects_other_target {target address value before instruction}
    (effect : RawEffect target before instruction)
    (notReadOnly : CFG.readOnly instruction = false)
    (intent : instruction.storeIntent before = some (address, value))
    (different : address ≠ target) : False := by
  rcases effect with allowed | ⟨stored, expected⟩
  · rw [notReadOnly] at allowed
    cases allowed
  · have same := Option.some.inj (expected.symm.trans intent)
    exact different (congrArg Prod.fst same).symm

theorem rawEffect_rejects_unsupported_effect {target before instruction}
    (effect : RawEffect target before instruction)
    (notReadOnly : CFG.readOnly instruction = false)
    (noStore : instruction.storeIntent before = none) : False := by
  rcases effect with allowed | ⟨_, expected⟩
  · rw [notReadOnly] at allowed
    cases allowed
  · rw [noStore] at expected
    cases expected

/-- Every real prefix carries the fixed-target classification of its ACTUAL
current decode, so temporary unauthorized writes followed by restoration
cannot satisfy the raw policy. This does not assume a future return. -/
theorem RawPolicy.prefix {bytes input initial} (policy : RawPolicy bytes input initial)
    {choices before count reads} (block : Block choices initial before count reads) :
    ∃ instruction, Sequential.decodeAt before = .ok instruction ∧
      FetchAllowed initial.rip bytes.length before instruction ∧ RawEffect input.address before instruction := by
  obtain ⟨Inv, start, advance⟩ := policy
  obtain ⟨ghost, _, inside⟩ := policy_prefix_invariant advance block start
  obtain ⟨_, instruction, decoded, enabled⟩ := advance ghost before inside
  obtain ⟨_, _, _, _, effect, _⟩ := enabled false
  exact ⟨instruction, decoded, effect⟩

/-- Rejection depends on the actual reachable prefix, not the final bytes. -/
theorem RawPolicy.rejects_other_target {bytes input initial before}
    (policy : RawPolicy bytes input initial) (reachable : Reachable initial before)
    {instruction address value}
    (decoded : Sequential.decodeAt before = .ok instruction)
    (notReadOnly : CFG.readOnly instruction = false)
    (intent : instruction.storeIntent before = some (address, value))
    (different : address ≠ input.address) : False := by
  obtain ⟨choices, count, reads, block⟩ := reachable
  obtain ⟨expected, actual, _, effect⟩ := policy.prefix block
  have same := Except.ok.inj (actual.symm.trans decoded)
  cases same
  exact rawEffect_rejects_other_target effect notReadOnly intent different

/-- All modeled atomics and syscalls are excluded at every real prefix. -/
theorem RawPolicy.rejects_unsupported_effect {bytes input initial before}
    (policy : RawPolicy bytes input initial) (reachable : Reachable initial before)
    {instruction} (decoded : Sequential.decodeAt before = .ok instruction)
    (notReadOnly : CFG.readOnly instruction = false)
    (noStore : instruction.storeIntent before = none) : False := by
  obtain ⟨_, _, _, block⟩ := reachable
  obtain ⟨expected, actual, _, effect⟩ := policy.prefix block
  have same := Except.ok.inj (actual.symm.trans decoded)
  cases same
  exact rawEffect_rejects_unsupported_effect effect notReadOnly noStore

end EDSL.Grading.Write32
