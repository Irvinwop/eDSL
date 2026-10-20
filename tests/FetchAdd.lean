/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics
import EDSL.Certificate
import EDSL.Audit

namespace EDSL.Tests.FetchAdd
open X86 OS.AddressSpace

def memory (old : BitVec 32) : Memory where
  read address := match address.toNat with
    | 4096 => some 0x89 | 4097 => some 0xf0 | 4098 => some 0xf0
    | 4099 => some 0x0f | 4100 => some 0xc1 | 4101 => some 0x07 | 4102 => some 0xc3
    | 32769 => some 0x20
    | 32768 | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some 0
    | 65536 => some (old.extractLsb' 0 8) | 65537 => some (old.extractLsb' 8 8)
    | 65538 => some (old.extractLsb' 16 8) | 65539 => some (old.extractLsb' 24 8)
    | 65540 => some 0xa5 | _ => none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4103)
  writable address := decide (65536 ≤ address.toNat ∧ address.toNat < 65540)

def entry (old : BitVec 32) (delta : Word) : State where
  memory := memory old
  registers register := if register = .rdi then 65536 else if register = .rsi then delta
    else if register = .rsp then 32768 else 0xdeadbeefcafebabe
  rip := 4096
  flags := 0xffffffffffffffff

def observe (old : BitVec 32) (delta : Word) : Except Error
    (Word × Option (BitVec 32) × Word × Word × Word × Word × Option Byte) := do
  let result ← run 3 (entry old delta)
  let state := result.state
  pure (state.registers .rax, (loadDWord state.memory 65536).toOption,
    state.flags &&& arithmeticFlagMask, state.flags &&& ~~~arithmeticFlagMask,
    state.registers .rsp, state.rip, state.memory.read 65540)

private theorem code (old : BitVec 32) : CodeAt (memory old) 4096 Examples.Compiler.FetchAdd.bytes := by
  refine ⟨by decide, ?_⟩
  intro offset byte present
  match offset with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 =>
    simp [Examples.Compiler.FetchAdd.bytes] at present
    subst byte
    rfl
  | offset + 7 => simp [Examples.Compiler.FetchAdd.bytes] at present

private theorem old_word (old : BitVec 32) : loadDWord (memory old) 65536 = .ok old := by
  change Except.ok (joinDWord (old.extractLsb' 0 8) (old.extractLsb' 8 8)
    (old.extractLsb' 16 8) (old.extractLsb' 24 8)) = .ok old
  rw [join_extracts]

private theorem code_disjoint : DWordDisjoint 65536 4096 7 := by
  intro offset bound
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 ∨ offset = 5 ∨ offset = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem stack_disjoint : DWordDisjoint 65536 32768 8 := by
  intro offset bound
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
    offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem every_input_executes (old : BitVec 32) (delta : Word) :
    AtomicExecutes (entry old delta)
      (Examples.Compiler.FetchAdd.finalState (entry old delta) old 8192) 3
      [⟨65536, old, old + delta.setWidth 32⟩] := by
  apply Examples.Compiler.FetchAdd.atomic_execution
  · exact code old
  · change atomicAddressable 65536 = true
    decide
  · rfl
  · exact old_word old
  · exact code_disjoint
  · exact stack_disjoint
  · rfl
  · rfl

-- Fixed independent carry, auxiliary-carry, parity and signed-overflow outcomes;
-- nonzero upper source bits must neither affect the sum nor survive in RAX.
example : observe 0xffffffff 0xfeedface00000001 =
    .ok (0xffffffff, some 0, 0x55, 0xfffffffffffff72a, 32776, 8192, some 0xa5) := by rfl
example : observe 0x7fffffff 1 =
    .ok (0x7fffffff, some 0x80000000, 0x894, 0xfffffffffffff72a, 32776, 8192, some 0xa5) := by rfl
example : observe 0x80000000 0x80000000 =
    .ok (0x80000000, some 0, 0x845, 0xfffffffffffff72a, 32776, 8192, some 0xa5) := by rfl
example : observe 0xf 1 =
    .ok (0xf, some 0x10, 0x10, 0xfffffffffffff72a, 32776, 8192, some 0xa5) := by rfl

example : Certificate.accepts .fetchAdd32 [0x89, 0xf0, 0x0f, 0xc1, 0x07, 0xc3] = false := by decide
example : Certificate.accepts .exchange32 Examples.Compiler.FetchAdd.bytes = false := by decide

def atAdd : State := { entry 0 1 with rip := 4098 }
example : decodeAt { atAdd with rip := 4099 } = .error .unsupportedEncoding := by rfl
example : decodeAt { atAdd with memory := { atAdd.memory with
    read := fun address => if address = 4101 then some 0x08 else atAdd.memory.read address } } =
    .error .unsupportedEncoding := by rfl
example : decodeAt { atAdd with memory := { atAdd.memory with
    executable := fun address => decide (address ≠ 4101) && atAdd.memory.executable address } } =
    .error (.inaccessibleInstruction 4101) := by rfl

example : fetchAddDWord (memory 0) 65537 1 = .error (.unsupportedAtomicAddress 65537) := by rfl
example : fetchAddDWord { memory 0 with writable := fun address => decide (address ≠ 65539) } 65536 1 =
    .error (.writeDenied 65536) := by rfl

def initial : OS.Atomics.State := OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty empty))
def setup : Except OS.Atomics.Fault (OS.Atomics.State × OS.Ownership.Ticket) := do
  let (allocated, result) ← OS.Atomics.mutate initial (.allocate 0 ⟨65536, 8⟩ readWrite)
  let some ticket := result | throw .missingHandle
  let (written, _) ← OS.Atomics.mutate allocated (.store 0 ticket 65536 0xffffffff)
  let (one, _) ← OS.Atomics.issue written 0 ticket 7 65536
  let (both, _) ← OS.Atomics.issue one 0 ticket 9 65536
  pure (both, ticket)

def resourceCounter : Except OS.Atomics.Fault (BitVec 32 × BitVec 32 × Option (BitVec 32) × Bool × Bool) := do
  let (shared, ticket) ← setup
  let (one, oldA) ← OS.Atomics.fetchAdd shared 7 0 2
  let (both, oldB) ← OS.Atomics.fetchAdd one 9 1 3
  let wrong := match OS.Atomics.fetchAdd both 7 1 99 with | .error .wrongActor => true | _ => false
  let blocked := match OS.Atomics.mutate both (.store 0 ticket 65536 0) with | .error .reserved => true | _ => false
  pure (oldA, oldB, (loadDWord (toMemory both.shared.resources.space) 65536).toOption, wrong, blocked)

example : resourceCounter = .ok (0xffffffff, 1, some 4, true, true) := by rfl

-- Checked allocation and handle issuance witness every symbolic old/delta pair.
def allocated : OS.Atomics.State := OS.Atomics.empty (OS.Borrowing.empty
  (OS.Ownership.install (OS.Ownership.empty empty) (mapUnchecked empty ⟨65536, 8⟩ readWrite) 0 ⟨65536, 8⟩))
def live : OS.Atomics.State := OS.Atomics.install allocated ⟨0, ⟨0, 0⟩, 7, 65536⟩

theorem live_valid : OS.Atomics.WellFormed live := by
  have emptyValid := OS.Atomics.empty_wellFormed _ (OS.Borrowing.empty_wellFormed _ (OS.Ownership.empty_wellFormed empty))
  have allocatedValid := OS.Atomics.mutate_wellFormed initial (.allocate 0 ⟨65536, 8⟩ readWrite)
    (allocated, some ⟨0, 0⟩) emptyValid (by rfl)
  exact (OS.Atomics.issue_wellFormed allocated 0 ⟨0, 0⟩ 7 65536 (live, 0) allocatedValid (by rfl)).1

theorem every_old_and_delta (old delta : BitVec 32) :
    ∃ before after, OS.Atomics.WellFormed before ∧
      OS.Atomics.fetchAdd before 7 0 delta = .ok (after, old) ∧
      loadDWord (toMemory after.shared.resources.space) 65536 = .ok (old + delta) := by
  obtain ⟨written, success⟩ := OS.Atomics.exchange_enabled live 7 0 ⟨0, ⟨0, 0⟩, 7, 65536⟩ old live_valid (by rfl)
  have valid := OS.Atomics.exchange_wellFormed _ _ _ _ _ live_valid success
  obtain ⟨handle, _, authorized, _, same⟩ := OS.Atomics.exchange_ok _ _ _ _ _ success
  have handleEq : handle = ⟨0, ⟨0, 0⟩, 7, 65536⟩ := Except.ok.inj authorized.symm
  subst handle
  have nextAuthority : OS.Atomics.authorize written.1 7 0 = .ok ⟨0, ⟨0, 0⟩, 7, 65536⟩ := by rw [same]; rfl
  obtain ⟨result, added⟩ := OS.Atomics.fetchAdd_enabled written.1 7 0 _ delta valid nextAuthority
  obtain ⟨firstHandle, firstAuth, first⟩ := OS.Atomics.exchange_sound _ _ _ _ _ success
  have firstEq : firstHandle = ⟨0, ⟨0, 0⟩, 7, 65536⟩ := Except.ok.inj firstAuth.symm
  subst firstHandle
  obtain ⟨lastHandle, lastAuth, last⟩ := OS.Atomics.fetchAdd_sound _ _ _ _ _ added
  have lastEq := Except.ok.inj (lastAuth.symm.trans nextAuthority)
  subst lastHandle
  have oldEq : result.2 = old := Except.ok.inj (last.2.2.1.symm.trans first.readback)
  exact ⟨written.1, result.1, valid,
    added.trans (congrArg Except.ok (Prod.ext rfl oldEq)), by simpa [oldEq] using last.readback⟩

end EDSL.Tests.FetchAdd

#audit_edsl
