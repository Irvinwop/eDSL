/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.LogicalPreservation
import EDSL.Logical64.Algebra
import EDSL.Audit

namespace EDSL.Tests.Atomics64Logical
open X86 OS.AddressSpace OS.Atomics64

abbrev Fault := OS.Atomics64.Fault

def seed : OS.Atomics64.State :=
  empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty OS.AddressSpace.empty)))

/-- A checked allocation, full64 initialization, persistent registration and
actor handle. The symbolic setup admits every input word and mask. -/
def allocated : OS.Atomics64.State := empty (OS.Atomics.empty (OS.Borrowing.empty
  (OS.Ownership.install (OS.Ownership.empty OS.AddressSpace.empty)
    (mapUnchecked OS.AddressSpace.empty ⟨65536, 16⟩ readWrite) 7 ⟨65536, 16⟩)))

def prepared (old : Word) : OS.Atomics64.State :=
  { allocated with legacy := { allocated.legacy with shared := { allocated.legacy.shared with
    resources := { allocated.legacy.shared.resources with
      space := writeQWordCells allocated.legacy.shared.resources.space 65536 old } } } }

def registered (old : Word) : OS.Atomics64.State :=
  installCell (prepared old) ⟨7, ⟨0, 0⟩, 65536⟩

def live (old : Word) : OS.Atomics64.State := installHandle (registered old) ⟨11, ⟨0⟩⟩

theorem allocated_valid : WellFormed allocated :=
  mutate_wellFormed seed (.allocate 7 ⟨65536, 16⟩ readWrite) (allocated, some ⟨0, 0⟩)
    (empty_wellFormed _ (OS.Atomics.empty_wellFormed _ (OS.Borrowing.empty_wellFormed _
      (OS.Ownership.empty_wellFormed OS.AddressSpace.empty)))) (by rfl)

theorem prepared_valid (old : Word) : WellFormed (prepared old) :=
  mutate_wellFormed allocated (.store64 7 ⟨0, 0⟩ 65536 old) (prepared old, none) allocated_valid (by rfl)

theorem registered_valid (old : Word) : WellFormed (registered old) :=
  (enroll_wellFormed (prepared old) 7 ⟨0, 0⟩ 65536 (registered old, ⟨0⟩) (prepared_valid old) (by rfl)).1

theorem live_valid (old : Word) : WellFormed (live old) :=
  (issue_wellFormed (registered old) 7 ⟨0⟩ 11 (live old, ⟨0⟩) (registered_valid old) (by rfl)).1

theorem live_read (old : Word) : loadQWord (toMemory (live old).legacy.shared.resources.space) 65536 = .ok old :=
  (OS.Borrowing.store64_effect (legacy_store64_guarded
    (show OS.Atomics.mutate allocated.legacy (.store64 7 ⟨0, 0⟩ 65536 old) =
      .ok ((prepared old).legacy, none) from by rfl))).readback

/-- Independent natural-number set membership, not the logical instruction
operator, specifies the answer. All three operations retain valid current
resources and read the actual initialized full64 value. -/
theorem every_operation_old_and_mask (operation : Logical64.Operation) (old mask : Word) :
    ∃ result, logicalUpdate operation.toLogicalOp (live old) 11 ⟨0⟩ mask = .ok result ∧
      WellFormed result.1 ∧ result.2.logical.event.before = old ∧
      loadQWord (toMemory result.1.legacy.shared.resources.space) 65536 = .ok result.2.logical.event.after ∧
      Logical64.MathematicalResult operation old mask result.2.logical.event.after := by
  have authorized : authorize (live old) 11 ⟨0⟩ =
      .ok (⟨11, ⟨0⟩⟩, ⟨7, ⟨0, 0⟩, 65536⟩) := by rfl
  obtain ⟨result, success⟩ := logicalUpdate_enabled _ _ _ _ _ _ _ (live_valid old) authorized
  have sound := logicalUpdate_sound _ _ _ _ _ _ success
  have identity := logicalUpdate_identity _ _ _ _ _ _ _ _ success authorized
  have beforeEq : result.2.logical.event.before = old :=
    Except.ok.inj (sound.1.2.2.1.symm.trans (identity.2 ▸ live_read old))
  refine ⟨result, success, logicalUpdate_wellFormed _ _ _ _ _ _ (live_valid old) success, beforeEq, ?_, ?_⟩
  · have readback := (logicalUpdate_effect _ _ _ _ _ _ success).shared.readback
    simpa only [identity.2] using readback
  · rw [sound.2.2.2.1, beforeEq]
    exact Logical64.eval_mathematical operation old mask

/-- Issuance precedes all three different operations. Literal expected words
catch stale-value snapshots, wrong opcode selection, high-half truncation and
failure to use another actor's most recent full64 value. -/
def mixedActors : Except Fault (List Event × Except Error Word × Except Error Word) := do
  let (both, second) ← issue (live 0xfedcba9876543210) 7 ⟨0⟩ 12
  let (one, firstEvent) ← logicalUpdate .band both 11 ⟨0⟩ 0x80000000ffffffff
  let (two, secondEvent) ← logicalUpdate .bxor one 12 second 0x8000000000000011
  let (last, thirdEvent) ← logicalUpdate .bor two 11 ⟨0⟩ 0x4000000000000002
  let memory := toMemory last.legacy.shared.resources.space
  return ([firstEvent, secondEvent, thirdEvent], loadQWord memory 65536, loadQWord memory 65544)

example : mixedActors = .ok
    ([⟨11, ⟨0⟩, ⟨0⟩, ⟨.band, 0x80000000ffffffff, ⟨65536, 0xfedcba9876543210, 0x8000000076543210⟩⟩⟩,
      ⟨12, ⟨1⟩, ⟨0⟩, ⟨.bxor, 0x8000000000000011, ⟨65536, 0x8000000076543210, 0x0000000076543201⟩⟩⟩,
      ⟨11, ⟨0⟩, ⟨0⟩, ⟨.bor, 0x4000000000000002, ⟨65536, 0x0000000076543201, 0x4000000076543203⟩⟩⟩],
     .ok 0x4000000076543203, .ok 0) := by rfl

def failureIs {α : Type} (operation : Except Fault α) (expected : Fault) : Bool :=
  match operation with
  | .error actual => decide (actual = expected)
  | .ok _ => false

def unchangedMask : Sequential.LogicalOp → Word
  | .band => 0xffffffffffffffff
  | .bor | .bxor => 0

/-- Hostile present memory, outside the admitted transition system. An old
handle cannot reuse its issuance-time permission snapshot for a no-change RMW. -/
def deniedByte (op : Sequential.LogicalOp) (offset : Nat) (permissions : Permissions)
    (expected : Fault) : Bool :=
  let state := live 0x8000000000000001
  let hostile := { state with legacy := { state.legacy with shared := { state.legacy.shared with
    resources := { state.legacy.shared.resources with
      space := protectUnchecked state.legacy.shared.resources.space
        ⟨65536 + BitVec.ofNat 64 offset, 1⟩ permissions } } } }
  failureIs (logicalUpdate op hostile 11 ⟨0⟩ (unchangedMask op)) expected

def permissionSweep (permissions : Permissions) (expected : Fault) : Bool :=
  [.band, .bor, .bxor].all fun op => (List.range 8).all fun offset => deniedByte op offset permissions expected

example : permissionSweep readOnly (.machine (.writeDenied 65536)) = true := by rfl
example : permissionSweep inaccessible (.machine (.writeDenied 65536)) = true := by rfl
example : permissionSweep ⟨true, true, true⟩ .executable = true := by rfl

-- No-change AND and XOR still emit events and leave registration active.
def noChangeAndLifetime (op : Sequential.LogicalOp) : Except Fault (Event × List Bool) := do
  let (after, event) ← logicalUpdate op (live 0x8000000000000001) 11 ⟨0⟩ (unchangedMask op)
  let wrong := failureIs (logicalUpdate op after 12 ⟨0⟩ 0) .wrongActor
  let busy := failureIs (retire after 7 ⟨0⟩) .liveHandles
  let closed ← close after 11 ⟨0⟩
  let oldHandle := failureIs (logicalUpdate op closed 11 ⟨0⟩ 0) .missingHandle
  let neighbor := failureIs (mutate closed (.store64 7 ⟨0, 0⟩ 65544 0)) .reserved
  let retired ← retire closed 7 ⟨0⟩
  let (transferred, _) ← mutate retired (.transfer 7 ⟨0, 0⟩ 7)
  let stale := failureIs (enroll transferred 7 ⟨0, 0⟩ 65536) (.ownership .staleEpoch)
  let (registeredAgain, newCell) ← enroll transferred 7 ⟨0, 1⟩ 65536
  let (renewed, newHandle) ← issue registeredAgain 7 newCell 11
  let oldCell := failureIs (issue renewed 7 ⟨0⟩ 12) .missingCell
  let revoked := failureIs (logicalUpdate op renewed 11 ⟨0⟩ 0) .missingHandle
  let _ ← logicalUpdate op renewed 11 newHandle (unchangedMask op)
  return (event, [wrong, busy, oldHandle, neighbor, stale, oldCell, revoked])

example : noChangeAndLifetime .band = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, ⟨.band, 0xffffffffffffffff,
      ⟨65536, 0x8000000000000001, 0x8000000000000001⟩⟩⟩,
      [true, true, true, true, true, true, true]) := by rfl
example : noChangeAndLifetime .bxor = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, ⟨.bxor, 0, ⟨65536, 0x8000000000000001, 0x8000000000000001⟩⟩⟩,
      [true, true, true, true, true, true, true]) := by rfl

/-- Stale authorization is rejected at the RMW itself, not merely enrollment.
This explicitly hostile legacy transition bypasses the managed reservation. -/
def staleCurrentEpoch (op : Sequential.LogicalOp) : Except Fault Bool := do
  let state := live 0x8000000000000001
  let (changed, _) ← (OS.Atomics.mutate state.legacy (.transfer 7 ⟨0, 0⟩ 7)).mapError Fault.legacy
  return failureIs (logicalUpdate op { state with legacy := changed } 11 ⟨0⟩ 0) (.ownership .staleEpoch)

example : [.band, .bor, .bxor].map staleCurrentEpoch = [.ok true, .ok true, .ok true] := by rfl

/-- A loan on a distinct allocation remains readable through an AND update;
after the loan ends, that allocation can become a second atomic cell. XOR on
the second cell and OR on the first retain each other's actual current bytes. -/
def loansAndIndependentCells : Except Fault
    (Except OS.Borrowing.ReadFault Word × Except Error Word × Except Error Word) := do
  let (resources, output) ← mutate (live 0x800000000000000f) (.allocate 8 ⟨131072, 8⟩ readWrite)
  let ticket ← match output with
    | some ticket => pure ticket
    | none => throw .missingCell
  let (written, _) ← mutate resources (.store64 8 ticket 131072 0x87654321fedcba98)
  let (loaned, loan) ← readBorrow written 8 ticket 22 ⟨131072, 8⟩
  let (changed, _) ← logicalUpdate .band loaned 11 ⟨0⟩ 0xfffffffffffffff0
  let retained := OS.Borrowing.loadWord64 changed.legacy.shared 22 loan 131072
  let ended ← finishLoan changed 22 loan
  let (otherRegistered, cell) ← enroll ended 8 ticket 131072
  let (both, handle) ← issue otherRegistered 8 cell 12
  let (otherChanged, _) ← logicalUpdate .bxor both 12 handle 0xffff0000000000ff
  let (last, _) ← logicalUpdate .bor otherChanged 11 ⟨0⟩ 1
  let memory := toMemory last.legacy.shared.resources.space
  return (retained, loadQWord memory 65536, loadQWord memory 131072)

example : loansAndIndependentCells = .ok
    (.ok 0x87654321fedcba98, .ok 0x8000000000000001, .ok 0x789a4321fedcba67) := by rfl

end EDSL.Tests.Atomics64Logical

#audit_edsl
#print axioms EDSL.Tests.Atomics64Logical.every_operation_old_and_mask
#print axioms EDSL.OS.Atomics64.logicalUpdate_primitive
#print axioms EDSL.OS.Atomics64.logicalUpdate_enabled
#print axioms EDSL.OS.Atomics64.logicalUpdate_loan_contents
#print axioms EDSL.OS.Atomics64.logicalUpdate_preserves_other
