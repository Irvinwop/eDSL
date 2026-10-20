/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicLogical64.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.AtomicLogical64Domain
open EDSL X86 OS OS.AddressSpace EDSL.AtomicLogical64
open EDSL.Grading.AtomicLogical64.Domain

def duplicateOr : List Byte := [0xf0, 0x48, 0x09, 0x37, 0xf0, 0x48, 0x09, 0x37, 0xc3]

/-- An unsupported instruction has the same full current-resource admission
and arbitrary full64 inputs as executable candidates. The machine rejects
the bytes when it actually attempts decoding. -/
theorem unsupported_current (old mask : Word) (af : Bool) :
    Pre [0xff] input (shared [0xff] old) (initial [0xff] old mask) ∧
      loadQWord (initial [0xff] old mask).memory 65536 = .ok old ∧
      LockedLogical64.step af (initial [0xff] old mask) = .error .unsupportedEncoding := by
  have pre := resource_pre [0xff] (by decide) (by decide) old mask
  have first := pre.code.2 0 0xff rfl
  simp only [BitVec.add_zero] at first
  refine ⟨pre, old_read _ (by decide) old mask, ?_⟩
  rw [LockedLogical64.step, LockedLogical64.decodeAt, first]
  rfl

def retFinal (old mask : Word) : X86.State :=
  { (initial [0xc3] old mask).writeRegister .rsp 32776 with rip := 8192 }

/-- RET-only code is admitted for arbitrary old/mask values, actually returns
through the original caller word, and leaves the target word unchanged. -/
theorem ret_current (old mask : Word) (af : Bool) :
    Pre [0xc3] input (shared [0xc3] old) (initial [0xc3] old mask) ∧
      LockedLogical64.step af (initial [0xc3] old mask) =
        .ok ⟨.returned (retFinal old mask), [.stack8 32768]⟩ ∧
      loadQWord (retFinal old mask).memory 65536 = .ok old := by
  have pre := resource_pre [0xc3] (by decide) (by decide) old mask
  refine ⟨pre, ?_, old_read [0xc3] (by decide) old mask⟩
  rw [LockedLogical64.step_eq_execute af (LockedLogical64.decodeAt_of_code .ret pre.code)]
  exact LockedLogical64.execute_ret_context _ _ af pre.stack pre.returnCanonical

/-- These three spans all have a genuinely requested missing bit. Admission
therefore cannot hide unsupported or incorrect programs behind empty inputs. -/
theorem useful_spans :
    (∃ old mask world cpu, Pre [0xff] input world cpu ∧
      loadQWord cpu.memory (cpu.registers .rdi) = .ok old ∧ cpu.registers .rsi = mask ∧
        Useful old mask) ∧
    (∃ old mask world cpu, Pre [0xc3] input world cpu ∧
      loadQWord cpu.memory (cpu.registers .rdi) = .ok old ∧ cpu.registers .rsi = mask ∧
        Useful old mask) ∧
    (∃ old mask world cpu, Pre duplicateOr input world cpu ∧
      loadQWord cpu.memory (cpu.registers .rdi) = .ok old ∧ cpu.registers .rsi = mask ∧
        Useful old mask) :=
  ⟨useful_current _ (by decide) (by decide), useful_current _ (by decide) (by decide),
    useful_current _ (by decide) (by decide)⟩

/-- The longer span installs both instruction starts and its final RET. These
are actual fetches from current RX cells, independent of future execution. -/
theorem duplicate_current (old mask : Word) :
    Pre duplicateOr input (shared duplicateOr old) (initial duplicateOr old mask) ∧
      loadQWord (initial duplicateOr old mask).memory 65536 = .ok old ∧
      fetchByte (initial duplicateOr old mask).memory 4100 = .ok 0xf0 ∧
      fetchByte (initial duplicateOr old mask).memory 4104 = .ok 0xc3 := by
  have pre := resource_pre duplicateOr (by decide) (by decide) old mask
  exact ⟨pre, old_read _ (by decide) old mask,
    pre.code.2 4 0xf0 rfl, pre.code.2 8 0xc3 rfl⟩

/-- For every admitted byte span, the checked handle operation reads the
symbolic old word and the requested full64 mask. It retains actual code and
caller cells, even when the candidate itself is not executable. -/
theorem current_rmw (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old mask : Word) :
    ∃ result, Atomics64.logicalDiscard (shared candidate old) 11 ⟨0⟩ mask = .ok result ∧
      result.2.logical.event.before = old ∧ result.2.logical.mask = mask ∧
      LoanAt result.1 11 0 (codeRegion candidate) ∧ LoanAt result.1 11 1 callerRegion ∧
      (∀ address, (codeRegion candidate).Contains address →
        result.1.legacy.shared.resources.space.cells address =
          (shared candidate old).legacy.shared.resources.space.cells address) ∧
      (∀ address, callerRegion.Contains address →
        result.1.legacy.shared.resources.space.cells address =
          (shared candidate old).legacy.shared.resources.space.cells address) := by
  have pre := resource_pre candidate positive bound old mask
  obtain ⟨handle, cell, authorized, pointer⟩ := pre.authority
  obtain ⟨result, success⟩ := Atomics64.logicalDiscard_enabled _ _ _ mask handle cell pre.valid authorized
  have identity := Atomics64.logicalDiscard_identity _ _ _ _ _ _ _ success authorized
  have sound := Atomics64.logicalDiscard_sound _ _ _ _ _ success
  have read := sound.1.2.2.1
  rw [identity.2, ← pointer] at read
  have same : result.2.logical.event.before = old :=
    Except.ok.inj (read.symm.trans (old_read candidate bound old mask))
  have effect := Atomics64.logicalDiscard_effect _ _ _ _ _ success
  have codeLive : (shared candidate old).legacy.shared.loans 0 =
      some ⟨⟨2, 0⟩, 0, 11, codeRegion candidate⟩ := rfl
  have callerLive : (shared candidate old).legacy.shared.loans 1 =
      some ⟨⟨1, 0⟩, 0, 11, callerRegion⟩ := rfl
  exact ⟨result, success, same, sound.2.2.1,
    ⟨_, (congrFun effect.shared.loans 0).trans codeLive, rfl, rfl⟩,
    ⟨_, (congrFun effect.shared.loans 1).trans callerLive, rfl, rfl⟩,
    Atomics64.logicalDiscard_loan_contents _ _ _ _ _ pre.valid success 0 _ codeLive,
    Atomics64.logicalDiscard_loan_contents _ _ _ _ _ pre.valid success 1 _ callerLive⟩

/-- Independent little-endian observations after a real authorized high-bit
RMW on an unsupported candidate. Neighbor, code and caller reads catch address,
width, byte-order and frame regressions. -/
def highbitObservation : Except Atomics64.Fault
    (Word × List (Option Byte) × Except X86.Error Word × Except X86.Error Byte × Except X86.Error Word) := do
  let result ← Atomics64.logicalDiscard (shared [0xff] 0) 11 ⟨0⟩ 0x8000000000000000
  let memory := toMemory result.1.legacy.shared.resources.space
  return (result.2.logical.event.before,
    [memory.read 65536, memory.read 65537, memory.read 65538, memory.read 65539,
      memory.read 65540, memory.read 65541, memory.read 65542, memory.read 65543],
    loadQWord memory 65544, fetchByte memory 4096, readWord memory 32768)

theorem highbit_observed : highbitObservation = .ok (0,
    [some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 0x80],
    .ok 0x1122334455667788, .ok 0xff, .ok 8192) := by rfl

/-- The maximum protocol window is constructed symbolically: its last byte
is installed, and the byte just past the extent remains inaccessible. -/
theorem maximum_window (old mask : Word) :
    Pre (List.replicate 4096 0xff) input (shared (List.replicate 4096 0xff) old)
      (initial (List.replicate 4096 0xff) old mask) ∧
    fetchByte (initial (List.replicate 4096 0xff) old mask).memory 8191 = .ok 0xff ∧
    fetchByte (initial (List.replicate 4096 0xff) old mask).memory 8192 =
      .error (.inaccessibleInstruction 8192) := by
  have positive : 0 < (List.replicate 4096 (0xff : Byte)).length := by
    simp only [List.length_replicate]; decide
  have bound : (List.replicate 4096 (0xff : Byte)).length ≤ 4096 := by
    simp only [List.length_replicate, Nat.le_refl]
  have pre := resource_pre _ positive bound old mask
  refine ⟨pre, pre.code.2 4095 0xff (List.getElem?_replicate_of_lt (by decide)), ?_⟩
  change fetchByte (toMemory (loaded (List.replicate 4096 0xff) old).space) 8192 = _
  have absent := loaded_far (List.replicate 4096 0xff) bound old 8192 (by decide)
  have executable : (toMemory (loaded (List.replicate 4096 0xff) old).space).executable 8192 = false := by
    dsimp only [toMemory]; rw [absent]; rfl
  simp only [fetchByte, executable, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

def closed (candidate : List Byte) (old : Word) : Shared :=
  Atomics64.removeHandle (shared candidate old) ⟨0⟩

/-- Closing a live named handle is checked first. Reissuing authority to the
same actor/cell cannot revive the old typed identity. -/
theorem closed_handle (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old mask : Word) :
    Atomics64.close (shared candidate old) 11 ⟨0⟩ = .ok (closed candidate old) ∧
      ∃ renewed, Atomics64.issue (closed candidate old) 0 ⟨0⟩ 11 = .ok (renewed, ⟨1⟩) ∧
        Atomics64.logicalDiscard renewed 11 ⟨0⟩ mask = .error .missingHandle := by
  have valid := shared_valid candidate positive bound old
  have authorized := Atomics64.authorize_success (shared candidate old) 11 ⟨0⟩
    ⟨11, ⟨0⟩⟩ ⟨0, ⟨0, 0⟩, 65536⟩ valid rfl rfl rfl
  have close : Atomics64.close (shared candidate old) 11 ⟨0⟩ = .ok (closed candidate old) := by
    simp [Atomics64.close, authorized, closed]
  have closedValid := Atomics64.close_wellFormed _ _ _ _ valid close
  have issue := Atomics64.issue_success (closed candidate old) 0 ⟨0⟩ 11
    ⟨0, ⟨0, 0⟩, 65536⟩ closedValid rfl rfl
  have revoked := Atomics64.close_revokes _ _ _ _ valid close
  exact ⟨close, _, issue, (revoked.persists (Atomics64.issue_advances _ _ _ _ _ issue)).logicalDiscard_denied 11 mask⟩

def codeFinished (candidate : List Byte) (old : Word) : Shared :=
  { shared candidate old with
    legacy := { (shared candidate old).legacy with
      shared := { (shared candidate old).legacy.shared with
        loans := fun query => if query = 0 then none else (shared candidate old).legacy.shared.loans query } } }

/-- Finishing a real code loan makes its read action fail; the independent
caller loan still reads all eight initialized return-address bytes. -/
theorem finished_loan (candidate : List Byte) (bound : candidate.length ≤ 4096) (old mask : Word) :
    Atomics64.finishLoan (shared candidate old) 11 0 = .ok (codeFinished candidate old) ∧
      Borrowing.loadWord64 (codeFinished candidate old).legacy.shared 11 0 4096 =
        .error (.authority .missingLoan) ∧
      Borrowing.loadWord64 (codeFinished candidate old).legacy.shared 11 1 32768 = .ok 8192 := by
  refine ⟨rfl, rfl, ?_⟩
  apply Borrowing.loadWord64_success _ _ _ _ _ ⟨⟨1, 0⟩, 0, 11, callerRegion⟩ rfl ⟨by decide, by decide⟩
  exact loadQWord_of_readWord _ _ _ (caller_read candidate bound old mask (fun _ => 0) 0)

private def failureIs (result : Except Atomics64.Fault α) (expected : Atomics64.Fault) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

/-- A same-owner transfer really increments the epoch after close+retire.
The stale ticket fails enrollment; the new ticket enrolls the same address. -/
def epochLifecycle (old : Word) : Except Atomics64.Fault Bool := do
  let noHandle ← Atomics64.close (shared [0xff] old) 11 ⟨0⟩
  let retired ← Atomics64.retire noHandle 0 ⟨0⟩
  let (transferred, ticket) ← Atomics64.mutate retired (.transfer 0 ⟨0, 0⟩ 0)
  let stale := failureIs (Atomics64.enroll transferred 0 ⟨0, 0⟩ 65536) (.ownership .staleEpoch)
  match ticket with
  | none => return false
  | some current =>
    let (renewed, _) ← Atomics64.enroll transferred 0 current 65536
    return stale && failureIs (Atomics64.issue renewed 0 ⟨0⟩ 11) .missingCell

private def retired (old : Word) : Shared := Atomics64.removeCell (closed [0xff] old) ⟨0⟩

private theorem retired_checked (old : Word) :
    Atomics64.retire (closed [0xff] old) 0 ⟨0⟩ = .ok (retired old) := by
  have close := (closed_handle [0xff] (by decide) (by decide) old 0).1
  have valid := Atomics64.close_wellFormed _ _ _ _ (shared_valid [0xff] (by decide) (by decide) old) close
  have authorized := Atomics64.authorizeCell_success (closed [0xff] old) 0 ⟨0⟩
    ⟨0, ⟨0, 0⟩, 65536⟩ valid rfl rfl
  have noHandles : Atomics64.hasHandles (closed [0xff] old) ⟨0⟩ = false := rfl
  rw [Atomics64.retire, authorized]
  simp only [ok_bind]
  rw [noHandles]
  rfl

private def transferred (old : Word) : Shared :=
  { retired old with
    legacy := { (retired old).legacy with
      shared := { (retired old).legacy.shared with
        resources := Ownership.replace (retired old).legacy.shared.resources 0
          (some ⟨0, 1, dataRegion⟩) } } }

private theorem transferred_checked (old : Word) :
    Atomics64.mutate (retired old) (.transfer 0 ⟨0, 0⟩ 0) =
      .ok (transferred old, some ⟨0, 1⟩) := by rfl

private theorem renewed_checked (old : Word) :
    Atomics64.enroll (transferred old) 0 ⟨0, 1⟩ 65536 =
      .ok (Atomics64.installCell (transferred old) ⟨0, ⟨0, 1⟩, 65536⟩, ⟨1⟩) := by
  have original := shared_valid [0xff] (by decide) (by decide) old
  have close := (closed_handle [0xff] (by decide) (by decide) old 0).1
  have closeValid := Atomics64.close_wellFormed _ _ _ _ original close
  have retiredValid := Atomics64.retire_wellFormed _ _ _ _ closeValid (retired_checked old)
  have valid := Atomics64.mutate_wellFormed _ _ _ retiredValid (transferred_checked old)
  have cell := (original.cells ⟨0⟩ ⟨0, ⟨0, 0⟩, 65536⟩ rfl).2
  have current : Atomics64.ValidCell (transferred old).legacy.shared ⟨0, ⟨0, 1⟩, 65536⟩ :=
    ⟨⟨⟨0, 1, dataRegion⟩, rfl, rfl, rfl, by decide, cell.1.writable⟩, cell.2.1, cell.2.2⟩
  exact Atomics64.enroll_success _ _ _ _ valid current rfl rfl rfl

theorem epoch_lifecycle (old : Word) : epochLifecycle old = .ok true := by
  unfold epochLifecycle
  rw [(closed_handle [0xff] (by decide) (by decide) old 0).1]
  simp only [ok_bind]
  rw [retired_checked old]
  simp only [ok_bind]
  rw [transferred_checked old]
  simp only [ok_bind]
  rw [renewed_checked old]
  rfl

/-- Reservation is allocation-wide, and both original live read loans block
ordinary mutation. These are real denied operations against the current setup. -/
theorem mutation_gates (candidate : List Byte) (old : Word) :
    Atomics64.mutate (shared candidate old) (.store64 0 ⟨0, 0⟩ 65544 0) = .error .reserved ∧
      Atomics64.readBorrow (shared candidate old) 0 ⟨0, 0⟩ 11 ⟨65544, 8⟩ = .error .reserved ∧
      Atomics64.mutate (shared candidate old) (.protect 0 ⟨2, 0⟩ readWrite) =
        .error (.legacy (.authority .borrowed)) ∧
      Atomics64.mutate (shared candidate old) (.release 0 ⟨1, 0⟩) =
        .error (.legacy (.authority .borrowed)) :=
  ⟨rfl, rfl, rfl, rfl⟩

end EDSL.Tests.AtomicLogical64Domain

#print axioms EDSL.Grading.AtomicLogical64.Domain.resource_pre
#print axioms EDSL.Grading.AtomicLogical64.Domain.arbitrary_current
#print axioms EDSL.Grading.AtomicLogical64.Domain.useful_current
#print axioms EDSL.Tests.AtomicLogical64Domain.unsupported_current
#print axioms EDSL.Tests.AtomicLogical64Domain.ret_current
#print axioms EDSL.Tests.AtomicLogical64Domain.current_rmw
#print axioms EDSL.Tests.AtomicLogical64Domain.highbit_observed
#print axioms EDSL.Tests.AtomicLogical64Domain.maximum_window
#print axioms EDSL.Tests.AtomicLogical64Domain.closed_handle
#print axioms EDSL.Tests.AtomicLogical64Domain.finished_loan
#print axioms EDSL.Tests.AtomicLogical64Domain.epoch_lifecycle
#audit_edsl
