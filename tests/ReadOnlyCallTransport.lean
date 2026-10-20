/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.ReadOnlyCallTransport
import EDSL.OS.CallResources.Domain

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ReadOnlyCallTransport
open X86 X86.Sequential OS OS.AddressSpace BufferCall
open Corpus.ReadOnlyCallTransport

-- Synthetic complete memory: two code extents, an original caller slot,
-- and an unrelated readable cell. Input spans alias the old executable code.
def supplied : Space where
  cells address := match address.toNat with
    | 4096 | 4097 | 4098 | 4099 => some ⟨0x90, readExecute⟩
    | 4100 | 8192 => some ⟨0xc3, readExecute⟩
    | 4101 | 4102 | 4103 => some ⟨0, readExecute⟩
    | 65545 => some ⟨0x30, readOnly⟩
    | 65544 | 65546 | 65547 | 65548 | 65549 | 65550 | 65551 => some ⟨0, readOnly⟩
    | 131072 => some ⟨0x5a, readOnly⟩
    | _ => none

def whole : Buffer := ⟨4096, [0x90, 0x90, 0x90, 0x90, 0xc3, 0, 0, 0]⟩
def suffix : Buffer := ⟨4100, [0xc3, 0, 0, 0]⟩

def declared : CallResources.Domain.Initial :=
  ⟨supplied, 7, 7, 10, 4096, whole.bytes, 65544, 12288⟩

theorem facts : CallResources.Domain.Facts declared :=
  CallResources.Domain.check_sound (by decide +kernel)

def overlapping : Borrowing.State := Borrowing.installLoan
  (CallResources.Domain.shared declared)
  ⟨CallResources.Domain.codeTicket, 7, Threads.principal 10, suffix.region⟩

theorem overlapping_valid : Borrowing.WellFormed overlapping :=
  (Borrowing.readBorrow_wellFormed _ 7 CallResources.Domain.codeTicket
    (Threads.principal 10) suffix.region (overlapping, 2)
    (CallResources.Domain.shared_valid facts) (by rfl)).1

def before : Corpus.BufferResources.Managed := ⟨overlapping, overlapping_valid⟩

def spec : Spec where
  Input := Word
  arguments base index := if index.val = 0 then some (.word64 base) else none
  buffers base := [whole, suffix, ⟨base, []⟩]
  domain _ := True
  result _ actual := actual = 7
  useful _ := True

def source (emptyBase : Word) (unused : Nat) : Resources spec :=
  ⟨before.shared, CallResources.Domain.call declared, emptyBase,
    fun buffer => if buffer = whole then 0 else if buffer = suffix then 2 else unused⟩

theorem source_contract (emptyBase : Word) (unused : Nat) :
    ResourceContract (source emptyBase unused) before.shared := by
  refine ⟨⟨before.valid, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
    facts.code, facts.stack, facts.returnCanonical, facts.stackBound,
    facts.postStackCanonical⟩, ?_, ?_⟩
  · intro buffer member
    have cases : buffer = whole ∨ buffer = suffix ∨ buffer = ⟨emptyBase, []⟩ := by
      simpa [spec, source] using member
    rcases cases with rfl | rfl | rfl
    · exact facts.code.readable
    · refine ⟨by decide +kernel, ?_⟩
      intro index byte present
      match index with
      | 0 | 1 | 2 | 3 => simp [suffix] at present; subst byte; rfl
      | index + 4 => simp [suffix] at present
    · exact Buffer.empty _ _
  · intro buffer member nonempty
    have cases : buffer = whole ∨ buffer = suffix ∨ buffer = ⟨emptyBase, []⟩ := by
      simpa [spec, source] using member
    rcases cases with rfl | rfl | rfl
    · exact ⟨_, rfl, rfl, rfl⟩
    · exact ⟨_, rfl, rfl, rfl⟩
    · exact False.elim (nonempty rfl)

def setup := Corpus.ReadOnlyCalls.attach before 7 10 ⟨8192, 1⟩ []

theorem setup_total : setup.toOption.isSome = true := by decide +kernel

def attached : Corpus.ReadOnlyCalls.Attached before 10 ⟨8192, 1⟩ [] :=
  setup.toOption.get setup_total

theorem new_code : CodeAt (toMemory before.shared.resources.space) 8192 [0xc3] :=
  checkCode_sound _ _ _ (by decide +kernel)

def updatedSpec : Spec := { spec with result := fun _ actual => actual = 0 }

def current (emptyBase : Word) (unused : Nat) : Resources updatedSpec :=
  resultView (retarget (source emptyBase unused) [0xc3] attached) (fun _ actual => actual = 0)

def machine (emptyBase : Word) : X86.State :=
  CallResources.Domain.machine declared
    (fun register => if register = .rdi then emptyBase else 0) 0x202

theorem source_pre (emptyBase : Word) (unused : Nat) :
    ResourcePre spec whole.bytes (source emptyBase unused) (machine emptyBase) := by
  refine ⟨⟨source_contract emptyBase unused, rfl⟩, rfl, rfl, ?_, True.intro, ?_⟩
  · rfl
  · intro index argument binding
    obtain ⟨index, bound⟩ := index
    match index with
    | 0 => simp [spec, source] at binding; subst argument; rfl
    | index + 1 => simp [spec] at binding

def newMachine (emptyBase : Word) : X86.State := { machine emptyBase with rip := 8192 }

/-- Both overlapping inputs and every empty pointer/unused ID survive the
code attachment and result-only change, including full-width RDI binding. -/
theorem current_pre (emptyBase : Word) (unused : Nat) :
    ResourcePre updatedSpec [0xc3] (current emptyBase unused) (newMachine emptyBase) :=
  (resultView_pre_iff (retarget (source emptyBase unused) [0xc3] attached)
    (fun _ actual => actual = 0) [0xc3] (newMachine emptyBase)).mpr
      (retarget_pre attached rfl (source_pre emptyBase unused) new_code)

/-- Evaluate the actual new RET and its original caller read. -/
theorem new_code_returns (emptyBase : Word) :
    ∃ final, step false (newMachine emptyBase) =
      .ok ⟨.returned final, [⟨.stack, 65544, 8⟩]⟩ ∧
      final.rip = 12288 ∧ final.registers .rsp = 65552 ∧
      final.memory = (newMachine emptyBase).memory := by
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- Independent literal read results exercise retained caller and both input
loans through the borrowing API; the caller owner still cannot overwrite it. -/
theorem retained_accesses (emptyBase : Word) (unused : Nat) :
    Borrowing.loadWord64 (current emptyBase unused).shared (Threads.principal 10) 1 65544 =
      .ok 12288 ∧
    Borrowing.loadWord64 (current emptyBase unused).shared (Threads.principal 10)
      ((current emptyBase unused).inputLoan whole) 4096 = .ok 0xc390909090 ∧
    Borrowing.loadWord (current emptyBase unused).shared (Threads.principal 10)
      ((current emptyBase unused).inputLoan suffix) 4100 = .ok 0xc3 ∧
    Borrowing.mutate (current emptyBase unused).shared
      (.store64 7 CallResources.Domain.stackTicket 65544 0) = .error .borrowed := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Unrelated readable RAM remains non-executable and outside the input loan. -/
theorem unrelated_access_denied (emptyBase : Word) (unused : Nat) :
    readDataByte (toMemory (current emptyBase unused).shared.resources.space) 131072 = .ok 0x5a ∧
    fetchByte (toMemory (current emptyBase unused).shared.resources.space) 131072 =
      .error (.inaccessibleInstruction 131072) ∧
    Borrowing.loadWord (current emptyBase unused).shared (Threads.principal 10)
      ((current emptyBase unused).inputLoan whole) 131072 = .error .outsideLoan := by
  exact ⟨rfl, rfl, rfl⟩

/-- Executable bytes do not authorize substituting the old code loan for the
new code extent, even though that old loan remains a valid input loan. -/
theorem stale_code_denied (emptyBase : Word) (unused : Nat) :
    ¬ ResourceContract
      { current emptyBase unused with call := { (current emptyBase unused).call with codeLoan := 0 } }
      (current emptyBase unused).shared := by
  intro admitted
  obtain ⟨loan, live, _, region⟩ := admitted.call.codeLoan
  have retained : Threads.HasLoan (current emptyBase unused).shared 10 0 ⟨4096, 8⟩ :=
    attached.original_loan (source_contract emptyBase unused).call.codeLoan
  obtain ⟨original, originalLive, _, originalRegion⟩ := retained
  have same : loan = original := Option.some.inj (live.symm.trans originalLive)
  rw [same] at region
  have impossible : (8192 : Word) = 4096 :=
    congrArg Region.base (region.symm.trans originalRegion)
  exact (by decide +kernel : (8192 : Word) ≠ 4096) impossible

/-- The old byte list cannot describe the actual new executable extent. -/
theorem stale_bytes_denied (emptyBase : Word) (unused : Nat) :
    ¬ ResourceContract
      { current emptyBase unused with call := { (current emptyBase unused).call with bytes := whole.bytes } }
      (current emptyBase unused).shared := by
  intro admitted
  have actual : fetchByte (toMemory (current emptyBase unused).shared.resources.space) 8192 =
      .ok 0xc3 := rfl
  have wrong := admitted.call.code.2 0 0x90 rfl
  have impossible : (0xc3 : Byte) = 0x90 := Except.ok.inj (actual.symm.trans wrong)
  exact (by decide +kernel : (0xc3 : Byte) ≠ 0x90) impossible

def ended (emptyBase : Word) (unused : Nat) : Borrowing.State :=
  { (current emptyBase unused).shared with loans := fun query =>
    if query = 2 then none else (current emptyBase unused).shared.loans query }

/-- Actual finishLoan leaves all bytes, permissions and allocations present.
The surviving larger input loan cannot replace the revoked exact suffix loan. -/
theorem revoked_input_denied (emptyBase : Word) (unused : Nat) :
    Borrowing.finishLoan (current emptyBase unused).shared (Threads.principal 10) 2 =
      .ok (ended emptyBase unused) ∧
    (ended emptyBase unused).resources = (current emptyBase unused).shared.resources ∧
    Borrowing.loadWord (ended emptyBase unused) (Threads.principal 10)
      ((current emptyBase unused).inputLoan whole) 4100 = .ok 0xc3 ∧
    Borrowing.loadWord (ended emptyBase unused) (Threads.principal 10) 2 4100 =
      .error (.authority .missingLoan) ∧
    ¬ ResourceContract (current emptyBase unused) (ended emptyBase unused) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro admitted
  obtain ⟨loan, live, _, _⟩ := admitted.inputs suffix
    (by simp [updatedSpec, spec, current, resultView, retarget, source]) (by decide +kernel)
  change none = some loan at live
  cases live

#print axioms facts
#print axioms overlapping_valid
#print axioms source_contract
#print axioms setup_total
#print axioms new_code
#print axioms source_pre
#print axioms current_pre
#print axioms new_code_returns
#print axioms retained_accesses
#print axioms unrelated_access_denied
#print axioms stale_code_denied
#print axioms stale_bytes_denied
#print axioms revoked_input_denied
end EDSL.Tests.ReadOnlyCallTransport
#audit_edsl
