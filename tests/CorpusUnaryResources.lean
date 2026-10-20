/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.UnaryCertificates
import EDSL.OS.Borrowing.History

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.CorpusUnaryResources
open X86 X86.Sequential OS Corpus.V1
open UnaryCertificates

private theorem certificate_semantics (compiler : Compiler) (operation : Operation) :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask (spec operation)) (bytes compiler operation) := by
  have claim := (certificate compiler operation).claim.1
  change Grading.SemanticClaim (Grading.registered (taskID operation)) (bytes compiler operation) at claim
  rw [registration operation] at claim
  exact (Grading.old_semanticClaim_iff _ _).mp claim

private def other : Operation → Operation
  | .absSigned32 => .byteSwap64
  | .byteSwap64 => .absSigned32

/-- Another authentic symbol in the same complete file remains the wrong
requested name. The production uniqueness theorem distinguishes the rows. -/
theorem wrong_name_rejected (compiler : Compiler) (operation : Operation) :
    (input compiler operation).check (file compiler) (name (other operation)) = false := by
  cases accepted : (input compiler operation).check (file compiler) (name (other operation)) with
  | false => rfl
  | true =>
    have wrong := (ELF.FunctionSymbol.checked_sound accepted).2.1.2.2.1
    have original := (ELF.FunctionSymbol.checked_sound
      (UnaryWindows.checked compiler (other operation))).2.1.2.2.1
    change (input compiler operation).metadata.matches (name (other operation)) =
      [(UnaryWindows.function compiler (other operation)).occurrence] at original
    have same := List.singleton_inj.mp (original.symm.trans wrong)
    have index := congrArg ELF.FunctionSymbol.Occurrence.index same
    have different : (UnaryWindows.function compiler (other operation)).occurrence.index ≠
        (UnaryWindows.function compiler operation).occurrence.index := by
      cases compiler <;> cases operation <;> decide +kernel
    exact False.elim (different index)

/-- Even an executable prefix cannot replace a complete declared extent.
This covers every shorter/longer candidate using the checker's mapping rule. -/
theorem wrong_extent_rejected (compiler : Compiler) (operation : Operation)
    (candidate : List Byte) (different : candidate.length ≠ (bytes compiler operation).length) :
    ({ input compiler operation with bytes := candidate } : Corpus.FunctionInput).check
      (file compiler) (name operation) = false := by
  cases accepted : ({ input compiler operation with bytes := candidate } : Corpus.FunctionInput).check
      (file compiler) (name operation) with
  | false => rfl
  | true =>
    have original := (ELF.FunctionSymbol.checked_mapping (UnaryWindows.checked compiler operation)).2.1
    have wrong := (ELF.FunctionSymbol.checked_mapping accepted).2.1
    exact False.elim (different (wrong.symm.trans original))

/-- Replacing RET by NOP preserves the extent but cannot borrow the original
file binding. The checker must compare bytes, not just metadata and length. -/
theorem wrong_text_rejected (compiler : Compiler) (operation : Operation) :
    ({ input compiler operation with bytes := (bytes compiler operation).dropLast ++ [0x90] } :
      Corpus.FunctionInput).check (file compiler) (name operation) = false := by
  let candidate := (bytes compiler operation).dropLast ++ [0x90]
  have length : candidate.length = (bytes compiler operation).length := by
    cases compiler <;> cases operation <;> decide +kernel
  have different : candidate ≠ bytes compiler operation := by
    cases compiler <;> cases operation <;> decide +kernel
  cases accepted : ({ input compiler operation with bytes := candidate } : Corpus.FunctionInput).check
      (file compiler) (name operation) with
  | false => rfl
  | true =>
    have original := (ELF.FunctionSymbol.checked_sound (UnaryWindows.checked compiler operation)).2.2.2.source
    have wrong := (ELF.FunctionSymbol.checked_sound accepted).2.2.2.source
    change ((file compiler).drop (UnaryWindows.function compiler operation).window.offset).take
      candidate.length = candidate at wrong
    rw [length] at wrong
    exact False.elim (different (wrong.symm.trans original))

def shifted (compiler : Compiler) (operation : Operation) : Corpus.FunctionInput :=
  { input compiler operation with function :=
    { UnaryWindows.function compiler operation with window :=
      { (UnaryWindows.function compiler operation).window with address :=
        (UnaryWindows.function compiler operation).window.address + 1 } } }

/-- Correct bytes/name/file do not authenticate a displaced selected entry. -/
theorem wrong_address_rejected (compiler : Compiler) (operation : Operation) :
    (shifted compiler operation).check (file compiler) (name operation) = false := by
  cases accepted : (shifted compiler operation).check (file compiler) (name operation) with
  | false => rfl
  | true =>
    have original := (ELF.FunctionSymbol.checked_mapping (UnaryWindows.checked compiler operation)).1
    change (UnaryWindows.function compiler operation).window.address =
      (UnaryWindows.function compiler operation).occurrence.symbol.value at original
    have wrong := (ELF.FunctionSymbol.checked_mapping accepted).1
    change (UnaryWindows.function compiler operation).window.address + 1 =
      (UnaryWindows.function compiler operation).occurrence.symbol.value at wrong
    omega

/-- A changed RAM byte at any selected position cannot satisfy current
admission, even if the original file admission and loan IDs are retained. -/
theorem changed_current_text_rejected (compiler : Compiler) (operation : Operation)
    (memory : Memory) (index : Nat) (byte : Byte)
    (present : (bytes compiler operation)[index]? = some byte)
    (changed : fetchByte memory ((environment compiler operation).code + BitVec.ofNat 64 index) ≠ .ok byte) :
    ¬ PureCall.ResourcePre (spec operation) (bytes compiler operation)
      (resource compiler operation (usefulValue operation))
      { initial compiler operation (usefulValue operation) with memory := memory } := by
  intro admitted
  exact changed (admitted.machine.code.2 index byte present)

/-- Execute permission is a current requirement independently of byte
equality. An NX entry cannot reuse stale complete-file admission. -/
theorem current_permission_rejected (compiler : Compiler) (operation : Operation)
    (memory : Memory) (denied : memory.executable (environment compiler operation).code = false) :
    ¬ PureCall.ResourcePre (spec operation) (bytes compiler operation)
      (resource compiler operation (usefulValue operation))
      { initial compiler operation (usefulValue operation) with memory := memory } := by
  have nonempty : ∃ byte, (bytes compiler operation)[0]? = some byte := by
    cases compiler <;> cases operation <;> exact ⟨_, rfl⟩
  obtain ⟨byte, present⟩ := nonempty
  apply changed_current_text_rejected compiler operation memory 0 byte present
  simp [fetchByte, denied]

def ended (compiler : Compiler) (operation : Operation) : Borrowing.State :=
  let current := resource compiler operation (usefulValue operation)
  { current.shared with loans := fun query =>
    if query = current.call.stackLoan then none else current.shared.loans query }

/-- A real finishLoan transition leaves RAM, permissions, owners and epochs
unchanged but rejects the call. Revocation remains effective through every
subsequent admitted resource history, even if fresh loans are issued. -/
theorem finished_loan_rejected (compiler : Compiler) (operation : Operation) :
    let current := resource compiler operation (usefulValue operation)
    Borrowing.finishLoan current.shared (Threads.principal current.call.worker)
      current.call.stackLoan = .ok (ended compiler operation) ∧
    (ended compiler operation).resources = current.shared.resources ∧
    ∀ after, Borrowing.History (ended compiler operation) after →
      ¬ PureCall.ResourcePre (spec operation) (bytes compiler operation)
        { current with shared := after } (initial compiler operation (usefulValue operation)) := by
  dsimp only
  let current := resource compiler operation (usefulValue operation)
  have valid := (pre compiler operation (usefulValue operation) (useful_domain operation)).current.contract
  obtain ⟨loan, live, borrower, _⟩ := valid.stackLoan
  have finished : Borrowing.finishLoan current.shared (Threads.principal current.call.worker)
      current.call.stackLoan = .ok (ended compiler operation) := by
    simp [Borrowing.finishLoan, Borrowing.authorize, current, live, borrower, ended]
  refine ⟨finished, rfl, ?_⟩
  intro after history admitted
  have revoked := Borrowing.finished_for_history _ _ valid.wellFormed finished history
  obtain ⟨_, stillLive, _, _⟩ := admitted.current.contract.stackLoan
  rw [revoked.2] at stillLive
  cases stillLive

/-- The result is forced by the independent integer square-root relation,
at the actual ELF address with useful current loans, for every AF stream. -/
theorem actual_absolute_result (compiler : Compiler) :
    AllExecutions (initial compiler .absSigned32 (0xffffffff : BitVec 32)) (fun result =>
      (result.state.registers .rax).setWidth 32 = (1 : BitVec 32) ∧
      result.state.rip = caller.returnAddress ∧
      CallResources.Current (resource compiler .absSigned32 (0xffffffff : BitVec 32)).call
        (resource compiler .absSigned32 (0xffffffff : BitVec 32)).shared result.state) := by
  have semantic := (certificate_semantics compiler .absSigned32).resource _ _
    (pre compiler .absSigned32 (0xffffffff : BitVec 32) (useful_domain .absSigned32))
  intro choices
  obtain ⟨result, execution, post, current⟩ := semantic.1 choices
  refine ⟨result, execution, ?_, post.returnAddress, current⟩
  apply BitVec.eq_of_toInt_eq
  exact WordMath.absSquare_unique post.result (by
    change (0 : Int) ≤ 1 ∧ (1 : Int) * 1 = (-1 : Int) * (-1)
    decide +kernel)

/-- Byte digit reversal independently fixes the literal full64 output. -/
theorem actual_swap_result (compiler : Compiler) :
    AllExecutions (initial compiler .byteSwap64 (1 : Word)) (fun result =>
      result.state.registers .rax = 0x0100000000000000 ∧
      result.state.rip = caller.returnAddress ∧
      CallResources.Current (resource compiler .byteSwap64 (1 : Word)).call
        (resource compiler .byteSwap64 (1 : Word)).shared result.state) := by
  have expected : WordMath.ByteReverse64 1 0x0100000000000000 := by
    intro index bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
    rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have semantic := (certificate_semantics compiler .byteSwap64).resource _ _
    (pre compiler .byteSwap64 (1 : Word) trivial)
  intro choices
  obtain ⟨result, execution, post, current⟩ := semantic.1 choices
  exact ⟨result, execution, WordMath.byteReverse64_unique post.result expected,
    post.returnAddress, current⟩

#print axioms wrong_name_rejected
#print axioms wrong_extent_rejected
#print axioms wrong_text_rejected
#print axioms wrong_address_rejected
#print axioms changed_current_text_rejected
#print axioms current_permission_rejected
#print axioms finished_loan_rejected
#print axioms actual_absolute_result
#print axioms actual_swap_result
end EDSL.Tests.CorpusUnaryResources
#audit_edsl
