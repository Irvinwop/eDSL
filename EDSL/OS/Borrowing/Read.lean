/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Borrowing.Read.Core
import EDSL.Examples.Compiler.MemoryOps

namespace EDSL.OS.Borrowing
open X86 AddressSpace

/-- Successful logical authority is composed with the actual 8b 07 c3 bytes.
Code and caller stack are premises at the execution state. -/
theorem borrowed_load32_correct (state : State) (borrower identifier : Nat)
    (initial : X86.State) (value : BitVec 32) (returnAddress : Word)
    (valid : WellFormed state)
    (success : loadWord state borrower identifier (initial.registers .rdi) = .ok value)
    (code : CodeAt (toMemory state.resources.space) initial.rip Examples.Compiler.MemoryOps.loadBytes)
    (stack : readWord (toMemory state.resources.space) (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    let entry := { initial with memory := toMemory state.resources.space }
    (∃ loan, authorize state borrower identifier = .ok loan ∧ ValidLoan state.resources loan) ∧
    Executes entry (Examples.Compiler.MemoryOps.loadFinal entry value returnAddress) 2 ∧
    ¬ Diverges entry ∧ ∀ final count, Executes entry final count →
      final = Examples.Compiler.MemoryOps.loadFinal entry value returnAddress ∧ count = 2 := by
  obtain ⟨loan, authorized, _, observed⟩ := loadWord_ok _ _ _ _ _ success
  have live := (authorize_ok _ _ _ _ authorized).1
  exact ⟨⟨loan, authorized, (valid.2 _ _ live).2⟩,
    Examples.Compiler.MemoryOps.load_correct _ value returnAddress code observed stack returnValid⟩

/-- Stable borrowed data composes with actual code after arbitrary guarded
resource histories. Code/stack binding is still checked at the final entry. -/
theorem borrowed_load32_after_history {before after : State} (history : History before after)
    (borrower identifier : Nat) (initial : X86.State) (value : BitVec 32) (returnAddress : Word)
    (valid : WellFormed before)
    (success : loadWord before borrower identifier (initial.registers .rdi) = .ok value)
    (survives : (after.loans identifier).isSome = true)
    (code : CodeAt (toMemory after.resources.space) initial.rip Examples.Compiler.MemoryOps.loadBytes)
    (stack : readWord (toMemory after.resources.space) (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    let entry := { initial with memory := toMemory after.resources.space }
    (∃ loan, authorize after borrower identifier = .ok loan ∧ ValidLoan after.resources loan) ∧
    Executes entry (Examples.Compiler.MemoryOps.loadFinal entry value returnAddress) 2 ∧
    ¬ Diverges entry ∧ ∀ final count, Executes entry final count →
      final = Examples.Compiler.MemoryOps.loadFinal entry value returnAddress ∧ count = 2 :=
  borrowed_load32_correct after borrower identifier initial value returnAddress
    (history.wellFormed valid)
    (history.loadWord_stable valid borrower identifier _ value success survives) code stack returnValid

end EDSL.OS.Borrowing
