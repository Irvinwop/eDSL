/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Completion.Core
import EDSL.OS.Futex.Predicate.Guards

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate.Completion
open X86

/-- Construct the actual ordinary instruction successor and check its action
bound. LOAD reads current one; historical zero comparisons still follow the
entire WAIT body. No future execution result is an input. -/
theorem ordinary_reduction {address : Word} {client : Client} {point : Point}
    {context : Threads.Context} {memory : Memory}
    (current : Running client point context) (ready : Ready client point memory)
    (wordAddress : client.entry.registers .rdi = address)
    (published : loadDWord memory address = .ok 1)
    (notCall : point ≠ .syscall) (notReturn : ∀ observed, point ≠ .done observed) :
    ∃ next after, executeInstruction (MachineThreads.contextState context memory) point.instruction =
      .ok (.next (MachineThreads.contextState after memory)) ∧
      Running client next after ∧ remaining next + 1 ≤ remaining point := by
  cases point with
  | load =>
    exact ⟨.compare 1, context.loaded 1,
      execute_load context memory 1 (by rw [current.rdi, wordAddress]; exact published),
      current.load_next 1, by decide⟩
  | compare observed =>
    refine ⟨.branch observed, cmpContext context, execute_cmp .., current.compare_next, ?_⟩
    simp only [remaining]
    split <;> decide
  | branch observed =>
    by_cases zero : observed = 0
    · subst observed
      have zf : context.flags.getLsbD 6 = true := by simpa using current.fields.2
      exact ⟨.number, branchContext context (context.rip + 2),
        execute_jnz_fallthrough context memory 0x16 zf, current.branch_zero, by decide⟩
    · have zf : context.flags.getLsbD 6 = false := by
        simpa only [beq_eq_false_iff_ne.mpr zero] using current.fields.2
      have executed := execute_jnz_taken context memory 0x16 zf
        (by rw [branch_done_target current]; exact ready zero)
      rw [branch_done_target current] at executed
      exact ⟨.done observed, branchContext context (client.entry.rip + 29),
        executed, current.branch_nonzero zero, by simp only [remaining, ite_eq_right zero]; decide⟩
  | number =>
    exact ⟨.operation, movContext context .rax 202, execute_mov .., current.number_next, by decide⟩
  | operation =>
    exact ⟨.syscall, movContext context .rsi 128, execute_mov .., current.operation_next, by decide⟩
  | syscall => exact (notCall rfl).elim
  | resumed raw =>
    exact ⟨.retryCompare, movContext context .rax 1, execute_mov .., current.resumed_next,
      by simp only [remaining]; decide⟩
  | retryCompare =>
    exact ⟨.retryBranch, cmpContext context, execute_cmp .., current.retryCompare_next, by decide⟩
  | retryBranch =>
    have executed := execute_jnz_taken context memory 0xe3 current.fields.2.2
      (by rw [branch_retry_target current]; exact ready)
    rw [branch_retry_target current] at executed
    exact ⟨.load, branchContext context client.entry.rip, executed, current.retryBranch_next, by decide⟩
  | done observed => exact (notReturn observed rfl).elim

/-- The exact decoded ordinary issue reaches that smaller cut while retaining
all physical RAM and every peer record/pending invocation. -/
theorem ordinary_issue {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} {point : Point} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (running : RunningAt client worker state.suspended point)
    (notCall : point ≠ .syscall) (notReturn : ∀ observed, point ≠ .done observed) :
    ∃ next context,
      Suspend.issue state.suspended worker =
        .ok (retire state.suspended worker context, .machine (.retired worker none)) ∧
      RunningAt client worker (retire state.suspended worker context) next ∧
      remaining next + 1 ≤ remaining point ∧
      PrivateFrame worker state.suspended (retire state.suspended worker context) := by
  obtain ⟨actual, found, current, live, free, empty⟩ := running
  have ready := admitted.loop_ready member point
  obtain ⟨next, context, executed, nextCurrent, bound⟩ := ordinary_reduction current ready
    (admitted.static.descriptors worker (.waitLoop client) member).1 published notCall notReturn
  exact ⟨next, context, issue_next found current live free empty
      (admitted.protected worker (.waitLoop client) member).2.2.1 ready notCall executed,
    ⟨⟨context, false, []⟩, retire_selected found context, nextCurrent, rfl, free, rfl⟩,
    bound, rfl, fun _ different => ⟨retire_peer different, rfl⟩⟩

end EDSL.OS.Futex.Predicate.Completion

#audit_edsl
