import EDSL.OS.Futex.Predicate.Raw.Control
import EDSL.Audit

namespace EDSL.OS.Futex.Predicate
open X86

theorem retry_three_issues {client : Client} {state : Suspend.State} {worker : Nat}
    {before : TSO.Worker} {raw : Word}
    (atWorker : state.machine.workers[worker]? = some before)
    (current : Running client (.resumed raw) before.context) (live : before.returned = false)
    (free : state.pending worker = none) (empty : before.buffer = [])
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (canonical : X86.canonical client.entry.rip = true) :
    ∃ after selected,
      Suspend.schedule state [.issue worker, .issue worker, .issue worker] =
        .ok (after, [.machine (.retired worker none), .machine (.retired worker none),
          .machine (.retired worker none)]) ∧
      after.machine.workers[worker]? = some selected ∧
      selected.returned = false ∧ selected.buffer = [] ∧ after.pending worker = none ∧
      selected.context.rip = client.entry.rip ∧ selected.context.registers .rax = 1 ∧
      selected.context.registers .rsi = 128 ∧ Running client .load selected.context ∧
      after.machine.memory = state.machine.memory ∧
      (∀ peer, peer ≠ worker →
        after.machine.workers[peer]? = state.machine.workers[peer]? ∧
        after.pending peer = state.pending peer) := by
  let moved := movContext before.context .rax 1
  let first := retire state worker moved
  have movedControl : Running client .retryCompare moved := current.resumed_next
  have firstStep : Suspend.issue state worker = .ok (first, .machine (.retired worker none)) :=
    issue_next atWorker current live free empty code trivial (by intro impossible; cases impossible) (execute_mov ..)
  have firstAt : first.machine.workers[worker]? = some ⟨moved, false, []⟩ :=
    retire_selected atWorker moved
  let compared := cmpContext moved
  let second := retire first worker compared
  have comparedControl : Running client .retryBranch compared := movedControl.retryCompare_next
  have secondStep : Suspend.issue first worker = .ok (second, .machine (.retired worker none)) :=
    issue_next firstAt movedControl rfl free rfl code trivial (by decide) (execute_cmp ..)
  have secondAt : second.machine.workers[worker]? = some ⟨compared, false, []⟩ :=
    retire_selected firstAt compared
  let checked := branchContext compared client.entry.rip
  let third := retire second worker checked
  have checkedControl : Running client .load checked := comparedControl.retryBranch_next
  have branchStep := execute_jnz_taken compared state.machine.memory 0xe3 comparedControl.fields.2.2
    (by rw [branch_retry_target comparedControl]; exact canonical)
  rw [branch_retry_target comparedControl] at branchStep
  have thirdStep : Suspend.issue second worker = .ok (third, .machine (.retired worker none)) :=
    issue_next secondAt comparedControl rfl free rfl code canonical (by decide) branchStep
  refine ⟨third, ⟨checked, false, []⟩, ?_, retire_selected secondAt checked,
    rfl, rfl, free, rfl, ?_, ?_, checkedControl, rfl, ?_⟩
  · simp only [Suspend.schedule, Suspend.step, firstStep, secondStep, thirdStep, ok_bind]
    rfl
  · simp [checked, compared, moved, branchContext, cmpContext, movContext]
  · exact current.fields.2
  · intro peer different
    exact ⟨(retire_peer different).trans ((retire_peer different).trans (retire_peer different)), rfl⟩

theorem stale_zero_enters_wait {client : Client} {state : Suspend.State} {worker : Nat}
    {before : TSO.Worker}
    (atWorker : state.machine.workers[worker]? = some before)
    (current : Running client (.branch 0) before.context) (live : before.returned = false)
    (free : state.pending worker = none) (empty : before.buffer = [])
    (code : CodeAt state.machine.memory client.entry.rip bytes) (abi : client.ABI) :
    ∃ after saved,
      Suspend.schedule state [.issue worker, .issue worker, .issue worker, .issue worker] =
        .ok (after, [.machine (.retired worker none), .machine (.retired worker none),
          .machine (.retired worker none), .entered worker state.nextCall]) ∧
      after.pending worker = some saved ∧ saved.identifier = state.nextCall ∧
      client.Family saved.request ∧ classify saved.request = .ok (.wait 0) ∧
      saved.request.user.registers .r10 = 0 ∧ saved.request.continuation = client.entry.rip + 19 ∧
      saved.request.user.memory = state.machine.memory ∧
      after.nextCall = state.nextCall + 1 ∧ after.machine.memory = state.machine.memory := by
  let branched := branchContext before.context (before.context.rip + 2)
  let first := retire state worker branched
  have branchedControl : Running client .number branched := current.branch_zero
  have zf : before.context.flags.getLsbD 6 = true := by simpa using current.fields.2
  have firstStep : Suspend.issue state worker = .ok (first, .machine (.retired worker none)) :=
    issue_next atWorker current live free empty code (by intro impossible; exact (impossible rfl).elim)
      (by decide) (execute_jnz_fallthrough before.context state.machine.memory 0x16 zf)
  have firstAt : first.machine.workers[worker]? = some ⟨branched, false, []⟩ :=
    retire_selected atWorker branched
  let numbered := movContext branched .rax 202
  let second := retire first worker numbered
  have numberedControl : Running client .operation numbered := branchedControl.number_next
  have secondStep : Suspend.issue first worker = .ok (second, .machine (.retired worker none)) :=
    issue_next firstAt branchedControl rfl free rfl code trivial (by decide) (execute_mov ..)
  have secondAt : second.machine.workers[worker]? = some ⟨numbered, false, []⟩ :=
    retire_selected firstAt numbered
  let calling := movContext numbered .rsi 128
  let third := retire second worker calling
  have callingControl : Running client .syscall calling := numberedControl.operation_next
  have thirdStep : Suspend.issue second worker = .ok (third, .machine (.retired worker none)) :=
    issue_next secondAt numberedControl rfl free rfl code trivial (by decide) (execute_mov ..)
  have thirdAt : third.machine.workers[worker]? = some ⟨calling, false, []⟩ :=
    retire_selected secondAt calling
  let request : SyscallRequest := ⟨MachineThreads.contextState calling state.machine.memory, calling.rip + 2⟩
  let after := Suspend.capture third worker request
  have entered : Suspend.issue third worker = .ok (after, .entered worker state.nextCall) :=
    (syscall_enabled thirdAt callingControl rfl free rfl code).1
  have family : client.Family request := ⟨callingControl, rfl⟩
  refine ⟨after, ⟨state.nextCall, worker, request⟩, ?_, ?_, rfl, family,
    Family.classifies abi family, ?_, Family.continuation family, rfl, rfl, rfl⟩
  · simp only [Suspend.schedule, Suspend.step, firstStep, secondStep, thirdStep, entered, ok_bind]
    rfl
  · simp [after, Suspend.capture, third, second, first, retire]
  · exact (callingControl.stable.register .r10 (by decide) (by decide) (by decide) (by decide)).trans abi.2.1

theorem published_one_returns {client : Client} {state : Suspend.State} {worker : Nat}
    {before : TSO.Worker}
    (atWorker : state.machine.workers[worker]? = some before)
    (current : Running client .load before.context) (live : before.returned = false)
    (free : state.pending worker = none) (empty : before.buffer = [])
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (aligned : atomicAddressable (client.entry.registers .rdi) = true)
    (published : loadDWord state.machine.memory (client.entry.registers .rdi) = .ok 1)
    (doneCanonical : X86.canonical (client.entry.rip + 29) = true)
    (stack : readWord state.machine.memory (client.entry.registers .rsp) = .ok client.returnTarget)
    (returnCanonical : X86.canonical client.returnTarget = true) :
    ∃ after selected,
      Suspend.schedule state [.issue worker, .issue worker, .issue worker, .issue worker] =
        .ok (after, [.machine (.retired worker none), .machine (.retired worker none),
          .machine (.retired worker none), .machine (.retired worker none)]) ∧
      after.machine.workers[worker]? = some selected ∧ selected.returned = true ∧
      selected.context.registers .rax = 1 ∧ selected.context.rip = client.returnTarget ∧
      selected.context.registers .rsp = client.entry.registers .rsp + 8 ∧
      selected.context.flags = cmpZeroFlags32 before.context.flags 1 ∧
      selected.context.registers .rcx = before.context.registers .rcx ∧
      selected.context.registers .r11 = before.context.registers .r11 ∧
      selected.buffer = [] ∧ after.pending worker = none ∧
      after.machine.memory = state.machine.memory ∧
      WorkerControl client worker after selected ∧
      (∀ peer, peer ≠ worker →
        after.machine.workers[peer]? = state.machine.workers[peer]? ∧
        after.pending peer = state.pending peer) := by
  let loaded := before.context.loaded 1
  let first := retire state worker loaded
  have loadedControl : Running client (.compare 1) loaded := current.load_next 1
  have firstStep : Suspend.issue state worker = .ok (first, .machine (.retired worker none)) :=
    issue_next atWorker current live free empty code ⟨aligned, 1, published⟩ (by decide)
      (execute_load before.context state.machine.memory 1 (by rw [current.rdi]; exact published))
  have firstAt : first.machine.workers[worker]? = some ⟨loaded, false, []⟩ :=
    retire_selected atWorker loaded
  let compared := cmpContext loaded
  let second := retire first worker compared
  have comparedControl : Running client (.branch 1) compared := loadedControl.compare_next
  have secondStep : Suspend.issue first worker = .ok (second, .machine (.retired worker none)) :=
    issue_next firstAt loadedControl rfl free rfl code trivial (by decide) (execute_cmp ..)
  have secondAt : second.machine.workers[worker]? = some ⟨compared, false, []⟩ :=
    retire_selected firstAt compared
  let checked := branchContext compared (client.entry.rip + 29)
  let third := retire second worker checked
  have checkedControl : Running client (.done 1) checked := comparedControl.branch_nonzero (by decide)
  have branchStep := execute_jnz_taken compared state.machine.memory 0x16 checkedControl.fields.2.2
    (by rw [branch_done_target comparedControl]; exact doneCanonical)
  rw [branch_done_target comparedControl] at branchStep
  have thirdStep : Suspend.issue second worker = .ok (third, .machine (.retired worker none)) :=
    issue_next secondAt comparedControl rfl free rfl code (fun _ => doneCanonical) (by decide) branchStep
  have thirdAt : third.machine.workers[worker]? = some ⟨checked, false, []⟩ :=
    retire_selected secondAt checked
  let returned := client.returned checked
  let fourth := retire third worker returned true
  have fourthStep : Suspend.issue third worker = .ok (fourth, .machine (.retired worker none)) :=
    (ret_enabled thirdAt checkedControl rfl free rfl code stack returnCanonical).1
  refine ⟨fourth, ⟨returned, true, []⟩, ?_, retire_selected thirdAt returned true,
    rfl, ?_, rfl, ?_, ?_, ?_, ?_, rfl, free, rfl,
    .returned checked 1 checkedControl rfl rfl free rfl, ?_⟩
  · simp only [Suspend.schedule, Suspend.step, firstStep, secondStep, thirdStep, fourthStep, ok_bind]
    rfl
  · simp [returned, checked, compared, loaded, Client.returned, branchContext,
      cmpContext, Threads.Context.loaded]
  · simp [returned, Client.returned, checkedControl.rsp]
  · simp [returned, checked, compared, loaded, Client.returned, branchContext,
      cmpContext, Threads.Context.loaded]
  · simp [returned, checked, compared, loaded, Client.returned, branchContext,
      cmpContext, Threads.Context.loaded]
  · simp [returned, checked, compared, loaded, Client.returned, branchContext,
      cmpContext, Threads.Context.loaded]
  · intro peer different
    exact ⟨(retire_peer different).trans ((retire_peer different).trans
      ((retire_peer different).trans (retire_peer different))), rfl⟩

theorem WorkerControl.returned_checked {client : Client} {state : Suspend.State} {worker : Nat}
    {actual : TSO.Worker} (control : WorkerControl client worker state actual)
    (done : actual.returned = true) :
    ∃ observed context,
      Running client (.done observed) context ∧ actual.context = client.returned context ∧
      actual.context.registers .rax = observed.setWidth 64 ∧ observed ≠ 0 ∧
      actual.context.rip = client.returnTarget ∧
      actual.context.registers .rsp = client.entry.registers .rsp + 8 ∧
      actual.context.flags = context.flags ∧ actual.context.registers .rcx = context.registers .rcx ∧
      actual.context.registers .r11 = context.registers .r11 := by
  cases control with
  | running _ _ live _ _ | entered _ _ _ _ _ live _ => simp [done] at live
  | returned context observed checked historical _ _ _ =>
    rw [historical]
    refine ⟨observed, context, checked, rfl, ?_, checked.fields.2.1, rfl, ?_, rfl, ?_, ?_⟩
    · simpa [Client.returned] using checked.fields.1
    · simp [Client.returned, checked.rsp]
    · simp [Client.returned]
    · simp [Client.returned]

end EDSL.OS.Futex.Predicate

#print axioms EDSL.OS.Futex.Predicate.decode_at
#print axioms EDSL.OS.Futex.Predicate.syscall_enabled
#print axioms EDSL.OS.Futex.Predicate.ret_enabled
#print axioms EDSL.OS.Futex.Predicate.retry_three_issues
#print axioms EDSL.OS.Futex.Predicate.stale_zero_enters_wait
#print axioms EDSL.OS.Futex.Predicate.published_one_returns
#audit_edsl
