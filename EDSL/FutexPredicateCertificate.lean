/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Notification
import EDSL.OS.Futex.Predicate.Completion
import EDSL.ELF.Loader

set_option warningAsError true

namespace EDSL.FutexPredicateCertificate
open X86 OS OS.Futex OS.Futex.Predicate

/-- This exact profile reloads the predicate after every WAIT completion.
Its return-one contract uses the managed zero/one signal protocol; arbitrary
nonzero values outside that protocol are not claimed to return one. -/
def accepts (candidate : List Byte) : Bool := decide (candidate = Predicate.bytes)

/-- Selection uses the restricted loader's actual ELF entry and complete
file-backed executable window, rather than searching the file for a byte list. -/
def acceptsELF (file : List Byte) : Bool :=
  match ELF.parse file with
  | .error _ => false
  | .ok image => ELF.checkEntry file image Predicate.bytes

theorem acceptsELF_sound {file : List Byte} (accepted : acceptsELF file = true) :
    ∃ image, ELF.parse file = .ok image ∧ ELF.checkEntry file image Predicate.bytes = true := by
  cases parsed : ELF.parse file with
  | error error => simp [acceptsELF, parsed] at accepted
  | ok image => exact ⟨image, rfl, by simpa [acceptsELF, parsed] using accepted⟩

/-- Current executable code is bound to the actual loop member. The ABI and
canonical branch targets are explicit consequences of current admission. -/
structure Binding (candidate : List Byte) (cohort : Predicate.Cohort) (state : Futex.State)
    (worker : Nat) (client : Predicate.Client) : Prop where
  exactBytes : candidate = Predicate.bytes
  length : candidate.length = 30
  member : cohort.clients[worker]? = some (.waitLoop client)
  code : CodeAt state.suspended.machine.memory client.entry.rip candidate
  abi : client.ABI
  targets : canonical client.entry.rip = true ∧ canonical (client.entry.rip + 29) = true

/-- All environmental obligations remain in current admission. In particular,
loading code creates no keeper, call pin, stack loan, payload grant or thread.
Safety and constructive suffixes below are checked theorems of this admission,
not fields promising that a scheduler will execute a future trace. -/
structure Specification (candidate : List Byte) (cohort : Predicate.Cohort) (state : Futex.State)
    (worker : Nat) (client : Predicate.Client) : Prop where
  binding : Binding candidate cohort state worker client
  admitted : Predicate.Admitted cohort state

theorem sound (candidate : List Byte) (accepted : accepts candidate = true)
    {cohort : Predicate.Cohort} {state : Futex.State} {worker : Nat} {client : Predicate.Client}
    (admitted : Predicate.Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (code : CodeAt state.suspended.machine.memory client.entry.rip candidate) :
    Specification candidate cohort state worker client := by
  have exactBytes : candidate = Predicate.bytes := of_decide_eq_true accepted
  refine ⟨⟨exactBytes, ?_, member, code,
    (admitted.static.descriptors worker (.waitLoop client) member).2.1,
    admitted.static.loopTargets worker client member⟩, admitted⟩
  rw [exactBytes]
  decide

theorem Specification.of_admitted
    {candidate : List Byte} {cohort : Predicate.Cohort} {before after : Futex.State}
    {worker : Nat} {client : Predicate.Client}
    (certificate : Specification candidate cohort before worker client)
    (admitted : Predicate.Admitted cohort after) :
    Specification candidate cohort after worker client := by
  apply sound candidate (by simp [accepts, certificate.binding.exactBytes]) admitted certificate.binding.member
  rw [certificate.binding.exactBytes]
  exact admitted.currentCode worker (.waitLoop client) certificate.binding.member

/-- Every successful actual raw instruction has a positive managed lift with
identical physical state and observation. Managed success is a conclusion. -/
theorem Specification.issue
    {candidate : List Byte} {cohort : Predicate.Cohort} {state : Futex.State}
    {worker : Nat} {client : Predicate.Client}
    (certificate : Specification candidate cohort state worker client)
    {selected : Nat} {suspended : Suspend.State} {observation : Suspend.Observation}
    (actual : Suspend.issue state.suspended selected = .ok (suspended, observation)) :
    ∃ after, Physical.issue cohort.profile state selected = .ok (after, observation) ∧
      after.suspended = suspended ∧ Specification candidate cohort after worker client := by
  obtain ⟨after, issued, same, admitted⟩ := Predicate.issue_lift certificate.admitted actual
  exact ⟨after, issued, same, certificate.of_admitted admitted⟩

theorem Specification.drain
    {candidate : List Byte} {cohort : Predicate.Cohort} {state : Futex.State}
    {worker : Nat} {client : Predicate.Client}
    (certificate : Specification candidate cohort state worker client)
    {selected : Nat} {suspended : Suspend.State} {observation : Suspend.Observation}
    (actual : Suspend.drain state.suspended selected = .ok (suspended, observation)) :
    ∃ after, Physical.drain cohort.profile state selected = .ok (after, observation) ∧
      after.suspended = suspended ∧ Specification candidate cohort after worker client := by
  obtain ⟨after, drained, same, admitted⟩ := Predicate.drain_lift certificate.admitted actual
  exact ⟨after, drained, same, certificate.of_admitted admitted⟩

theorem Specification.service
    {candidate : List Byte} {cohort : Predicate.Cohort} {state : Futex.State}
    {worker : Nat} {client : Predicate.Client}
    (certificate : Specification candidate cohort state worker client)
    {action : Futex.Action} (guard : Predicate.Guard state action) :
    ∃ after, Futex.step cohort.profile.service state action = .ok after ∧
      Specification candidate cohort after worker client := by
  obtain ⟨after, serviced, admitted⟩ := Predicate.service_lift certificate.admitted guard
  exact ⟨after, serviced, certificate.of_admitted admitted⟩

/-- The artifact binding survives every accepted mixed physical/service trace. -/
theorem Specification.trace
    {candidate : List Byte} {cohort : Predicate.Cohort} {before after : Futex.State}
    {worker : Nat} {client : Predicate.Client}
    (certificate : Specification candidate cohort before worker client)
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (trace : Runtime.Trace cohort.profile before actions observations after) :
    Specification candidate cohort after worker client :=
  certificate.of_admitted (certificate.admitted.trace trace)

/-- The exact finite physical prefix is lifted; a future successful managed
replay is not supplied by the caller or the artifact certificate. -/
theorem Specification.lift_prefix
    {candidate : List Byte} {cohort : Predicate.Cohort} {state : Futex.State}
    {worker : Nat} {client : Predicate.Client}
    (certificate : Specification candidate cohort state worker client)
    {actions : List Runtime.Action} {observations : List Runtime.Observation} {physical : Suspend.State}
    (trace : Predicate.MachineTrace state.suspended actions observations physical) :
    ∃ after, Runtime.Trace cohort.profile state actions observations after ∧
      after.suspended = physical ∧ Specification candidate cohort after worker client := by
  obtain ⟨after, lifted, same, admitted⟩ := Predicate.MachineTrace.lift trace certificate.admitted rfl
  exact ⟨after, lifted, same, certificate.of_admitted admitted⟩

/-- The observable terminal contract includes the predicate check, return one,
original RET/stack, register frame, no pending invocation and empty loop FIFO. -/
theorem Specification.returned
    {candidate : List Byte} {cohort : Predicate.Cohort} {state : Futex.State}
    {worker : Nat} {client : Predicate.Client}
    (certificate : Specification candidate cohort state worker client)
    {actual : TSO.Worker} (selected : state.suspended.machine.workers[worker]? = some actual)
    (done : actual.returned = true) : Predicate.Returns client cohort.registration.address
      state.suspended worker actual :=
  certificate.admitted.returned_sound certificate.binding.member selected done

/-- After actual publication and queue clearance, every admitted loop cut has
an enabled suffix through its protected RET. Fourteen counts modeled Runtime
actions, including service actions; it is not a timing, minimum-operation,
fairness or real-kernel theorem. Historical resume clobbers are retained. -/
theorem Specification.complete
    {candidate : List Byte} {cohort : Predicate.Cohort} {state : Futex.State}
    {worker : Nat} {client : Predicate.Client}
    (certificate : Specification candidate cohort state worker client)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker) (flags rcx r11 : Word) :
    ∃ after, Predicate.CompletesWithin 14 cohort worker client state after ∧
      Specification candidate cohort after worker client := by
  obtain ⟨after, completed⟩ := Predicate.constructive_completion_with certificate.admitted
    certificate.binding.member published clear flags rcx r11
  have evidence := completed
  obtain ⟨_, _, _, _, _, _, admitted, _⟩ := evidence
  exact ⟨after, completed, certificate.of_admitted admitted⟩

/-- The stronger suffix additionally certifies that every action selects this
loop or compares/resumes its own actual current WAIT0 invocation. -/
theorem Specification.complete_selected
    {candidate : List Byte} {cohort : Predicate.Cohort} {state : Futex.State}
    {worker : Nat} {client : Predicate.Client}
    (certificate : Specification candidate cohort state worker client)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker) (flags rcx r11 : Word) :
    ∃ after, Predicate.SelectedCompletesWithin 14 cohort worker client state after ∧
      Specification candidate cohort after worker client := by
  obtain ⟨after, completed⟩ := Predicate.constructive_completion_selected_with certificate.admitted
    certificate.binding.member published clear flags rcx r11
  have evidence := completed.forget
  obtain ⟨_, _, _, _, _, _, admitted, _⟩ := evidence
  exact ⟨after, completed, certificate.of_admitted admitted⟩

/-- Arbitrary later mixed traces cannot requeue the designated WAIT under the
published signal protocol. The conclusion retains W=1 and current artifact
admission, without claiming that an arbitrary scheduler makes progress. -/
theorem Specification.notification_trace
    {candidate : List Byte} {cohort : Predicate.Cohort} {before after : Futex.State}
    {worker : Nat} {client : Predicate.Client}
    (certificate : Specification candidate cohort before worker client)
    (published : loadDWord before.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait before worker)
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (trace : Runtime.Trace cohort.profile before actions observations after) :
    Futex.Notification.NoQueuedWait after worker ∧
      loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 ∧
      Specification candidate cohort after worker client := by
  have designated := (certificate.admitted.static.descriptors worker (.waitLoop client)
    certificate.binding.member).2.2.2.2
  have currentClear : Futex.Notification.NoQueuedWait before cohort.waiter := designated ▸ clear
  obtain ⟨safe, word, admitted⟩ :=
    Predicate.Notification.trace_preserves certificate.admitted published currentClear trace
  exact ⟨by simpa only [designated] using safe, word, certificate.of_admitted admitted⟩

/-- A real publisher's XCHG and its own associated saved WAKE establish queue
clearance without an initial-clear premise. The actual publication and arbitrary
mixed middle/suffix traces retain its payload and this loop's artifact binding. -/
theorem Specification.notification
    {candidate : List Byte} {cohort : Predicate.Cohort}
    {before exchanged waking afterWake after : Futex.State}
    {worker publisher invocation pin : Nat} {client : Predicate.Client}
    {event : AtomicEvent} {selected : Option Nat}
    {middleActions laterActions : List Runtime.Action} {prefixObs suffixObs : List Runtime.Observation}
    (certificate : Specification candidate cohort before worker client)
    (exchange : Physical.issue cohort.profile before publisher =
      .ok (exchanged, .machine (.retired publisher (some event))))
    (between : Runtime.Trace cohort.profile exchanged middleActions prefixObs waking)
    (associated : waking.calls invocation = some ⟨publisher, .wakeOne, pin, .entered⟩)
    (wake : wakeOne waking invocation selected = .ok afterWake)
    (later : Runtime.Trace cohort.profile afterWake laterActions suffixObs after) :
    (∃ producer saved, cohort.clients[publisher]? = some (.legacy producer) ∧
      producer.role = .publishPayloadWake ∧ waking.suspended.pending publisher = some saved ∧
      saved.identifier = invocation ∧ producer.Family saved.request ∧
      loadDWord after.suspended.machine.memory producer.store.address = .ok producer.store.value) ∧
    Futex.Notification.NoQueuedWait after worker ∧
      loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 ∧
      Specification candidate cohort after worker client := by
  obtain ⟨publication, clear, word, admitted⟩ := Predicate.Notification.exchange_wake_trace
    certificate.admitted exchange between associated wake later
  have designated := (certificate.admitted.static.descriptors worker (.waitLoop client)
    certificate.binding.member).2.2.2.2
  exact ⟨publication, by simpa only [designated] using clear, word, certificate.of_admitted admitted⟩

/-- Full literal ELF parsing/loading binds this entry's exact loop code to the
same actual admitted client. Freshness, current memory, ABI and OS resources
remain explicit premises; loading establishes no Linux startup refinement. -/
theorem loaded_sound (file candidate : List Byte) (image : ELF.Image)
    (parsed : ELF.parse file = .ok image) (checked : ELF.checkEntry file image candidate = true)
    (accepted : accepts candidate = true) (prior : AddressSpace.Space)
    (free : ELF.fresh image prior = true)
    {cohort : Predicate.Cohort} {state : Futex.State} {worker : Nat} {client : Predicate.Client}
    (admitted : Predicate.Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (memory : state.suspended.machine.memory = AddressSpace.toMemory (ELF.install file image prior))
    (entry : client.entry.rip = ELF.codeAddress image) :
    ELF.load file prior = .ok ⟨image, ELF.install file image prior⟩ ∧
      Specification candidate cohort state worker client := by
  refine ⟨ELF.load_success file prior image parsed free, sound candidate accepted admitted member ?_⟩
  rw [memory, entry]
  exact ELF.checked_entry_code file image candidate prior checked

end EDSL.FutexPredicateCertificate

#audit_edsl
