/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Notification
import EDSL.OS.Futex.Predicate.Completion

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate.Notification
open X86

/-- Current notification positively enables a complete loop suffix. Its full
RAM frame retains every already visible payload, and the independent return
contract comes from the actual constructed trace through RET. -/
theorem complete {cohort : Cohort} {state : State} {worker : Nat} {client : Client}
    (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state cohort.waiter) (flags rcx r11 : Word) :
    ∃ after, CompletesWithin 14 cohort worker client state after ∧
      Futex.Notification.NoQueuedWait after cohort.waiter := by
  have designated : worker = cohort.waiter := (admitted.static.descriptors _ _ member).2.2.2.2
  obtain ⟨after, completed⟩ := constructive_completion_with admitted member published
    (designated.symm ▸ clear) flags rcx r11
  have witness := completed
  obtain ⟨_, _, _, trace, _, _, _, _⟩ := witness
  exact ⟨after, completed, (trace_preserves admitted published clear trace).1⟩

/-- Actual publisher retirement, an arbitrary intervening mixed prefix, its
own captured WAKE1 and an arbitrary mixed suffix establish a state from which
the loop can finish. The payload and cleared queue remain current at the
constructed return. No scheduler progress is an admission premise. -/
theorem exchange_wake_complete {cohort : Cohort}
    {before exchanged waking afterWake current : State}
    {publisher invocation pin worker : Nat} {client : Client} {event : AtomicEvent}
    {selected : Option Nat} {middleActions laterActions : List Runtime.Action}
    {prefixObs suffixObs : List Runtime.Observation}
    (admitted : Admitted cohort before)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (exchange : Physical.issue cohort.profile before publisher =
      .ok (exchanged, .machine (.retired publisher (some event))))
    (between : Runtime.Trace cohort.profile exchanged middleActions prefixObs waking)
    (associated : waking.calls invocation = some ⟨publisher, .wakeOne, pin, .entered⟩)
    (wake : wakeOne waking invocation selected = .ok afterWake)
    (later : Runtime.Trace cohort.profile afterWake laterActions suffixObs current)
    (flags rcx r11 : Word) :
    ∃ final, CompletesWithin 14 cohort worker client current final ∧
      Futex.Notification.NoQueuedWait final cohort.waiter ∧
      ∃ producer saved, cohort.clients[publisher]? = some (.legacy producer) ∧
        producer.role = .publishPayloadWake ∧
        waking.suspended.pending publisher = some saved ∧ saved.identifier = invocation ∧
        producer.Family saved.request ∧
        loadDWord final.suspended.machine.memory producer.store.address = .ok producer.store.value := by
  obtain ⟨⟨producer, saved, atProducer, role, pending, identity, family, payload⟩,
    clear, published, valid⟩ := exchange_wake_trace admitted exchange between associated wake later
  obtain ⟨final, completed, finalClear⟩ := complete valid member published clear flags rcx r11
  have witness := completed
  obtain ⟨_, _, _, _, _, _, _, frame⟩ := witness
  exact ⟨final, completed, finalClear, producer, saved, atProducer, role, pending, identity,
    family, by rw [frame.1]; exact payload⟩

end EDSL.OS.Futex.Predicate.Notification

#audit_edsl
