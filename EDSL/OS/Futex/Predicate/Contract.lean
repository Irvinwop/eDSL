/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Admission
import EDSL.OS.Futex.ClientControlStages

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86

/-- Independent observable result of the signal-word loop. The contract uses
actual machine/OS fields, not a particular control constructor or proof hint. -/
structure Returns (client : Client) (address : Word) (state : Suspend.State)
    (worker : Nat) (actual : TSO.Worker) : Prop where
  selected : state.machine.workers[worker]? = some actual
  done : actual.returned = true
  empty : actual.buffer = []
  free : state.pending worker = none
  result : actual.context.registers .rax = 1
  target : actual.context.rip = client.returnTarget
  stack : actual.context.registers .rsp = client.entry.registers .rsp + 8
  predicate : loadDWord state.machine.memory address = .ok 1
  zeroFlag : actual.context.flags.getLsbD 6 = false
  preserved : ∀ register, register ≠ .rax → register ≠ .rsi → register ≠ .rcx →
    register ≠ .r11 → register ≠ .rsp →
    actual.context.registers register = client.entry.registers register
  second : actual.context.registers .rsi = client.entry.registers .rsi ∨
    actual.context.registers .rsi = 128

/-- Current checked-signal knowledge supplies the independent return result.
Universal execution correctness additionally requires the separate actual
control-initialization and transition-preservation proofs. -/
theorem LoopControl.returned_sound {address : Word} {client : Client} {worker : Nat}
    {state : Suspend.State} {actual : TSO.Worker}
    (control : LoopControl address client worker state actual)
    (found : state.machine.workers[worker]? = some actual) (done : actual.returned = true) :
    Returns client address state worker actual := by
  cases control with
  | running _ _ _ live _ _ => simp [done] at live
  | entered _ _ _ _ _ live _ => simp [done] at live
  | returned context observed checked known historical _ free empty =>
    obtain ⟨domain, published⟩ := known observed rfl
    have one : observed = 1 := by
      rcases domain with zero | one
      · exact (checked.fields.2.1 zero).elim
      · exact one
    subst observed
    refine ⟨found, done, empty, free, ?_, ?_, ?_, published rfl, ?_, ?_, ?_⟩
    · simp [historical, Client.returned, checked.fields.1]
    · simp [historical, Client.returned]
    · simp [historical, Client.returned, checked.rsp]
    · simpa [historical, Client.returned] using checked.fields.2.2
    · intro register rax rsi rcx r11 rsp
      simpa [historical, Client.returned, rsp] using
        checked.stable.register register rax rsi rcx r11
    · simpa [historical, Client.returned] using checked.stable.2

theorem Admitted.returned_sound {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} {actual : TSO.Worker} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (found : state.suspended.machine.workers[worker]? = some actual)
    (done : actual.returned = true) : Returns client cohort.registration.address state.suspended worker actual := by
  obtain ⟨kind, atKind, control⟩ := admitted.control worker actual found
  have same : kind = .waitLoop client := Option.some.inj (atKind.symm.trans member)
  subst kind
  exact LoopControl.returned_sound control found done

/-- A returned loop has no live service call for its worker: actual call
records must be tied to a current Saved record, which the result excludes. -/
theorem Returns.no_call {client : Client} {address : Word} {state : Futex.State}
    {worker : Nat} {actual : TSO.Worker} {profile : Physical.Profile}
    (returned : Returns client address state.suspended worker actual)
    (runtime : Runtime.Invariant profile state) {identifier : Nat} {call : Call}
    (found : state.calls identifier = some call) : call.worker ≠ worker := by
  intro same
  obtain ⟨saved, pending, _, _, _⟩ := (runtime.service.calls identifier call found).saved
  rw [same, returned.free] at pending
  cases pending

theorem LoopControl.initial (address : Word) (client : Client) (worker : Nat)
    (state : Suspend.State) (free : state.pending worker = none) :
    LoopControl address client worker state ⟨client.entry, false, []⟩ := by
  refine .running .load (Running.initial client) ?_ rfl free rfl
  simp [Point.Known, Point.Observed]

def Kind.initialWorker (kind : Kind) : TSO.Worker := ⟨kind.binding.entry, false, []⟩

/-- Fresh physical workers have genuine initial controls; this does not
manufacture calls, queues, resource rights or a future execution premise. -/
theorem Control.initial (cohort : Cohort) (authority : Atomics.State)
    (registration : Option Resources.Registration) :
    Control cohort (Runtime.initial authority registration (cohort.clients.map Kind.initialWorker)).suspended := by
  intro worker actual found
  change (cohort.clients.map Kind.initialWorker)[worker]? = some actual at found
  rw [List.getElem?_map] at found
  cases member : cohort.clients[worker]? with
  | none => simp [member] at found
  | some kind =>
    simp only [member, Option.map_some, Option.some.injEq] at found
    subst actual
    refine ⟨kind, rfl, ?_⟩
    cases kind with
    | waitLoop client => exact LoopControl.initial _ _ _ _ rfl
    | legacy client => exact Clients.WorkerControl.initial _ _ _ rfl

end EDSL.OS.Futex.Predicate

#audit_edsl
