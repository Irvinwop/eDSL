/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.WordProjection.Reads
import EDSL.OS.TSO64.WordProjection.Writes

/-!
Finite, labelled refinement of the checked scheduler's managed uniform-qword
fragment. Classification retains actual MOV64 reads, actual admission requests
and tags, and the five reference actions of a checked locked RMW. In particular,
endpoint equality alone never permits erasing a selected managed MOV64 read.

Ordinary memory outside this projection, registers, instruction control and
resource bookkeeping are erased. Initial queues and memory are explicit run
boundaries. This result establishes neither source-language ordering, hardware
validity, fairness, progress nor correspondence with the complete HOL4 model.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.WordProjection
open X86 Concurrency

/-- Only a MOV64 without a current managed selector may take the quiet read
case. The universally quantified form prevents erasing a managed MOV by
presenting it through a generic instruction variable. -/
def ErasableLoad (state : TSO64.State) (worker : Worker)
    (instruction : Sequential.Instruction) : Prop :=
  ∀ destination address, instruction = .loadMem64 destination address →
    atomicFor state.world worker.resources (address.eval (localCPU state worker)) = none

/-- Labels for one real ordinary effect. Store constructors retain the actual
request/admission, and the managed-load constructor retains the actual selected
descriptor and byte-load result. Endpoint equalities are proved from the real
queue/finish effects, not checked by another executor. -/
inductive OrdinaryTrace (state : TSO64.State) (tid : Nat) (worker : Worker)
    (instruction : Sequential.Instruction) (result : TSO64.State × Observation)
    (profile : Profile) : List ReferenceLabel → Prop where
  | quiet (intent : storeIntent instruction (localCPU state worker) = none)
      (erasable : ErasableLoad state worker instruction)
      (same : project result.1 = project state) :
      OrdinaryTrace state tid worker instruction result profile []
  | owned (store : Store) (ticket : Ownership.Ticket)
      (intent : storeIntent instruction (localCPU state worker) = some store)
      (admission : Queue.Admission state.world worker.resources store worker.nextStore
        profile (.ordinary ticket store))
      (same : project result.1 = project state) :
      OrdinaryTrace state tid worker instruction result profile []
  | managed (store : Store) (reference : Queue.ManagedRef) (value : Word)
      (occurrence : Nat)
      (intent : storeIntent instruction (localCPU state worker) = some store)
      (admission : Queue.Admission state.world worker.resources store worker.nextStore
        profile (.managed reference value occurrence))
      (same : project result.1 =
        TSOWord.writeBuffered (project state) tid reference.handle.cell value) :
      OrdinaryTrace state tid worker instruction result profile
        [.write tid reference.handle.cell value]
  | load (destination : Register) (address : Sequential.Address)
      (reference : Queue.ManagedRef) (value : Word)
      (decoded : instruction = .loadMem64 destination address)
      (selected : atomicFor state.world worker.resources
        (address.eval (localCPU state worker)) =
          some (reference.identifier, reference.handle, reference.cell))
      (loaded : loadQWord (localCPU state worker).memory reference.cell.address = .ok value)
      (same : project result.1 = project state) :
      OrdinaryTrace state tid worker instruction result profile
        [.read tid reference.handle.cell value]

/-- The real ordinary effect always has a constrained label classification.
A successful current managed MOV64 is classified from its actual local load,
regardless of whether its destination or projected endpoint changes. -/
theorem ordinary_trace {state : TSO64.State} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {af : Bool}
    {result : TSO64.State × Observation} {profile : Profile}
    (effect : OrdinaryEffect state tid worker instruction af result profile)
    (live : state.workers[tid]? = some worker) :
    ∃ labels, OrdinaryTrace state tid worker instruction result profile labels := by
  classical
  cases ordinary_queue_projection effect live with
  | quiet intent same =>
    by_cases isLoad : ∃ destination address, instruction = .loadMem64 destination address
    · obtain ⟨destination, address, equal⟩ := isLoad
      subst instruction
      cases selected : atomicFor state.world worker.resources
          (address.eval (localCPU state worker)) with
      | none =>
        refine ⟨[], .quiet intent ?_ same⟩
        intro otherDestination otherAddress equal
        cases equal
        exact selected
      | some descriptor =>
        rcases descriptor with ⟨identifier, handle, cell⟩
        obtain ⟨value, loaded, _current, _installed⟩ := effect.loadMem64
        have addressEq := (atomicFor_sound selected).2.2
        rw [← addressEq] at loaded
        exact ⟨[.read tid handle.cell value],
          .load destination address ⟨identifier, handle, cell⟩ value rfl selected loaded same⟩
    · refine ⟨[], .quiet intent ?_ same⟩
      intro destination address equal
      exact False.elim (isLoad ⟨destination, address, equal⟩)
  | owned store ticket intent admission same =>
    exact ⟨[], .owned store ticket intent admission same⟩
  | managed store reference value occurrence intent admission same =>
    exact ⟨[.write tid reference.handle.cell value],
      .managed store reference value occurrence intent admission same⟩

/-- Soundness of each constrained ordinary trace. A managed read uses the
independently defined reference read rule, including actual newest-buffer
forwarding or absence of any own pending alias. -/
theorem OrdinaryTrace.path {state : TSO64.State} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {result : TSO64.State × Observation}
    {profile : Profile} {labels : List ReferenceLabel}
    (trace : OrdinaryTrace state tid worker instruction result profile labels)
    (valid : WellFormed state profile) (live : state.workers[tid]? = some worker) :
    TSOWord.Path (project state) labels (project result.1) := by
  cases trace with
  | quiet intent erasable same =>
    rw [same]
    exact TSOWord.Path.nil _
  | owned store ticket intent admission same =>
    rw [same]
    exact TSOWord.Path.nil _
  | managed store reference value occurrence intent admission same =>
    rw [same]
    exact TSOWord.Path.cons TSOWord.Step.writeBuffer (TSOWord.Path.nil _)
  | load destination address reference value decoded selected loaded same =>
    have authoritative := atomicFor_sound selected
    have current : Queue.Current state.world worker.resources reference :=
      ⟨authoritative.1, authoritative.2.1⟩
    rw [same]
    exact TSOWord.Path.cons (managed_read valid live current loaded) (TSOWord.Path.nil _)

/-- A selected actual MOV64 cannot be silently classified. This gives clients
an exact label without choosing the existential trace returned by the general
step theorem or comparing projected endpoints. -/
theorem OrdinaryTrace.load_labels {state : TSO64.State} {tid : Nat} {worker : Worker}
    {destination : Register} {address : Sequential.Address}
    {result : TSO64.State × Observation} {profile : Profile}
    {labels : List ReferenceLabel} {reference : Queue.ManagedRef} {value : Word}
    (trace : OrdinaryTrace state tid worker (.loadMem64 destination address) result profile labels)
    (selected : atomicFor state.world worker.resources
      (address.eval (localCPU state worker)) =
        some (reference.identifier, reference.handle, reference.cell))
    (loaded : loadQWord (localCPU state worker).memory reference.cell.address = .ok value) :
    labels = [.read tid reference.handle.cell value] := by
  cases trace with
  | quiet intent erasable same =>
    have absent := erasable destination address rfl
    rw [selected] at absent
    cases absent
  | owned store ticket intent admission same =>
    simp [storeIntent, Sequential.Instruction.storeIntent64,
      Sequential.Instruction.storeIntent] at intent
  | managed store writer stored occurrence intent admission same =>
    simp [storeIntent, Sequential.Instruction.storeIntent64,
      Sequential.Instruction.storeIntent] at intent
  | load otherDestination otherAddress reader readValue decoded chosen read same =>
    cases decoded
    have descriptorEq := Option.some.inj (selected.symm.trans chosen)
    have sameHandle : reference.handle = reader.handle :=
      congrArg (fun descriptor : Atomics64.HandleId64 × Atomics64.Handle × Atomics64.Cell =>
        descriptor.2.1) descriptorEq
    have sameCell : reference.cell = reader.cell :=
      congrArg (fun descriptor : Atomics64.HandleId64 × Atomics64.Handle × Atomics64.Cell =>
        descriptor.2.2) descriptorEq
    rw [sameCell] at loaded
    have sameValue : value = readValue := Except.ok.inj (loaded.symm.trans read)
    rw [← sameHandle, ← sameValue]

/-- An actually admitted managed enqueue fixes its exact reference write
label. Ordinary admission cannot erase it, since admission gives preference to
an ordinary grant and the managed admission records that grant's absence. -/
theorem OrdinaryTrace.managed_labels {state : TSO64.State} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {result : TSO64.State × Observation}
    {profile : Profile} {labels : List ReferenceLabel} {store : Store}
    {reference : Queue.ManagedRef} {value : Word} {occurrence : Nat}
    (trace : OrdinaryTrace state tid worker instruction result profile labels)
    (intent : storeIntent instruction (localCPU state worker) = some store)
    (admission : Queue.Admission state.world worker.resources store worker.nextStore
      profile (.managed reference value occurrence)) :
    labels = [.write tid reference.handle.cell value] := by
  cases trace with
  | quiet absent erasable same =>
    rw [intent] at absent
    cases absent
  | owned otherStore ticket captured ordinary same =>
    have sameStore : store = otherStore := Option.some.inj (intent.symm.trans captured)
    subst otherStore
    cases admission with
    | managed reference value absent shared qword selected =>
      cases ordinary with
      | ordinary ticket chosen =>
        rw [chosen] at absent
        cases absent
  | managed otherStore writer stored otherOccurrence captured managed same =>
    have sameStore : store = otherStore := Option.some.inj (intent.symm.trans captured)
    subst otherStore
    cases admission with
    | managed reference value absent shared qword selected =>
      cases managed with
      | managed writer stored otherAbsent otherShared otherQword chosen =>
        have descriptorEq := Option.some.inj (selected.symm.trans chosen)
        have sameHandle : reference.handle = writer.handle :=
          congrArg (fun descriptor : Atomics64.HandleId64 × Atomics64.Handle × Atomics64.Cell =>
            descriptor.2.1) descriptorEq
        have sameValue : value = stored :=
          StoreBuffer.Mixed.Value.qword.inj (qword.symm.trans otherQword)
        rw [← sameHandle, ← sameValue]
  | load destination address reader readValue decoded selected loaded same =>
    subst instruction
    simp [storeIntent, Sequential.Instruction.storeIntent64,
      Sequential.Instruction.storeIntent] at intent

/-- Per-action classification tied to an actual successful scheduler action.
Ordinary instructions retain their decoded origin. Publications retain the
actual head tag, and RMW labels retain the actual checked event values. -/
inductive StepTrace (state : TSO64.State) : Action → (TSO64.State × Observation) →
    Profile → List ReferenceLabel → Prop where
  | ordinary {tid : Nat} {af : Bool} {worker : Worker}
      {instruction : Sequential.Instruction} {result : TSO64.State × Observation}
      {profile : Profile} {labels : List ReferenceLabel}
      (success : step state (.issue tid af) profile = .ok result)
      (live : state.workers[tid]? = some worker)
      (fetched : decode (fetchCPU state worker) = .ok (.ordinary instruction))
      (effect : OrdinaryEffect state tid worker instruction af result profile)
      (classified : OrdinaryTrace state tid worker instruction result profile labels) :
      StepTrace state (.issue tid af) result profile labels
  | blocked {action : Action} {after : TSO64.State} {tid : Nat} {profile : Profile}
      (success : step state action profile = .ok (after, .blocked tid)) :
      StepTrace state action (after, .blocked tid) profile []
  | ordinaryDrain {tid : Nat} {after : TSO64.State} {ticket : Ownership.Ticket}
      {store : Store} {profile : Profile}
      (success : step state (.drain tid) profile =
        .ok (after, .drained tid (.ordinary ticket store))) :
      StepTrace state (.drain tid) (after, .drained tid (.ordinary ticket store)) profile []
  | managedDrain {tid : Nat} {after : TSO64.State} {reference : Queue.ManagedRef}
      {value : Word} {occurrence : Nat} {profile : Profile}
      (success : step state (.drain tid) profile =
        .ok (after, .drained tid (.managed reference value occurrence))) :
      StepTrace state (.drain tid)
        (after, .drained tid (.managed reference value occurrence)) profile [.tau]
  | rmw {action : Action} {after : TSO64.State} {tid : Nat}
      {event : Atomics64.FetchAddEvent} {profile : Profile}
      (success : step state action profile = .ok (after, .rmw tid event)) :
      StepTrace state action (after, .rmw tid event) profile
        [.lock tid, .read tid event.cell event.arithmetic.event.before,
          .write tid event.cell event.arithmetic.event.after, .tau, .unlock tid]

/-- A classified action always retains its exact successful checked step. -/
theorem StepTrace.success {state : TSO64.State} {action : Action}
    {result : TSO64.State × Observation} {profile : Profile} {labels : List ReferenceLabel}
    (trace : StepTrace state action result profile labels) :
    step state action profile = .ok result := by
  cases trace <;> assumption

/-- Every classified action has the same labelled reference behavior. The
managed-drain case uses its real FIFO-head publication; ordinary drains use
registered-cell framing and cannot skip a managed concrete head. -/
theorem StepTrace.path {state : TSO64.State} {action : Action}
    {result : TSO64.State × Observation} {profile : Profile} {labels : List ReferenceLabel}
    (trace : StepTrace state action result profile labels) (valid : WellFormed state profile) :
    TSOWord.Path (project state) labels (project result.1) := by
  cases trace with
  | ordinary success live fetched effect classified => exact classified.path valid live
  | blocked success =>
    rw [blocked_unchanged success]
    exact TSOWord.Path.nil _
  | ordinaryDrain success =>
    cases drain_projection valid success with
    | ordinary ticket store observed same =>
      rw [same]
      exact TSOWord.Path.nil _
    | managed reference value occurrence observed path => cases observed
  | managedDrain success =>
    cases drain_projection valid success with
    | ordinary ticket store observed same => cases observed
    | managed reference value occurrence observed path => exact path
  | rmw success => exact rmw_path valid success

/-- Every successful actual step admits a constrained trace. No read label is
chosen by comparing desired postconditions or testing reference reachability. -/
theorem step_trace {state : TSO64.State} {action : Action}
    {result : TSO64.State × Observation} {profile : Profile}
    (valid : WellFormed state profile) (success : step state action profile = .ok result) :
    ∃ labels, StepTrace state action result profile labels ∧
      TSOWord.Path (project state) labels (project result.1) := by
  have classified : ∃ labels, StepTrace state action result profile labels := by
    cases step_origin success with
    | ordinary live running code caller fetched effect =>
      obtain ⟨labels, trace⟩ := ordinary_trace effect live
      exact ⟨labels, .ordinary success live fetched effect trace⟩
    | blocked live running code caller fetched bounds nonempty =>
      exact ⟨[], .blocked success⟩
    | rmw live running code caller fetched bounds empty grant effect =>
      exact ⟨_, .rmw success⟩
    | @drained tid worker head tail output profile live fifo gate changed effect =>
      cases head with
      | ordinary ticket store => exact ⟨[], .ordinaryDrain success⟩
      | managed reference value occurrence => exact ⟨[.tau], .managedDrain success⟩
  obtain ⟨labels, trace⟩ := classified
  exact ⟨labels, trace, trace.path valid⟩

/-- Composition of reference paths preserves the complete ordered labels. -/
theorem path_append {before middle after : ReferenceState}
    {first second : List ReferenceLabel}
    (head : TSOWord.Path before first middle) (tail : TSOWord.Path middle second after) :
    TSOWord.Path before (first ++ second) after := by
  induction head with
  | nil => exact tail
  | cons first following ih => exact TSOWord.Path.cons first (ih tail)

/-- A classified schedule retains one actual step proof per input action and
one observed result per step. Reference labels concatenate in action order;
a locked action contributes its complete five-label expansion. -/
inductive ScheduleTrace (profile : Profile) : TSO64.State → List Action →
    (TSO64.State × List Observation) → List ReferenceLabel → Prop where
  | nil (state : TSO64.State) : ScheduleTrace profile state [] (state, []) []
  | cons {state : TSO64.State} {action : Action} {rest : List Action}
      {head : TSO64.State × Observation} {tail : TSO64.State × List Observation}
      {first following : List ReferenceLabel}
      (stepped : StepTrace state action head profile first)
      (scheduled : ScheduleTrace profile head.1 rest tail following) :
      ScheduleTrace profile state (action :: rest) (tail.1, head.2 :: tail.2)
        (first ++ following)

/-- Every actual finite schedule has both per-action classification and a
reference path with those same labels. Validity is propagated through the real
scheduler, rather than assumed independently at every intermediate state. -/
theorem schedule_trace {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile}
    (valid : WellFormed state profile)
    (success : schedule state actions profile = .ok result) :
    ∃ labels, ScheduleTrace profile state actions result labels ∧
      TSOWord.Path (project state) labels (project result.1) := by
  induction actions generalizing state result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    exact ⟨[], .nil state, TSOWord.Path.nil _⟩
  | cons action rest ih =>
    obtain ⟨head, tail, stepped, scheduled, same⟩ := schedule_cons_ok success
    obtain ⟨first, classified, headPath⟩ := step_trace valid stepped
    obtain ⟨following, tailTrace, tailPath⟩ :=
      ih (step_wellFormed valid stepped) scheduled
    rw [same]
    exact ⟨first ++ following, .cons classified tailTrace, path_append headPath tailPath⟩

end EDSL.OS.TSO64.WordProjection
