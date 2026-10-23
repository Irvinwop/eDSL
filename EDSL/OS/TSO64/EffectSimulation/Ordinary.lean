/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects.Head
import EDSL.OS.TSO64.Access
import EDSL.X86.VCGen.ManagedRules

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Whole local-CPU coherence for the existing ordinary TSO64 scheduler. Issue
retains the world; the installed context and the actual admitted mixed FIFO
reconstruct the executor's entire successor state. The converse uses checked
effect-head evidence and current prestate OS gates, under either existing
authority profile. Own drain preserves the local CPU while publishing its head.

No instruction semantics, scheduler actions, authority, or atomic widths are
extended here. In particular no sequential DWORD atomic observation is lifted
to a qword RMW. These single-action facts supply no interleaving invariant,
fairness, whole-program progress, target-hardware theorem, or corpus credit.
-/

namespace EDSL.OS.TSO64.EffectSimulation
open X86

abbrev S := OS.TSO64.State
abbrev O := OS.TSO64.Observation

/-- Actual retirement together with equality of the FULL reconstructed CPU,
including memory and permission maps. Atomic and syscall outcomes fail closed. -/
def Reifies (tid : Nat) (result : S × O)
    (actual : Sequential.Observation) : Prop :=
  ∃ worker, result.1.workers[tid]? = some worker ∧
    match actual.result with
    | .next output => result.2 = .ordinary tid ∧
        worker.phase = .running ∧ localCPU result.1 worker = output
    | .returned output => result.2 = .returned tid ∧
        worker.phase = .returned ∧ localCPU result.1 worker = output
    | .atomic _ _ | .syscall _ => False

/-- Only gates about the current prestate. The existential cursor records real
queue admission, never a guessed successor CPU or a future scheduler success.
The effect policy in a head is separate from these original OS authorities. -/
structure OrdinaryReady (state : S) (tid : Nat) (worker : Worker)
    (instruction : Sequential.Instruction) (profile : Profile := .ownedOnly)
    (family : RMWFamily := .xaddOnly) : Prop where
  live : state.workers[tid]? = some worker
  running : worker.phase = .running
  codeCurrent : LeaseCurrent state.world worker.resources.actor worker.resources.code
  callerCurrent : LeaseCurrent state.world worker.resources.actor worker.resources.caller
  dispatch : decode (fetchCPU state worker) family = .ok (.ordinary instruction)
  admitted : supported instruction = true
  bounds : codeFits worker instruction.length
  reads : ∃ units, (instruction.operandReads (localCPU state worker)).mapM
    (fun read => checkRead state worker read profile) = .ok units
  queue : ∃ update : Queue.Cursor, QueueEffect state worker instruction update profile

/-- The current scheduler's ordinary subset has no vector-only instruction.
This law does not collapse independent flag choices for the extended ISA. -/
theorem supported_boolChoiceProfile {instruction : Sequential.Instruction}
    (admitted : supported instruction = true) : instruction.boolChoiceProfile = true := by
  cases instruction <;> first | exact admitted | rfl

private theorem intent_none {instruction : Sequential.Instruction} {initial : X86.State}
    (intent : storeIntent instruction initial = none) :
    instruction.storeIntent initial = none ∧ instruction.storeIntent64 initial = none := by
  cases wide : instruction.storeIntent64 initial with
  | some pair => simp [storeIntent, wide] at intent
  | none =>
    cases narrow : instruction.storeIntent initial with
    | some pair => simp [storeIntent, wide, narrow] at intent
    | none => exact ⟨rfl, rfl⟩

/-- Delegate extension instructions to their existing full-memory theorem and
legacy instructions to their actual executor. In particular legacy RET is not
treated as a new instruction or as an empty-buffer boundary. -/
private theorem nonstore_next_memory {initial output : X86.State}
    {instruction : Sequential.Instruction} {af : Bool} {actual : Sequential.Observation}
    (noStore : instruction.storeIntent initial = none)
    (noStore64 : instruction.storeIntent64 initial = none)
    (executed : Sequential.execute initial instruction af = .ok actual)
    (next : actual.result = .next output) : output.memory = initial.memory := by
  cases instruction <;> first
  | exact Sequential.execute_new_memory rfl noStore noStore64 executed next
  | rename_i old
    change old.storeIntent initial = none at noStore
    cases legacy : X86.executeInstruction initial old with
    | error fault => simp [Sequential.execute, legacy] at executed
    | ok result =>
      simp only [Sequential.execute, legacy, ok_bind, pure_ok, Except.ok.injEq] at executed
      cases executed
      change result = .next output at next
      rw [next] at legacy
      exact X86.executeInstruction_next_memory noStore legacy

private theorem nonstore_memory {initial output : X86.State}
    {instruction : Sequential.Instruction} {af : Bool} {actual : Sequential.Observation}
    (intent : storeIntent instruction initial = none)
    (executed : Sequential.execute initial instruction af = .ok actual)
    (outcome : actual.result = .next output ∨ actual.result = .returned output) :
    output.memory = initial.memory := by
  obtain ⟨noStore, noStore64⟩ := intent_none intent
  rcases outcome with next | returned
  · exact nonstore_next_memory noStore noStore64 executed next
  · exact Sequential.execute_returned_memory executed returned

/-- A classified store's memory is the production checked DWORD/QWORD update.
Successful store execution also rules out a returned outcome; the argument
does not assume a poststate memory equation or a fresh publication world. -/
private theorem store_memory {initial output : X86.State}
    {instruction : Sequential.Instruction} {af : Bool} {actual : Sequential.Observation}
    {store : Store} (intent : storeIntent instruction initial = some store)
    (executed : Sequential.execute initial instruction af = .ok actual)
    (outcome : actual.result = .next output ∨ actual.result = .returned output) :
    output.memory = store.publish initial.memory := by
  rcases storeIntent_origin intent with ⟨value, width, wide⟩ | ⟨value, width, narrow⟩
  · rw [Sequential.execute_storeIntent64_checked af wide] at executed
    cases allowed : canStoreQWord initial.memory store.address with
    | false => simp [allowed] at executed
    | true =>
      simp only [allowed, ↓reduceIte, Except.ok.injEq] at executed
      cases executed
      rcases outcome with next | returned
      · cases next
        simp only [StoreBuffer.Mixed.Store.publish, width]
      · cases returned
  · rw [Sequential.execute_storeIntent_checked af narrow] at executed
    cases allowed : canStoreDWord initial.memory store.address with
    | false => simp [allowed] at executed
    | true =>
      simp only [allowed, ↓reduceIte, Except.ok.injEq] at executed
      cases executed
      rcases outcome with next | returned
      · cases next
        simp only [StoreBuffer.Mixed.Store.publish, width]
      · cases returned

/-- The discarded executor memory is exactly the actual successor FIFO's view
of the unchanged world. Admission retains the tag and original store operands;
appending a store is one production Mixed update, even with overlapping writes. -/
theorem queue_memory {state : S} {worker : Worker}
    {instruction : Sequential.Instruction} {update : Queue.Cursor} {profile : Profile}
    {af : Bool} {actual : Sequential.Observation} {output : X86.State}
    (queue : QueueEffect state worker instruction update profile)
    (executed : Sequential.execute (localCPU state worker) instruction af = .ok actual)
    (outcome : actual.result = .next output ∨ actual.result = .returned output) :
    StoreBuffer.Mixed.view (published state.world) (payload update.pending) = output.memory := by
  cases queue with
  | unchanged intent => exact (nonstore_memory intent executed outcome).symm
  | enqueued intent admission =>
    rw [OS.TSO64.payload_enqueue, StoreBuffer.Mixed.view_enqueue, admission.store]
    exact (store_memory intent executed outcome).symm

/-- Recover the whole actual successor CPU from ordinary retirement. This uses
the existing queued-store semantics, not a coherence premise. The world is
literally retained; a RET installs its returned context with its pending FIFO. -/
theorem ordinary_reifies {state : S} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {af : Bool} {result : S × O}
    {profile : Profile}
    (live : state.workers[tid]? = some worker)
    (running : worker.phase = .running)
    (effect : OrdinaryEffect state tid worker instruction af result profile) :
    ∃ actual,
      Sequential.stepWith (Sequential.FlagChoices.uniform af) (localCPU state worker) =
        .ok actual ∧
      Reifies tid result actual ∧ result.1.world = state.world := by
  cases effect with
  | @intro update actual _admitted _bounds decoded _reads queue stepped finish =>
    have executed := stepped
    rw [Sequential.step_eq_execute af decoded] at executed
    refine ⟨actual, ?_, ?_, ?_⟩
    · rw [Sequential.stepWith_uniform _ af
        (Sequential.boolChoiceProfile_of_step_success stepped)]
      exact stepped
    · cases finish with
      | @next output _ outcome =>
        have memory := queue_memory queue executed (.inl outcome)
        refine ⟨{ worker with context := .ofCPU output, pending := update.pending, nextStore := update.nextStore }, ?_, ?_⟩
        · exact List.getElem?_set_self (List.getElem_of_getElem? live).1
        · simp only [outcome]
          refine ⟨trivial, running, ?_⟩
          change X86.State.mk output.registers output.rip output.flags
            (StoreBuffer.Mixed.view (published state.world) (payload update.pending)) = output
          rw [memory]
      | @returned output _ outcome =>
        have memory := queue_memory queue executed (.inr outcome)
        refine ⟨{ worker with context := .ofCPU output, phase := .returned, pending := update.pending, nextStore := update.nextStore }, ?_, ?_⟩
        · exact List.getElem?_set_self (List.getElem_of_getElem? live).1
        · simp only [outcome]
          refine ⟨trivial, trivial, ?_⟩
          change X86.State.mk output.registers output.rip output.flags
            (StoreBuffer.Mixed.view (published state.world) (payload update.pending)) = output
          rw [memory]
    · cases finish <;> rfl

/-- Actual legacy RET retains the original resources, pending entries and
occurrence counter, even when its FIFO is nonempty. No caller replacement or
implicit publication is hidden in context installation. -/
theorem ordinary_ret_pending {state : S} {tid : Nat} {worker : Worker}
    {af : Bool} {result : S × O} {profile : Profile}
    (live : state.workers[tid]? = some worker)
    (effect : OrdinaryEffect state tid worker (.legacy .ret) af result profile) :
    ∃ after, result.1.workers[tid]? = some after ∧
      after.resources = worker.resources ∧ after.pending = worker.pending ∧
      after.nextStore = worker.nextStore := by
  cases effect with
  | intro _admitted _bounds _decoded _reads queue _stepped finish =>
    cases queue with
    | enqueued intent _admission =>
      simp [storeIntent, Sequential.Instruction.storeIntent64,
        Sequential.Instruction.storeIntent, X86.Instruction.storeIntent] at intent
    | unchanged _intent =>
      cases finish with
      | @next output _ _outcome =>
        exact ⟨{ worker with context := .ofCPU output },
          List.getElem?_set_self (List.getElem_of_getElem? live).1, rfl, rfl, rfl⟩
      | @returned output _ _outcome =>
        exact ⟨{ worker with context := .ofCPU output, phase := .returned },
          List.getElem?_set_self (List.getElem_of_getElem? live).1, rfl, rfl, rfl⟩

/-- Current ordinary support cannot produce atomic or syscall observations.
New instructions reuse the existing outcome theorem. Legacy cases invert only
the real executor's outcomes; they introduce no evaluator or opcode semantics. -/
private theorem supported_outcome {initial : X86.State}
    {instruction : Sequential.Instruction} {af : Bool} {actual : Sequential.Observation}
    (admitted : supported instruction = true)
    (executed : Sequential.execute initial instruction af = .ok actual) :
    ∃ output, actual.result = .next output ∨ actual.result = .returned output := by
  cases instruction <;> first
  | obtain ⟨output, next⟩ := Sequential.execute_new_next rfl executed
    exact ⟨output, .inl next⟩
  | rename_i old
    cases old with
    | leaEaxRdiDisp8 _ | leaEaxRaxDisp8 _ | cmpEaxZero
    | movEaxEdi | movEaxEsi | mov32 _ _ =>
      cases executed
      exact ⟨_, .inl rfl⟩
    | jrcxz displacement =>
      cases branched : executeJrcxz initial displacement <;>
        simp only [Sequential.execute, X86.executeInstruction, branched, ok_bind,
          error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at executed
      cases executed
      exact ⟨_, .inl rfl⟩
    | loopRcx displacement =>
      cases branched : executeLoop initial displacement <;>
        simp only [Sequential.execute, X86.executeInstruction, branched, ok_bind,
          error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at executed
      cases executed
      exact ⟨_, .inl rfl⟩
    | jnz displacement =>
      cases branched : executeJnz initial displacement <;>
        simp only [Sequential.execute, X86.executeInstruction, branched, ok_bind,
          error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at executed
      cases executed
      exact ⟨_, .inl rfl⟩
    | loadEaxRdi =>
      cases loaded : executeLoad initial <;>
        simp only [Sequential.execute, X86.executeInstruction, loaded, ok_bind,
          error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at executed
      cases executed
      exact ⟨_, .inl rfl⟩
    | loadEaxRsi =>
      cases loaded : executeLoadRsi initial <;>
        simp only [Sequential.execute, X86.executeInstruction, loaded, ok_bind,
          error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at executed
      cases executed
      exact ⟨_, .inl rfl⟩
    | storeEsiRdi =>
      cases stored : executeStore initial <;>
        simp only [Sequential.execute, X86.executeInstruction, stored, ok_bind,
          error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at executed
      cases executed
      exact ⟨_, .inl rfl⟩
    | storeEaxRsi =>
      cases stored : executeStoreRsi initial <;>
        simp only [Sequential.execute, X86.executeInstruction, stored, ok_bind,
          error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at executed
      cases executed
      exact ⟨_, .inl rfl⟩
    | ret =>
      cases returned : executeRet initial <;>
        simp only [Sequential.execute, X86.executeInstruction, returned, ok_bind,
          error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at executed
      cases executed
      exact ⟨_, .inr rfl⟩
    | exchangeEaxRdi | fetchAddEaxRdi | syscall =>
      simp [supported] at admitted

/-- Construct the actual production issue from an existing checked head and
current OS prestate admissions. The bytes/policy remain those of the head;
there is no static-node size bound, successor oracle, or invented world. -/
theorem issue_from_head {state : S} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {af : Bool} {profile : Profile} {family : RMWFamily}
    {bytes : List Byte} {base : Word} {policy : X86.VCGen.Effects.Policy}
    {actual : Sequential.Observation}
    (valid : WellFormed state profile)
    (ready : OrdinaryReady state tid worker instruction profile family)
    (head : X86.VCGen.Effects.Head bytes base policy
      (Sequential.FlagChoices.uniform af) (localCPU state worker) instruction actual) :
    ∃ result : S × O,
      step state (.issue tid af) profile family = .ok result ∧
      Reifies tid result actual ∧ result.1.world = state.world ∧
      WellFormed result.1 profile := by
  obtain ⟨update, queue⟩ := ready.queue
  have executed := head.actual
  rw [Sequential.stepWith_eq_executeWith _ head.decoded,
    Sequential.executeWith_uniform _ _ af (supported_boolChoiceProfile ready.admitted)] at executed
  obtain ⟨output, outcome⟩ := supported_outcome ready.admitted executed
  have finish : ∃ result : S × O,
      FinishEffect state tid worker update.pending actual result update.nextStore := by
    rcases outcome with next | returned
    · exact ⟨(install state tid state.world
        { worker with context := .ofCPU output, pending := update.pending, nextStore := update.nextStore }, .ordinary tid), .next next⟩
    · exact ⟨(install state tid state.world
        { worker with context := .ofCPU output, phase := .returned, pending := update.pending, nextStore := update.nextStore }, .returned tid), .returned returned⟩
  obtain ⟨result, finish⟩ := finish
  have stepped : Sequential.step af (localCPU state worker) = .ok actual := by
    rw [Sequential.step_eq_execute af head.decoded]
    exact executed
  have effect : OrdinaryEffect state tid worker instruction af result profile :=
    .intro ready.admitted ready.bounds head.decoded ready.reads queue stepped finish
  have success : step state (.issue tid af) profile family = .ok result := by
    obtain ⟨units, reads⟩ := ready.reads
    change issue state tid af profile family = .ok result
    simp [issue, ready.live, ready.running, ready.codeCurrent, ready.callerCurrent,
      ready.dispatch, ordinary, ready.admitted, ready.bounds, head.decoded, reads,
      X86.VCGen.ManagedRules.queue_checked queue, executed, Except.mapError,
      X86.VCGen.ManagedRules.finish_checked finish]
  obtain ⟨observed, vector, reified, world⟩ := ordinary_reifies ready.live ready.running effect
  have same : observed = actual := Except.ok.inj (vector.symm.trans head.actual)
  subst observed
  exact ⟨result, success, reified, world, effect.wellFormed valid ready.live⟩

/-- Only the draining worker's whole local CPU stutters. Publication can change
the shared world, so this theorem supplies no general peer-CPU equality. It also applies
after RET, with no phase or empty-buffer premise. -/
theorem drain_localCPU {state : S} {tid : Nat} {worker : Worker}
    {result : S × O} {profile : Profile}
    (live : state.workers[tid]? = some worker)
    (success : drain state tid profile = .ok result) :
    ∃ after, result.1.workers[tid]? = some after ∧
      after.context = worker.context ∧ after.phase = worker.phase ∧
      after.resources = worker.resources ∧ after.nextStore = worker.nextStore ∧
      localCPU result.1 after = localCPU state worker := by
  obtain ⟨prior, _head, tail, world, priorLive, _pending, installed, _projection,
    view, _retired⟩ := drain_fifo success
  have same : prior = worker := Option.some.inj (priorLive.symm.trans live)
  subst prior
  rw [installed]
  refine ⟨{ worker with pending := tail }, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · exact List.getElem?_set_self (List.getElem_of_getElem? live).1
  · change cpu worker (StoreBuffer.Mixed.view (published world) (payload tail)) =
      cpu worker (localCPU state worker).memory
    rw [view]

#print axioms Reifies
#print axioms OrdinaryReady
#print axioms supported_boolChoiceProfile
#print axioms queue_memory
#print axioms ordinary_reifies
#print axioms ordinary_ret_pending
#print axioms issue_from_head
#print axioms drain_localCPU

end EDSL.OS.TSO64.EffectSimulation

#audit_edsl
