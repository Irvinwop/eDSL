/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import EDSL.X86.VCGen.Effects.Checked
import EDSL.OS.TSO64.EffectSimulation.Ordinary
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
One owned synthetic MOV/MOV/MOV/RET body, exercised under both existing
authority profiles. The Effects certificate is about the actual initial local
CPU. Its head is lifted only after supplying current OS admissions separately.
Literal observations test issue without publication, mixed-width forwarding,
RET with pending stores, and oldest-first publication after return.

There is no interpreter or expected-value overlay here: all CPUs and scheduler
checkpoints come from the production executors. Sequential policy predicates
grant no OS authority. These finite tests make no peer-interference, managed
store, atomic-event, fairness, hardware, or corpus claim.

-/

namespace EDSL.Tests.EffectTSO64Simulation
open X86 OS.TSO64 OS.TSO64.EffectSimulation

-- The imported modules provide no general Except equality instance.
-- These finite observations have decidable payloads and faults; keeping this
-- constructive instance local avoids exporting a policy to other modules.
private def exceptDecidableEq {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α) :=
  fun left right =>
    match left, right with
    | .error leftFault, .error rightFault =>
      match decEq leftFault rightFault with
      | .isTrue same => isTrue (congrArg Except.error same)
      | .isFalse different => isFalse (fun same => different (Except.error.inj same))
    | .ok leftValue, .ok rightValue =>
      match decEq leftValue rightValue with
      | .isTrue same => isTrue (congrArg Except.ok same)
      | .isFalse different => isFalse (fun same => different (Except.ok.inj same))
    | .error _, .ok _ => isFalse (fun same => by cases same)
    | .ok _, .error _ => isFalse (fun same => by cases same)

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α) := exceptDecidableEq

private theorem output_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) :
    attempt = .ok (attempt.toOption.get accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private theorem found_ok {α : Type} (value : Option α) (present : value.isSome = true) :
    value = some (value.get present) := by
  cases value with
  | none => cases present
  | some value => rfl

/-- Guarded dispatch has no DecidableEq instance. Inspect only its ordinary
instruction, then construct the exact successful dispatch equation generically. -/
private def ordinarySnapshot (attempt : Except Fault Decoded) : Option Sequential.Instruction :=
  match attempt with
  | .ok (.ordinary instruction) => some instruction
  | _ => none

private theorem ordinary_snapshot (attempt : Except Fault Decoded)
    (instruction : Sequential.Instruction)
    (snapshot : ordinarySnapshot attempt = some instruction) :
    attempt = .ok (.ordinary instruction) := by
  cases attempt with
  | error fault => cases snapshot
  | ok decoded =>
    cases decoded with
    | ordinary current =>
      have same : current = instruction := Option.some.inj snapshot
      cases same
      rfl
    | locked current => cases snapshot

/-- Observe an actual executor result without comparing functional CPU fields.
The elimination lemmas below retain that same output as their witness. -/
private def nextSnapshot {α : Type} (observe : X86.State → α)
    (attempt : Except Error Sequential.Observation) : Option (List Sequential.Read × α) :=
  match attempt with
  | .ok ⟨.next output, reads⟩ => some (reads, observe output)
  | _ => none

private theorem next_snapshot {α : Type} (observe : X86.State → α)
    (attempt : Except Error Sequential.Observation) (reads : List Sequential.Read) (value : α)
    (snapshot : nextSnapshot observe attempt = some (reads, value)) :
    ∃ output : X86.State, attempt = .ok ⟨.next output, reads⟩ ∧ observe output = value := by
  cases attempt with
  | error fault => cases snapshot
  | ok actual =>
    rcases actual with ⟨outcome, actualReads⟩
    cases outcome with
    | next output =>
      have fields : actualReads = reads ∧ observe output = value :=
        Prod.mk.inj (Option.some.inj snapshot)
      rcases fields with ⟨readsEq, valueEq⟩
      cases readsEq
      exact ⟨output, rfl, valueEq⟩
    | atomic event output => cases snapshot
    | returned output => cases snapshot
    | syscall request => cases snapshot

private def returnedSnapshot {α : Type} (observe : X86.State → α)
    (attempt : Except Error Sequential.Observation) : Option (List Sequential.Read × α) :=
  match attempt with
  | .ok ⟨.returned output, reads⟩ => some (reads, observe output)
  | _ => none

private theorem returned_snapshot {α : Type} (observe : X86.State → α)
    (attempt : Except Error Sequential.Observation) (reads : List Sequential.Read) (value : α)
    (snapshot : returnedSnapshot observe attempt = some (reads, value)) :
    ∃ output : X86.State, attempt = .ok ⟨.returned output, reads⟩ ∧ observe output = value := by
  cases attempt with
  | error fault => cases snapshot
  | ok actual =>
    rcases actual with ⟨outcome, actualReads⟩
    cases outcome with
    | next output => cases snapshot
    | atomic event output => cases snapshot
    | returned output =>
      have fields : actualReads = reads ∧ observe output = value :=
        Prod.mk.inj (Option.some.inj snapshot)
      rcases fields with ⟨readsEq, valueEq⟩
      cases readsEq
      exact ⟨output, rfl, valueEq⟩
    | syscall request => cases snapshot

/-- Project the authority invariant while the state and worker are unknown.
Applying this lemma does not normalize the resource-manager fixture. -/
private theorem current_leases {state : OS.TSO64.State} {worker : Worker}
    {tid : Nat} {profile : Profile} (valid : WellFormed state profile)
    (live : state.workers[tid]? = some worker) :
    LeaseCurrent state.world worker.resources.actor worker.resources.code ∧
      LeaseCurrent state.world worker.resources.actor worker.resources.caller := by
  have workerValid : WorkerValid state.world worker profile :=
    valid.2 worker (List.mem_of_getElem? live)
  exact ⟨workerValid.1.1, workerValid.1.2.1⟩

private structure Prepared where
  state : OS.TSO64.State
  valid : ∀ profile : Profile, WellFormed state profile

/-- Reuse the checked manager fixture and the actual attach/WF theorem. Only
one worker is needed; its code and ORIGINAL return-slot loans are retained. -/
private def setup : Except Fault Prepared := do
  let ready ← (TSO64.fixture 0x1a8b480189328948 0x90909090909090c3 19).mapError Fault.os
  match attached : attach ⟨ready.checked.world, []⟩ 11
      (TSO64.context 262144 131072 0x1122334455667788 0xdeadbeef)
      ready.codeA ready.callerA [ready.dataA] [ready.atomicA] with
  | .error fault => .error fault
  | .ok state => .ok ⟨state, fun profile =>
      attach_valid_for profile ⟨ready.checked.valid, by simp⟩ attached⟩

private theorem setup_present : setup.toOption.isSome = true := by decide +kernel
private def prepared : Prepared := setup.toOption.get setup_present
private def initial : OS.TSO64.State := prepared.state
private theorem initial_present : (initial.workers[0]?).isSome = true := by decide +kernel
private def initialWorker : Worker := (initial.workers[0]?).get initial_present

private theorem initial_live : initial.workers[0]? = some initialWorker :=
  found_ok (α := Worker) (initial.workers[0]?) initial_present

private theorem initial_valid (profile : Profile) : WellFormed initial profile :=
  prepared.valid profile

/-- MOV [RDX],RSI; MOV [RCX],EAX; MOV RBX,[RDX]; RET.
RCX initially points four bytes into the owned qword at RDX. -/
private def bytes : List Byte := [0x48, 0x89, 0x32, 0x89, 0x01, 0x48, 0x8b, 0x1a, 0xc3]

private def graph : Sequential.CFG.Graph := ⟨[
  ⟨0, .storeMem64 (.base .rdx) .rsi, true, 3⟩,
  ⟨3, .storeMem32 (.base .rcx) .rax, false, 2⟩,
  ⟨5, .loadMem64 .rbx (.base .rdx), false, 1⟩,
  ⟨8, .legacy .ret, false, 0⟩], 3⟩

private abbrev entry : graph.Index := ⟨0, by decide +kernel⟩
private def Current (_ : X86.State) : Prop := True
private def AllowedRead (_ : X86.State) (_ : Sequential.Read) : Prop := True
private def decCurrent (state : X86.State) : Decidable (Current state) := isTrue trivial
private def decReads (state : X86.State) (read : Sequential.Read) :
    Decidable (AllowedRead state read) := isTrue trivial

/-- Independent full-width loaded result, original stack return, instruction
cost and actual read order. Ordinary stores produce no atomic events. -/
private def Post (result : Sequential.Result) (events : List AtomicEvent) : Prop :=
  result.state.registers .rbx = 0xdeadbeef55667788 ∧
  result.state.rip = 0x7000 ∧ result.state.registers .rsp = 262152 ∧
  result.instructions = 4 ∧
  result.reads = [⟨.data, 131072, 8⟩, ⟨.stack, 262144, 8⟩] ∧ events = []

private def decPost (result : Sequential.Result) (events : List AtomicEvent) :
    Decidable (Post result events) := by
  unfold Post
  infer_instance

private def certified : Bool :=
  VCGen.Effects.certifySeparated bytes graph 393216 Current AllowedRead decCurrent decReads
    4 entry (localCPU initial initialWorker) Post decPost

theorem bounded_effects_accepted : certified = true := by decide +kernel

/-- These are prestate gates, not a premise that a chosen issue will succeed.
The queue witness is obtained from actual current production admission. -/
private theorem initial_ready (profile : Profile) :
    OrdinaryReady initial 0 initialWorker (.storeMem64 (.base .rdx) .rsi) profile := by
  have leases : LeaseCurrent initial.world initialWorker.resources.actor initialWorker.resources.code ∧
      LeaseCurrent initial.world initialWorker.resources.actor initialWorker.resources.caller :=
    current_leases (state := initial) (worker := initialWorker) (tid := 0) (profile := profile)
      (initial_valid profile) initial_live
  refine {
    live := initial_live
    running := ?_
    codeCurrent := leases.1
    callerCurrent := leases.2
    dispatch := ?_
    admitted := rfl
    bounds := ?_
    reads := ?_
    queue := ?_
  }
  · decide +kernel
  · exact ordinary_snapshot (decode (fetchCPU initial initialWorker))
      (.storeMem64 (.base .rdx) .rsi) (by decide +kernel)
  · decide +kernel
  · exact ⟨[], rfl⟩
  · let attempt : Except Fault Queue.Cursor :=
      prepareQueue initial initialWorker (.storeMem64 (.base .rdx) .rsi) profile
    have admitted : attempt.toOption.isSome = true := by
      cases profile <;> decide +kernel
    exact ⟨attempt.toOption.get admitted,
      prepareQueue_effect (state := initial) (worker := initialWorker)
        (instruction := .storeMem64 (.base .rdx) .rsi)
        (update := attempt.toOption.get admitted) (profile := profile)
        (output_ok (ε := Fault) (α := Queue.Cursor) attempt admitted)⟩

-- Extract only successful outputs of actual scheduler actions. Their Boolean
-- existence checks are setup obligations, not independent behavioral tests.
private theorem qword_present (profile : Profile) :
    (step initial (.issue 0 false) profile).toOption.isSome = true := by
  cases profile <;> decide +kernel

private def qword (profile : Profile) : OS.TSO64.State × Observation :=
  (step initial (.issue 0 false) profile).toOption.get (qword_present profile)

private theorem qword_actual (profile : Profile) :
    step initial (.issue 0 false) profile = .ok (qword profile) :=
  output_ok (ε := Fault) (α := OS.TSO64.State × Observation)
    (step initial (.issue 0 false) profile) (qword_present profile)

private theorem highDWord_present (profile : Profile) :
    (step (qword profile).1 (.issue 0 true) profile).toOption.isSome = true := by
  cases profile <;> decide +kernel

private def highDWord (profile : Profile) : OS.TSO64.State × Observation :=
  (step (qword profile).1 (.issue 0 true) profile).toOption.get
    (highDWord_present profile)

private theorem highDWord_actual (profile : Profile) :
    step (qword profile).1 (.issue 0 true) profile = .ok (highDWord profile) :=
  output_ok (ε := Fault) (α := OS.TSO64.State × Observation)
    (step (qword profile).1 (.issue 0 true) profile) (highDWord_present profile)

private theorem loaded_present (profile : Profile) :
    (step (highDWord profile).1 (.issue 0 true) profile).toOption.isSome = true := by
  cases profile <;> decide +kernel

private def loaded (profile : Profile) : OS.TSO64.State × Observation :=
  (step (highDWord profile).1 (.issue 0 true) profile).toOption.get
    (loaded_present profile)

private theorem loaded_actual (profile : Profile) :
    step (highDWord profile).1 (.issue 0 true) profile = .ok (loaded profile) :=
  output_ok (ε := Fault) (α := OS.TSO64.State × Observation)
    (step (highDWord profile).1 (.issue 0 true) profile) (loaded_present profile)

private theorem returned_present (profile : Profile) :
    (step (loaded profile).1 (.issue 0 false) profile).toOption.isSome = true := by
  cases profile <;> decide +kernel

private def returned (profile : Profile) : OS.TSO64.State × Observation :=
  (step (loaded profile).1 (.issue 0 false) profile).toOption.get
    (returned_present profile)

private theorem returned_actual (profile : Profile) :
    step (loaded profile).1 (.issue 0 false) profile = .ok (returned profile) :=
  output_ok (ε := Fault) (α := OS.TSO64.State × Observation)
    (step (loaded profile).1 (.issue 0 false) profile) (returned_present profile)

private theorem firstDrain_present (profile : Profile) :
    (drain (returned profile).1 0 profile).toOption.isSome = true := by
  cases profile <;> decide +kernel

private def firstDrain (profile : Profile) : OS.TSO64.State × Observation :=
  (drain (returned profile).1 0 profile).toOption.get (firstDrain_present profile)

private theorem firstDrain_actual (profile : Profile) :
    drain (returned profile).1 0 profile = .ok (firstDrain profile) :=
  output_ok (ε := Fault) (α := OS.TSO64.State × Observation)
    (drain (returned profile).1 0 profile) (firstDrain_present profile)

private theorem finalDrain_present (profile : Profile) :
    (drain (firstDrain profile).1 0 profile).toOption.isSome = true := by
  cases profile <;> decide +kernel

private def finalDrain (profile : Profile) : OS.TSO64.State × Observation :=
  (drain (firstDrain profile).1 0 profile).toOption.get (finalDrain_present profile)

private theorem finalDrain_actual (profile : Profile) :
    drain (firstDrain profile).1 0 profile = .ok (finalDrain profile) :=
  output_ok (ε := Fault) (α := OS.TSO64.State × Observation)
    (drain (firstDrain profile).1 0 profile) (finalDrain_present profile)

/-- Invert a real issue at its current guarded dispatch. This avoids asking
definitional equality to compare entire functional scheduler output states. -/
private theorem actual_ordinary {state : OS.TSO64.State} {worker : Worker} {tid : Nat}
    {instruction : Sequential.Instruction} {af : Bool} {result : OS.TSO64.State × Observation}
    {profile : Profile} (live : state.workers[tid]? = some worker)
    (dispatch : decode (fetchCPU state worker) = .ok (.ordinary instruction))
    (success : step state (.issue tid af) profile = .ok result) :
    OrdinaryEffect state tid worker instruction af result profile := by
  obtain ⟨current, currentLive, _running, _code, _caller, decoded, fetched, effect⟩ :=
    issue_effect success
  have workerEq := Option.some.inj (currentLive.symm.trans live)
  subst current
  have instructionEq := Except.ok.inj (fetched.symm.trans dispatch)
  subst decoded
  exact effect

/-- Align indices using actual decode and execution equations before applying
the bridge. Neither the state nor the existential CPU is normalized here. -/
private theorem head_of_steps {code : List Byte} {base : Word}
    {policy : VCGen.Effects.Policy} {choice : Sequential.FlagChoices} {before : X86.State}
    {instruction : Sequential.Instruction} {actual : Sequential.Observation}
    (available : ∃ decoded observed,
      VCGen.Effects.Head code base policy choice before decoded observed)
    (decoded : Sequential.decodeAt before = .ok instruction)
    (executed : Sequential.stepWith choice before = .ok actual) :
    VCGen.Effects.Head code base policy choice before instruction actual := by
  obtain ⟨oldInstruction, oldActual, head⟩ := available
  have instructionEq : oldInstruction = instruction :=
    Except.ok.inj (head.decoded.symm.trans decoded)
  have actualEq : oldActual = actual := Except.ok.inj (head.actual.symm.trans executed)
  subst oldInstruction
  subst oldActual
  exact head

private theorem ordinary_observed {state : OS.TSO64.State} {worker : Worker} {tid : Nat}
    {instruction : Sequential.Instruction} {af : Bool} {result : OS.TSO64.State × Observation}
    {profile : Profile} {actual : Sequential.Observation}
    (live : state.workers[tid]? = some worker) (running : worker.phase = .running)
    (effect : OrdinaryEffect state tid worker instruction af result profile)
    (executed : Sequential.stepWith (Sequential.FlagChoices.uniform af) (localCPU state worker) =
      .ok actual) :
    Reifies tid result actual ∧ result.1.world = state.world := by
  obtain ⟨observed, vector, reified, world⟩ := ordinary_reifies live running effect
  have same : observed = actual := Except.ok.inj (vector.symm.trans executed)
  subst observed
  exact ⟨reified, world⟩

/-- Eliminate reification and transfer finite observations with unknown result
states. Concrete clients supply production equations and independent literals. -/
private theorem checked_next_word {state : OS.TSO64.State} {worker : Worker} {tid : Nat}
    {instruction : Sequential.Instruction} {af : Bool} {result : OS.TSO64.State × Observation}
    {profile : Profile} {code : List Byte} {base : Word} {policy : VCGen.Effects.Policy}
    {output : X86.State} {reads : List Sequential.Read} {address old value : Word}
    (valid : WellFormed state profile)
    (ready : OrdinaryReady state tid worker instruction profile)
    (head : VCGen.Effects.Head code base policy (Sequential.FlagChoices.uniform af)
      (localCPU state worker) instruction ⟨.next output, reads⟩)
    (issued : step state (.issue tid af) profile = .ok result)
    (publishedWord : loadQWord (published state.world) address = .ok old)
    (word : loadQWord output.memory address = .ok value) :
    ∃ after : Worker, result.1.workers[tid]? = some after ∧
      result.2 = .ordinary tid ∧ WellFormed result.1 profile ∧
      result.1.world = state.world ∧
      loadQWord (published result.1.world) address = .ok old ∧
      loadQWord (localCPU result.1 after).memory address = .ok value := by
  obtain ⟨produced, checked, reified, world, preserved⟩ :=
    issue_from_head valid ready head
  have same : produced = result := Except.ok.inj (checked.symm.trans issued)
  subst produced
  obtain ⟨after, live, coherence⟩ := reified
  change result.2 = .ordinary tid ∧ after.phase = .running ∧
    localCPU result.1 after = output at coherence
  refine ⟨after, live, coherence.1, preserved, world, ?_, ?_⟩
  · rw [world]
    exact publishedWord
  · rw [coherence.2.2]
    exact word

private theorem next_word {result : OS.TSO64.State × Observation} {tid : Nat}
    {before : World} {output : X86.State} {reads : List Sequential.Read} {address value : Word}
    (reified : Reifies tid result ⟨.next output, reads⟩)
    (world : result.1.world = before) (word : loadQWord output.memory address = .ok value) :
    ∃ after : Worker, result.1.workers[tid]? = some after ∧ result.2 = .ordinary tid ∧
      result.1.world = before ∧
      loadQWord (localCPU result.1 after).memory address = .ok value := by
  obtain ⟨after, live, coherence⟩ := reified
  change result.2 = .ordinary tid ∧ after.phase = .running ∧
    localCPU result.1 after = output at coherence
  refine ⟨after, live, coherence.1, world, ?_⟩
  rw [coherence.2.2]
  exact word

private theorem next_register_published {result : OS.TSO64.State × Observation} {tid : Nat}
    {before : World} {output : X86.State} {reads : List Sequential.Read}
    {register : Register} {value address old : Word}
    (reified : Reifies tid result ⟨.next output, reads⟩)
    (world : result.1.world = before) (observed : output.registers register = value)
    (publishedWord : loadQWord (published before) address = .ok old) :
    ∃ after : Worker, result.1.workers[tid]? = some after ∧ result.2 = .ordinary tid ∧
      after.context.registers register = value ∧ result.1.world = before ∧
      loadQWord (published result.1.world) address = .ok old := by
  obtain ⟨after, live, coherence⟩ := reified
  change result.2 = .ordinary tid ∧ after.phase = .running ∧
    localCPU result.1 after = output at coherence
  refine ⟨after, live, coherence.1, ?_, world, ?_⟩
  · change (localCPU result.1 after).registers register = value
    rw [coherence.2.2]
    exact observed
  · rw [world]
    exact publishedWord

private structure ReturnSummary where
  rbx : Word
  rip : Word
  rsp : Word
  word : Except Error Word
  deriving DecidableEq

private def returnSummary (output : X86.State) (address : Word) : ReturnSummary :=
  ⟨output.registers .rbx, output.rip, output.registers .rsp, loadQWord output.memory address⟩

private theorem returned_observations {result : OS.TSO64.State × Observation} {tid : Nat}
    {output : X86.State} {reads : List Sequential.Read} {address value pc stack word : Word}
    (reified : Reifies tid result ⟨.returned output, reads⟩)
    (snapshot : returnSummary output address = ⟨value, pc, stack, .ok word⟩) :
    ∃ after : Worker, result.1.workers[tid]? = some after ∧ result.2 = .returned tid ∧
      after.phase = .returned ∧ after.context.registers .rbx = value ∧
      after.context.rip = pc ∧ after.context.registers .rsp = stack ∧
      loadQWord (localCPU result.1 after).memory address = .ok word := by
  obtain ⟨after, live, coherence⟩ := reified
  change result.2 = .returned tid ∧ after.phase = .returned ∧
    localCPU result.1 after = output at coherence
  refine ⟨after, live, coherence.1, coherence.2.1, ?_, ?_, ?_, ?_⟩
  · change (localCPU result.1 after).registers .rbx = value
    rw [coherence.2.2]
    exact congrArg ReturnSummary.rbx snapshot
  · change (localCPU result.1 after).rip = pc
    rw [coherence.2.2]
    exact congrArg ReturnSummary.rip snapshot
  · change (localCPU result.1 after).registers .rsp = stack
    rw [coherence.2.2]
    exact congrArg ReturnSummary.rsp snapshot
  · rw [coherence.2.2]
    exact congrArg ReturnSummary.word snapshot

/-- Consume the accepted trace's first-step view and constructive issue bridge.
Whole-CPU equality transfers the production vector store's independently
specified qword to the scheduler's local view; the world still contains zero. -/
theorem checked_head_lifts_without_publication (profile : Profile) :
    ∃ worker, (qword profile).1.workers[0]? = some worker ∧
      (qword profile).2 = .ordinary 0 ∧ WellFormed (qword profile).1 profile ∧
      (qword profile).1.world = initial.world ∧
      loadQWord (published (qword profile).1.world) 131072 = .ok 0 ∧
      loadQWord (localCPU (qword profile).1 worker).memory 131072 =
        .ok 0x1122334455667788 := by
  obtain ⟨_, _, _, _, _, trace⟩ :=
    VCGen.Effects.certifySeparated_sound bytes graph 393216 Current AllowedRead decCurrent
      decReads 4 entry (localCPU initial initialWorker) Post decPost bounded_effects_accepted
      (fun _ => Sequential.FlagChoices.uniform false)
  have decoded : Sequential.decodeAt (localCPU initial initialWorker) =
      .ok (.storeMem64 (.base .rdx) .rsi) := by decide +kernel
  have snapshot : nextSnapshot (fun output => loadQWord output.memory 131072)
      (Sequential.stepWith (Sequential.FlagChoices.uniform false) (localCPU initial initialWorker)) =
        some ([], .ok 0x1122334455667788) := by decide +kernel
  obtain ⟨output, actual, word⟩ := next_snapshot (α := Except Error Word)
    (fun output => loadQWord output.memory 131072)
    (Sequential.stepWith (Sequential.FlagChoices.uniform false) (localCPU initial initialWorker))
    [] (.ok 0x1122334455667788) snapshot
  have head : VCGen.Effects.Head bytes 393216
      (VCGen.Effects.codeSeparatedPolicy bytes 393216 Current AllowedRead)
      (Sequential.FlagChoices.uniform false) (localCPU initial initialWorker)
      (.storeMem64 (.base .rdx) .rsi) ⟨.next output, []⟩ :=
    head_of_steps (code := bytes) (base := 393216)
      (policy := VCGen.Effects.codeSeparatedPolicy bytes 393216 Current AllowedRead)
      (choice := Sequential.FlagChoices.uniform false) (before := localCPU initial initialWorker)
      (instruction := .storeMem64 (.base .rdx) .rsi) (actual := ⟨.next output, []⟩)
      trace.head decoded actual
  have publishedWord : loadQWord (published initial.world) 131072 = .ok 0 := by decide +kernel
  exact checked_next_word (state := initial) (worker := initialWorker) (tid := 0)
    (instruction := .storeMem64 (.base .rdx) .rsi) (af := false)
    (result := qword profile) (profile := profile) (code := bytes) (base := 393216)
    (policy := VCGen.Effects.codeSeparatedPolicy bytes 393216 Current AllowedRead)
    (output := output) (reads := []) (address := 131072) (old := 0) (value := 0x1122334455667788)
    (initial_valid profile) (initial_ready profile) head (qword_actual profile) publishedWord word

private theorem dword_present (profile : Profile) :
    ((qword profile).1.workers[0]?).isSome = true := by cases profile <;> decide +kernel

private def dwordWorker (profile : Profile) : Worker :=
  ((qword profile).1.workers[0]?).get (dword_present profile)

private theorem dword_live (profile : Profile) :
    (qword profile).1.workers[0]? = some (dwordWorker profile) :=
  found_ok (α := Worker) ((qword profile).1.workers[0]?) (dword_present profile)

/-- The bridge's DWORD enqueue branch must reconstruct the overlapping write,
not only preserve a later load's context. The older qword supplies the low half. -/
theorem high_dword_reifies_merged_memory (profile : Profile) :
    ∃ worker, (highDWord profile).1.workers[0]? = some worker ∧
      (highDWord profile).2 = .ordinary 0 ∧
      (highDWord profile).1.world = (qword profile).1.world ∧
      loadQWord (localCPU (highDWord profile).1 worker).memory 131072 =
        .ok 0xdeadbeef55667788 := by
  have dispatch : decode (fetchCPU (qword profile).1 (dwordWorker profile)) =
      .ok (.ordinary (.storeMem32 (.base .rcx) .rax)) :=
    ordinary_snapshot (decode (fetchCPU (qword profile).1 (dwordWorker profile)))
      (.storeMem32 (.base .rcx) .rax) (by cases profile <;> decide +kernel)
  have effect : OrdinaryEffect (qword profile).1 0 (dwordWorker profile)
      (.storeMem32 (.base .rcx) .rax) true (highDWord profile) profile :=
    actual_ordinary (state := (qword profile).1) (worker := dwordWorker profile) (tid := 0)
      (instruction := .storeMem32 (.base .rcx) .rax) (af := true)
      (result := highDWord profile) (profile := profile)
      (dword_live profile) dispatch (highDWord_actual profile)
  have running : (dwordWorker profile).phase = .running := by cases profile <;> decide +kernel
  have snapshot : nextSnapshot (fun output => loadQWord output.memory 131072)
      (Sequential.stepWith (Sequential.FlagChoices.uniform true)
        (localCPU (qword profile).1 (dwordWorker profile))) =
          some ([], .ok 0xdeadbeef55667788) := by cases profile <;> decide +kernel
  obtain ⟨output, executed, memory⟩ := next_snapshot (α := Except Error Word)
    (fun output => loadQWord output.memory 131072)
    (Sequential.stepWith (Sequential.FlagChoices.uniform true)
      (localCPU (qword profile).1 (dwordWorker profile))) [] (.ok 0xdeadbeef55667788) snapshot
  have coherence : Reifies 0 (highDWord profile) ⟨.next output, []⟩ ∧
      (highDWord profile).1.world = (qword profile).1.world :=
    ordinary_observed (state := (qword profile).1) (worker := dwordWorker profile) (tid := 0)
      (instruction := .storeMem32 (.base .rcx) .rax) (af := true)
      (result := highDWord profile) (profile := profile) (actual := ⟨.next output, []⟩)
      (dword_live profile) running effect executed
  exact next_word (result := highDWord profile) (tid := 0) (before := (qword profile).1.world)
    (output := output) (reads := []) (address := 131072) (value := 0xdeadbeef55667788)
    coherence.1 coherence.2 memory

private theorem load_present (profile : Profile) :
    ((highDWord profile).1.workers[0]?).isSome = true := by cases profile <;> decide +kernel

private def loadWorker (profile : Profile) : Worker :=
  ((highDWord profile).1.workers[0]?).get (load_present profile)

private theorem load_live (profile : Profile) :
    (highDWord profile).1.workers[0]? = some (loadWorker profile) :=
  found_ok (α := Worker) ((highDWord profile).1.workers[0]?) (load_present profile)

/-- Exercise ordinary_reifies at the actual resumed CPU with BOTH entries
pending. A literal vector-executor load and its read observation are transferred
through the bridge to RBX in the installed scheduler context. -/
theorem actual_load_reifies_merged_qword (profile : Profile) :
    ∃ worker, (loaded profile).1.workers[0]? = some worker ∧
      (loaded profile).2 = .ordinary 0 ∧
      worker.context.registers .rbx = 0xdeadbeef55667788 ∧
      (loaded profile).1.world = (highDWord profile).1.world ∧
      loadQWord (published (loaded profile).1.world) 131072 = .ok 0 := by
  have dispatch : decode (fetchCPU (highDWord profile).1 (loadWorker profile)) =
      .ok (.ordinary (.loadMem64 .rbx (.base .rdx))) :=
    ordinary_snapshot (decode (fetchCPU (highDWord profile).1 (loadWorker profile)))
      (.loadMem64 .rbx (.base .rdx)) (by cases profile <;> decide +kernel)
  have effect : OrdinaryEffect (highDWord profile).1 0 (loadWorker profile)
      (.loadMem64 .rbx (.base .rdx)) true (loaded profile) profile :=
    actual_ordinary (state := (highDWord profile).1) (worker := loadWorker profile) (tid := 0)
      (instruction := .loadMem64 .rbx (.base .rdx)) (af := true)
      (result := loaded profile) (profile := profile)
      (load_live profile) dispatch (loaded_actual profile)
  have running : (loadWorker profile).phase = .running := by cases profile <;> decide +kernel
  have snapshot : nextSnapshot (fun output => output.registers .rbx)
      (Sequential.stepWith (Sequential.FlagChoices.uniform true)
        (localCPU (highDWord profile).1 (loadWorker profile))) =
          some ([⟨.data, 131072, 8⟩], 0xdeadbeef55667788) := by
    cases profile <;> decide +kernel
  obtain ⟨output, executed, value⟩ := next_snapshot (α := Word)
    (fun output => output.registers .rbx)
    (Sequential.stepWith (Sequential.FlagChoices.uniform true)
      (localCPU (highDWord profile).1 (loadWorker profile)))
    [⟨.data, 131072, 8⟩] 0xdeadbeef55667788 snapshot
  have coherence : Reifies 0 (loaded profile) ⟨.next output, [⟨.data, 131072, 8⟩]⟩ ∧
      (loaded profile).1.world = (highDWord profile).1.world :=
    ordinary_observed (state := (highDWord profile).1) (worker := loadWorker profile) (tid := 0)
      (instruction := .loadMem64 .rbx (.base .rdx)) (af := true)
      (result := loaded profile) (profile := profile)
      (actual := ⟨.next output, [⟨.data, 131072, 8⟩]⟩)
      (load_live profile) running effect executed
  have publishedWord : loadQWord (published (highDWord profile).1.world) 131072 = .ok 0 := by
    cases profile <;> decide +kernel
  exact next_register_published (result := loaded profile) (tid := 0)
    (before := (highDWord profile).1.world) (output := output) (reads := [⟨.data, 131072, 8⟩])
    (register := .rbx) (value := 0xdeadbeef55667788) (address := 131072) (old := 0)
    coherence.1 coherence.2 value publishedWord

private theorem ret_present (profile : Profile) :
    ((loaded profile).1.workers[0]?).isSome = true := by cases profile <;> decide +kernel

private def retWorker (profile : Profile) : Worker :=
  ((loaded profile).1.workers[0]?).get (ret_present profile)

private theorem ret_live (profile : Profile) :
    (loaded profile).1.workers[0]? = some (retWorker profile) :=
  found_ok (α := Worker) ((loaded profile).1.workers[0]?) (ret_present profile)

/-- RET uses the original stack slot, advances RSP and retains the forwarded
memory. This consumes the returned branch of ordinary_reifies, not just MOV's
next branch or a pre-existing scheduler fixture's return snapshot. -/
theorem actual_ret_reifies_original_return (profile : Profile) :
    ∃ worker, (returned profile).1.workers[0]? = some worker ∧
      (returned profile).2 = .returned 0 ∧ worker.phase = .returned ∧
      worker.context.registers .rbx = 0xdeadbeef55667788 ∧
      worker.context.rip = 0x7000 ∧ worker.context.registers .rsp = 262152 ∧
      loadQWord (localCPU (returned profile).1 worker).memory 131072 =
        .ok 0xdeadbeef55667788 := by
  have dispatch : decode (fetchCPU (loaded profile).1 (retWorker profile)) =
      .ok (.ordinary (.legacy .ret)) :=
    ordinary_snapshot (decode (fetchCPU (loaded profile).1 (retWorker profile)))
      (.legacy .ret) (by cases profile <;> decide +kernel)
  have effect : OrdinaryEffect (loaded profile).1 0 (retWorker profile)
      (.legacy .ret) false (returned profile) profile :=
    actual_ordinary (state := (loaded profile).1) (worker := retWorker profile) (tid := 0)
      (instruction := .legacy .ret) (af := false) (result := returned profile) (profile := profile)
      (ret_live profile) dispatch (returned_actual profile)
  have running : (retWorker profile).phase = .running := by cases profile <;> decide +kernel
  have snapshot : returnedSnapshot (fun output => returnSummary output 131072)
      (Sequential.stepWith (Sequential.FlagChoices.uniform false)
        (localCPU (loaded profile).1 (retWorker profile))) =
          some ([⟨.stack, 262144, 8⟩],
            ⟨0xdeadbeef55667788, 0x7000, 262152, .ok 0xdeadbeef55667788⟩) := by
    cases profile <;> decide +kernel
  obtain ⟨output, executed, observations⟩ := returned_snapshot (α := ReturnSummary)
    (fun output => returnSummary output 131072)
    (Sequential.stepWith (Sequential.FlagChoices.uniform false)
      (localCPU (loaded profile).1 (retWorker profile))) [⟨.stack, 262144, 8⟩]
    ⟨0xdeadbeef55667788, 0x7000, 262152, .ok 0xdeadbeef55667788⟩ snapshot
  have coherence : Reifies 0 (returned profile) ⟨.returned output, [⟨.stack, 262144, 8⟩]⟩ ∧
      (returned profile).1.world = (loaded profile).1.world :=
    ordinary_observed (state := (loaded profile).1) (worker := retWorker profile) (tid := 0)
      (instruction := .legacy .ret) (af := false) (result := returned profile) (profile := profile)
      (actual := ⟨.returned output, [⟨.stack, 262144, 8⟩]⟩)
      (ret_live profile) running effect executed
  exact returned_observations (result := returned profile) (tid := 0) (output := output)
    (reads := [⟨.stack, 262144, 8⟩]) (address := 131072) (value := 0xdeadbeef55667788)
    (pc := 0x7000) (stack := 262152) (word := 0xdeadbeef55667788) coherence.1 observations

private structure PublicationSummary where
  ram : Except Error Word
  phase : Option Phase
  pending : Option Nat
  collected : Except Fault Word
  drained : Option (Nat × Word × StoreBuffer.Mixed.Value)
  retired : Nat
  deriving DecidableEq

private def publicationSummary (result : OS.TSO64.State × Observation) : PublicationSummary where
  ram := loadQWord (published result.1.world) 131072
  phase := result.1.workers[0]?.map Worker.phase
  pending := result.1.workers[0]?.map (fun worker => worker.pending.length)
  collected := collect result.1 0
  drained := match result.2 with
    | .drained tid entry => some (tid, entry.store.address, entry.store.value)
    | _ => none
  retired := result.2.retired

/-- Real RET is visible with two pending stores and unchanged global RAM.
Collection remains denied after only the oldest full-width store publishes;
the final DWORD drain merges its four bytes and enables collection. -/
theorem fifo_publication_and_collection (profile : Profile) :
    publicationSummary (returned profile) =
      ⟨.ok 0, some .returned, some 2, .error .resource, none, 1⟩ ∧
    publicationSummary (firstDrain profile) =
      ⟨.ok 0x1122334455667788, some .returned, some 1, .error .resource,
        some (0, 131072, .qword 0x1122334455667788), 0⟩ ∧
    publicationSummary (finalDrain profile) =
      ⟨.ok 0xdeadbeef55667788, some .returned, some 0, .ok 0xdeadbeef,
        some (0, 131076, .dword 0xdeadbeef), 0⟩ := by
  cases profile <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Compose both production drain equalities before substituting any concrete
scheduler checkpoints. This also keeps context projection reduction shallow. -/
private theorem two_drains_keep_returned
    {before first last : OS.TSO64.State × Observation} {tid : Nat} {profile : Profile}
    {address value pc stack word : Word}
    (retired : ∃ worker : Worker, before.1.workers[tid]? = some worker ∧
      before.2 = .returned tid ∧ worker.phase = .returned ∧
      worker.context.registers .rbx = value ∧ worker.context.rip = pc ∧
      worker.context.registers .rsp = stack ∧
      loadQWord (localCPU before.1 worker).memory address = .ok word)
    (firstActual : drain before.1 tid profile = .ok first)
    (lastActual : drain first.1 tid profile = .ok last) :
    ∃ middle final : Worker,
      first.1.workers[tid]? = some middle ∧ last.1.workers[tid]? = some final ∧
      middle.phase = .returned ∧ final.phase = .returned ∧
      loadQWord (localCPU first.1 middle).memory address = .ok word ∧
      loadQWord (localCPU last.1 final).memory address = .ok word ∧
      middle.context.registers .rbx = value ∧ final.context.registers .rbx = value := by
  obtain ⟨worker, live, _label, phase, register, _pc, _stack, memory⟩ := retired
  obtain ⟨middle, middleLive, contextOne, phaseOne, _resourcesOne, _counterOne, cpuOne⟩ :=
    drain_localCPU (state := before.1) (tid := tid) (worker := worker)
      (result := first) (profile := profile) live firstActual
  obtain ⟨final, finalLive, contextTwo, phaseTwo, _resourcesTwo, _counterTwo, cpuTwo⟩ :=
    drain_localCPU (state := first.1) (tid := tid) (worker := middle)
      (result := last) (profile := profile) middleLive lastActual
  have memoryOne : loadQWord (localCPU first.1 middle).memory address = .ok word :=
    (congrArg (fun cpu : X86.State => loadQWord cpu.memory address) cpuOne).trans memory
  have registerOne : middle.context.registers .rbx = value :=
    (congrArg (fun context : Context => context.registers .rbx) contextOne).trans register
  exact ⟨middle, final, middleLive, finalLive, phaseOne.trans phase,
    phaseTwo.trans (phaseOne.trans phase), memoryOne,
    (congrArg (fun cpu : X86.State => loadQWord cpu.memory address) cpuTwo).trans memoryOne,
    registerOne,
    (congrArg (fun context : Context => context.registers .rbx) contextTwo).trans registerOne⟩

/-- Apply the own-drain theorem twice after RET and transfer the concrete
merged local word through each whole-CPU equality. The global trajectory is
checked separately above, so local stuttering cannot hide reversed publication. -/
theorem returned_own_drains_keep_literal_local_result (profile : Profile) :
    ∃ middle final,
      (firstDrain profile).1.workers[0]? = some middle ∧
      (finalDrain profile).1.workers[0]? = some final ∧
      middle.phase = .returned ∧ final.phase = .returned ∧
      loadQWord (localCPU (firstDrain profile).1 middle).memory 131072 =
        .ok 0xdeadbeef55667788 ∧
      loadQWord (localCPU (finalDrain profile).1 final).memory 131072 =
        .ok 0xdeadbeef55667788 ∧
      middle.context.registers .rbx = 0xdeadbeef55667788 ∧
      final.context.registers .rbx = 0xdeadbeef55667788 := by
  exact two_drains_keep_returned (before := returned profile) (first := firstDrain profile)
    (last := finalDrain profile) (tid := 0) (profile := profile) (address := 131072)
    (value := 0xdeadbeef55667788) (pc := 0x7000) (stack := 262152) (word := 0xdeadbeef55667788)
    (actual_ret_reifies_original_return profile) (firstDrain_actual profile) (finalDrain_actual profile)

#print axioms bounded_effects_accepted
#print axioms checked_head_lifts_without_publication
#print axioms high_dword_reifies_merged_memory
#print axioms actual_load_reifies_merged_qword
#print axioms actual_ret_reifies_original_return
#print axioms fifo_publication_and_collection
#print axioms returned_own_drains_keep_literal_local_result

end EDSL.Tests.EffectTSO64Simulation

#audit_edsl
