/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import EDSL.OS.TSO64.EffectSimulation.Passive
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
One synthetic production schedule under both authority profiles. The subject
executes two DWORD stores and RET without publishing either store. Its passive
suffix includes a peer store, a genuinely blocked peer LOCK, and interleaved
own/peer drains. The peer changes disjoint owned RAM, which must also change
the returned subject's reconstructed local CPU despite its saved frame.

Every worker comes from checked makeWorker/attach; every later state comes
from successful production step/schedule results. There is no fabricated FIFO,
Origin, successor, memory overlay, executor, or initial invariant premise.
Neither profile needs managed ordinary access: the LOCK attempt blocks before
an atomic operation. This does not test sharedCell's managed-qword fallback.
The model's stable-resource, aligned scalar-RAM, long-mode and CET-off limits
apply. These finite model cases give no hardware, progress or corpus credit.
-/

namespace EDSL.Tests.EffectPassiveHistory
open X86 OS.TSO64 OS.TSO64.EffectSimulation

-- Constructive equality stays local to the finite observations below.
private def exceptEq {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error left, .error right =>
    match decEq left right with
    | .isTrue same => isTrue (congrArg Except.error same)
    | .isFalse different => isFalse (fun same => different (Except.error.inj same))
  | .ok left, .ok right =>
    match decEq left right with
    | .isTrue same => isTrue (congrArg Except.ok same)
    | .isFalse different => isFalse (fun same => different (Except.ok.inj same))
  | .error _, .ok _ => isFalse (fun same => by cases same)
  | .ok _, .error _ => isFalse (fun same => by cases same)

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α) := exceptEq
local instance : DecidableEq (List Store × Word × Phase × Nat) := inferInstance
local instance : DecidableEq (Nat × Nat × Word × StoreBuffer.Mixed.Value) := inferInstance
local instance : DecidableEq (List Store × Except Error Word) := inferInstance

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

-- Use product eta while the output is symbolic, before applying the fixture.
private theorem pair_output {ε α β : Type} {attempt : Except ε (α × β)} {result : α × β}
    (actual : attempt = .ok result) : attempt = .ok (result.1, result.2) := by
  cases result
  exact actual

private theorem mapped_position {α β : Type} (observe : α → β)
    {entries : List α} {index : Nat} {expected : β}
    (found : (entries.map observe)[index]? = some expected) :
    ∃ entry, entries[index]? = some entry ∧ observe entry = expected := by
  rw [List.getElem?_map] at found
  cases actual : entries[index]? with
  | none => rw [actual] at found; cases found
  | some entry =>
    rw [actual] at found
    exact ⟨entry, rfl, Option.some.inj found⟩

-- Compose production setup with symbolic workers before applying the fixture.
private theorem attach_worker {state : OS.TSO64.State} {actor : Nat} {context : Context}
    {code caller : Nat} {grants : List OS.Ownership.Ticket}
    {atomics : List OS.Atomics64.HandleId64} {worker : Worker}
    (made : makeWorker state.world actor context code caller grants atomics = .ok worker) :
    attach state actor context code caller grants atomics =
      .ok ⟨state.world, state.workers ++ [worker]⟩ := by
  simp only [attach, made, ok_bind, pure_ok]

private theorem empty_world_valid {currentWorld : World}
    (valid : OS.Atomics64.WellFormed currentWorld) (profile : Profile) :
    WellFormed (⟨currentWorld, []⟩ : OS.TSO64.State) profile := by
  refine ⟨valid, ?_⟩
  intro worker member
  cases member

private theorem checked_pair_setup {currentWorld : World}
    {actorA actorB codeA callerA codeB callerB : Nat} {contextA contextB : Context}
    {grantsA grantsB : List OS.Ownership.Ticket}
    {atomicsA atomicsB : List OS.Atomics64.HandleId64} {workerA workerB : Worker}
    (profile : Profile) (valid : OS.Atomics64.WellFormed currentWorld)
    (madeA : makeWorker currentWorld actorA contextA codeA callerA grantsA atomicsA = .ok workerA)
    (madeB : makeWorker currentWorld actorB contextB codeB callerB grantsB atomicsB = .ok workerB) :
    attach ⟨currentWorld, []⟩ actorA contextA codeA callerA grantsA atomicsA =
        .ok ⟨currentWorld, [workerA]⟩ ∧
      attach ⟨currentWorld, [workerA]⟩ actorB contextB codeB callerB grantsB atomicsB =
        .ok ⟨currentWorld, [workerA, workerB]⟩ ∧
      WellFormed (⟨currentWorld, [workerA, workerB]⟩ : OS.TSO64.State) profile := by
  have attached : attach ⟨currentWorld, []⟩ actorA contextA codeA callerA grantsA atomicsA =
      .ok ⟨currentWorld, [workerA]⟩ :=
    attach_worker (state := ⟨currentWorld, []⟩) madeA
  have followed : attach ⟨currentWorld, [workerA]⟩ actorB contextB codeB callerB grantsB atomicsB =
      .ok ⟨currentWorld, [workerA, workerB]⟩ :=
    attach_worker (state := ⟨currentWorld, [workerA]⟩) madeB
  have firstValid : WellFormed (⟨currentWorld, [workerA]⟩ : OS.TSO64.State) profile :=
    attach_valid_for (state := ⟨currentWorld, []⟩) (after := ⟨currentWorld, [workerA]⟩)
      profile (empty_world_valid (currentWorld := currentWorld) valid profile) attached
  exact ⟨attached, followed,
    attach_valid_for (state := ⟨currentWorld, [workerA]⟩)
      (after := ⟨currentWorld, [workerA, workerB]⟩) profile firstValid followed⟩

-- Construct all three connected origins before substituting extracted results.
private theorem three_step_trace {profile : Profile} {before : OS.TSO64.State}
    {firstResult secondResult thirdResult : OS.TSO64.State × Observation}
    {firstAction secondAction thirdAction : Action}
    (firstStep : step before firstAction profile = .ok firstResult)
    (secondStep : step firstResult.1 secondAction profile = .ok secondResult)
    (thirdStep : step secondResult.1 thirdAction profile = .ok thirdResult) :
    OriginTrace profile before
      [⟨before, firstAction, firstResult⟩,
        ⟨firstResult.1, secondAction, secondResult⟩,
        ⟨secondResult.1, thirdAction, thirdResult⟩] thirdResult.1 :=
  OriginTrace.cons (tick := ⟨before, firstAction, firstResult⟩) (step_origin firstStep)
    (OriginTrace.cons (tick := ⟨firstResult.1, secondAction, secondResult⟩) (step_origin secondStep)
      (OriginTrace.cons (tick := ⟨secondResult.1, thirdAction, thirdResult⟩)
        (step_origin thirdStep) .nil))

-- Normalize paired Pause endpoints while their states and logs are symbolic.
private theorem pause_from_trace {profile : Profile} {tid : Nat}
    {initial before after : OS.TSO64.State} {history extended : Log}
    {prior : Worker} {base : Word} {codeBytes : List Byte}
    (paused : Pause profile tid (before, history) (after, extended))
    (priorTrace : OriginTrace profile initial history before)
    (valid : WellFormed initial profile)
    (code : CodeAt (published initial.world) base codeBytes)
    (live : before.workers[tid]? = some prior) :
    OriginTrace profile initial extended after ∧
      WellFormed after profile ∧ CodeAt (published after.world) base codeBytes ∧
      ∃ current, after.workers[tid]? = some current ∧ SavedFrame prior current :=
  ⟨paused.authentic priorTrace, paused.wellFormed (priorTrace.wellFormed valid),
    paused.code (priorTrace.code code), paused.saved live⟩

-- Little endian: 89 02; 89 31; C3; 89 02; F0 48 0F C1 37; C3; padding.
-- The peer starts at offset five in the same real checked code allocation.
private def setup : Except TSO64.OSFault TSO64.Ready :=
  TSO64.fixture 0xf00289c331890289 0x909090c337c10f48 19
private theorem setup_present : setup.toOption.isSome = true := by decide +kernel
private def ready : TSO64.Ready := setup.toOption.get setup_present
private def world : World := ready.checked.world
private def entry : Context := TSO64.context 262144 131072 0xaabbccdd 0x11223344
private def peerEntry : Context :=
  { TSO64.context 327680 196608 9 0x55667788 with rip := 393221 }

private def makeSubject : Except Fault Worker :=
  makeWorker world 11 entry ready.codeA ready.callerA [ready.dataA] [ready.atomicA]
private def makePeer : Except Fault Worker :=
  makeWorker world 12 peerEntry ready.codeB ready.callerB [ready.dataB] [ready.atomicB]
private theorem subject_present : makeSubject.toOption.isSome = true := by decide +kernel
private theorem peer_present : makePeer.toOption.isSome = true := by decide +kernel
private def subject : Worker := makeSubject.toOption.get subject_present
private def peer : Worker := makePeer.toOption.get peer_present
private theorem subject_made :
    makeWorker world 11 entry ready.codeA ready.callerA [ready.dataA] [ready.atomicA] =
      .ok subject := output_ok makeSubject subject_present
private theorem peer_made :
    makeWorker world 12 peerEntry ready.codeB ready.callerB [ready.dataB] [ready.atomicB] =
      .ok peer := output_ok makePeer peer_present

-- Keep list constructors visible at depth 128, but prove actual attachment.
private def first : OS.TSO64.State := ⟨world, [subject]⟩
private def initial : OS.TSO64.State := ⟨world, [subject, peer]⟩
private theorem world_valid : OS.Atomics64.WellFormed world := ready.checked.valid

-- Stop elaborator unfolding at checked interfaces; kernel finite checks still
-- reduce the original definitions, including every resource and queue check.
attribute [local irreducible] ready world subject peer

private theorem initial_setup (profile : Profile) :
    attach ⟨world, []⟩ 11 entry ready.codeA ready.callerA [ready.dataA] [ready.atomicA] =
        .ok first ∧
      attach first 12 peerEntry ready.codeB ready.callerB [ready.dataB] [ready.atomicB] =
        .ok initial ∧
      WellFormed initial profile :=
  checked_pair_setup (currentWorld := world) (actorA := 11) (actorB := 12)
    (contextA := entry) (contextB := peerEntry)
    (codeA := ready.codeA) (callerA := ready.callerA)
    (codeB := ready.codeB) (callerB := ready.callerB)
    (grantsA := [ready.dataA]) (grantsB := [ready.dataB])
    (atomicsA := [ready.atomicA]) (atomicsB := [ready.atomicB])
    (workerA := subject) (workerB := peer) profile world_valid subject_made peer_made

private theorem initial_valid (profile : Profile) : WellFormed initial profile :=
  (initial_setup profile).2.2

private theorem initial_empty : subject.pending = [] ∧ peer.pending = [] :=
  ⟨(makeWorker_valid_for .ownedOnly subject_made).2.2.1,
    (makeWorker_valid_for .ownedOnly peer_made).2.2.1⟩

-- Success checks are extraction obligations, not the behavioral assertions.
private theorem low_present (profile : Profile) :
    (step initial (.issue 0 false) profile).toOption.isSome = true := by
  cases profile <;> decide +kernel
private def low (profile : Profile) : OS.TSO64.State × Observation :=
  (step initial (.issue 0 false) profile).toOption.get (low_present profile)
private theorem low_actual (profile : Profile) :
    step initial (.issue 0 false) profile = .ok (low profile) :=
  output_ok (step initial (.issue 0 false) profile) (low_present profile)

attribute [local irreducible] low

private theorem queued_present (profile : Profile) :
    (step (low profile).1 (.issue 0 true) profile).toOption.isSome = true := by
  cases profile <;> decide +kernel
private def queued (profile : Profile) : OS.TSO64.State × Observation :=
  (step (low profile).1 (.issue 0 true) profile).toOption.get (queued_present profile)
private theorem queued_actual (profile : Profile) :
    step (low profile).1 (.issue 0 true) profile = .ok (queued profile) :=
  output_ok (step (low profile).1 (.issue 0 true) profile) (queued_present profile)

attribute [local irreducible] queued

private theorem returned_present (profile : Profile) :
    (step (queued profile).1 (.issue 0 false) profile).toOption.isSome = true := by
  cases profile <;> decide +kernel
private def returned (profile : Profile) : OS.TSO64.State × Observation :=
  (step (queued profile).1 (.issue 0 false) profile).toOption.get (returned_present profile)
private theorem returned_actual (profile : Profile) :
    step (queued profile).1 (.issue 0 false) profile = .ok (returned profile) :=
  output_ok (step (queued profile).1 (.issue 0 false) profile) (returned_present profile)

attribute [local irreducible] returned

private theorem returned_live_present (profile : Profile) :
    ((returned profile).1.workers[0]?).isSome = true := by
  cases profile <;> decide +kernel
private def returnedWorker (profile : Profile) : Worker :=
  ((returned profile).1.workers[0]?).get (returned_live_present profile)
private theorem returned_live (profile : Profile) :
    (returned profile).1.workers[0]? = some (returnedWorker profile) :=
  found_ok ((returned profile).1.workers[0]?) (returned_live_present profile)

attribute [local irreducible] returnedWorker

private def issuedPrefix (profile : Profile) : Log := [
  ⟨initial, .issue 0 false, low profile⟩,
  ⟨(low profile).1, .issue 0 true, queued profile⟩,
  ⟨(queued profile).1, .issue 0 false, returned profile⟩]
private theorem prefix_authentic (profile : Profile) :
    OriginTrace profile initial (issuedPrefix profile) (returned profile).1 :=
  three_step_trace (profile := profile) (before := initial)
    (firstResult := low profile) (secondResult := queued profile) (thirdResult := returned profile)
    (firstAction := .issue 0 false) (secondAction := .issue 0 true) (thirdAction := .issue 0 false)
    (low_actual profile) (queued_actual profile) (returned_actual profile)

private def actions : List Action :=
  [.issue 1 false, .issue 1 true, .drain 0, .drain 1, .drain 0]
private theorem suffix_present (profile : Profile) :
    (schedule (returned profile).1 actions profile).toOption.isSome = true := by
  cases profile <;> decide +kernel
private def completed (profile : Profile) : OS.TSO64.State × List Observation :=
  (schedule (returned profile).1 actions profile).toOption.get (suffix_present profile)
private theorem suffix_actual (profile : Profile) :
    schedule (returned profile).1 actions profile =
      .ok ((completed profile).1, (completed profile).2) :=
  pair_output (output_ok (schedule (returned profile).1 actions profile) (suffix_present profile))

attribute [local irreducible] completed

private structure ContextView where
  registers : List Word
  rip : Word
  flags : Word
  phase : Phase
  nextStore : Nat
  deriving DecidableEq
private def contextView (worker : Worker) : ContextView :=
  ⟨[.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
      .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15].map worker.context.registers,
    worker.context.rip, worker.context.flags, worker.phase, worker.nextStore⟩

/-- Two independently specified DWORD payloads really precede RET. RET keeps
them pending, produces the literal original return/context, and leaves RAM old. -/
theorem returned_with_issued_dwords (profile : Profile) :
    subject.pending = [] ∧ peer.pending = [] ∧
    ((queued profile).1.workers[0]?).map (fun worker =>
      (payload worker.pending, worker.context.rip, worker.phase, worker.nextStore)) =
      some ([⟨131072, .dword 0x11223344⟩, ⟨131076, .dword 0xaabbccdd⟩],
        393220, .running, 2) ∧
    contextView (returnedWorker profile) = {
      registers := [0x11223344, 131076, 131072, 0x8877665544332211, 262152,
        0x8877665544332211, 0xaabbccdd, 65536,
        0x8877665544332211, 0x8877665544332211, 0x8877665544332211,
        0x8877665544332211, 0x8877665544332211, 0x8877665544332211,
        0x8877665544332211, 0x8877665544332211]
      rip := 0x7000, flags := 0x200202, phase := .returned, nextStore := 2 } ∧
    payload (returnedWorker profile).pending =
      [⟨131072, .dword 0x11223344⟩, ⟨131076, .dword 0xaabbccdd⟩] ∧
    loadQWord (published (returned profile).1.world) 131072 = .ok 0 ∧
    loadQWord (localCPU (returned profile).1 (returnedWorker profile)).memory 131072 =
      .ok 0xaabbccdd11223344 ∧
    loadQWord (localCPU (returned profile).1 (returnedWorker profile)).memory 196608 = .ok 0 := by
  refine ⟨initial_empty.1, initial_empty.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals cases profile <;> decide +kernel

private def observations (profile : Profile) : List Observation :=
  [(low profile).2, (queued profile).2, (returned profile).2] ++ (completed profile).2
private def publications (seen : List Observation) :
    List (Nat × Nat × Word × StoreBuffer.Mixed.Value) :=
  seen.zipIdx.filterMap fun (observation, index) => match observation with
    | .drained tid pending => some (index, tid, pending.store.address, pending.store.value)
    | _ => none

/-- Literal full-schedule positions retain the blocked LOCK and every drain.
The two halves of the subject's qword publish on opposite sides of the peer. -/
theorem retirement_and_publication_positions (profile : Profile) :
    (observations profile).map Observation.retired = [1, 1, 1, 1, 0, 0, 0, 0] ∧
    (observations profile)[2]? = some (.returned 0) ∧
    (observations profile)[4]? = some (.blocked 1) ∧
    publications (observations profile) =
      [(5, 0, 131072, .dword 0x11223344), (6, 1, 196608, .dword 0x55667788),
        (7, 0, 131076, .dword 0xaabbccdd)] := by
  cases profile <;> decide +kernel

/-- Current published and local RAM include peer publication after return.
The checked cell, its neighbor and both original caller slots remain literal. -/
theorem current_ram_after_publication (profile : Profile) :
    loadQWord (published (returned profile).1.world) 196608 = .ok 0 ∧
    loadQWord (published (completed profile).1.world) 196608 = .ok 0x55667788 ∧
    [131072, 65536, 65544, 262144, 327680].map
      (loadQWord (published (completed profile).1.world)) =
      [.ok 0xaabbccdd11223344, .ok 19, .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000] ∧
    ((completed profile).1.workers[0]?).map (fun worker =>
      (payload worker.pending, loadQWord (localCPU (completed profile).1 worker).memory 196608)) =
      some ([], .ok 0x55667788) := by
  cases profile <;> decide +kernel

private def bytes : List Byte := [0x89, 0x02, 0x89, 0x31, 0xc3]
private theorem initial_code : CodeAt (published initial.world) 393216 bytes := by
  refine ⟨by decide +kernel, ?_⟩
  intro offset byte found
  have bound : offset < 5 := (List.getElem_of_getElem? found).1
  have positions : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [bytes, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at found
    subst byte
    decide +kernel

private theorem current_caller {state : OS.TSO64.State} {worker : Worker} {profile : Profile}
    (valid : WellFormed state profile) (live : state.workers[0]? = some worker) :
    LeaseCurrent state.world worker.resources.actor worker.resources.caller :=
  (valid.2 worker (List.mem_of_getElem? live)).1.2.1

/-- Authenticate the actual passive suffix, recover the peer drain at its
original index, and apply all three Pause frame/WF/code interfaces. Neither
the complete worker nor its reconstructed memory is claimed immutable. -/
theorem authentic_pause_with_fresh_memory (profile : Profile) :
    ∃ suffix publication current,
      let history := issuedPrefix profile ++ suffix
      Pause profile 0 ((returned profile).1, issuedPrefix profile) ((completed profile).1, history) ∧
      OriginTrace profile initial history (completed profile).1 ∧
      history.map Tick.action = [.issue 0 false, .issue 0 true, .issue 0 false,
        .issue 1 false, .issue 1 true, .drain 0, .drain 1, .drain 0] ∧
      history.map (fun tick => tick.result.2) = observations profile ∧
      history[6]? = some publication ∧ publication.action = .drain 1 ∧
      (OriginTrace profile initial (history.take 6) publication.before ∧
        Origin publication.before publication.action publication.result profile ∧
        OriginTrace profile initial (history.take 7) publication.result.1) ∧
      (completed profile).1.workers[0]? = some current ∧
      SavedFrame (returnedWorker profile) current ∧
      WellFormed (completed profile).1 profile ∧
      CodeAt (published (completed profile).1.world) 393216 bytes ∧
      LeaseCurrent (completed profile).1.world current.resources.actor current.resources.caller ∧
      published (completed profile).1.world ≠ published (returned profile).1.world ∧
      localCPU (completed profile).1 current ≠
        localCPU (returned profile).1 (returnedWorker profile) := by
  have quiet : ∀ action ∈ actions, passive 0 action := by
    intro action member
    simp only [actions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [passive]
  obtain ⟨suffix, paused, actionMap, observationMap⟩ :=
    Pause.of_schedule (tid := 0) (suffix_actual profile) quiet (issuedPrefix profile)
  let history := issuedPrefix profile ++ suffix
  obtain ⟨trace, valid, code, current, live, saved⟩ :=
    pause_from_trace (profile := profile) (tid := 0) (initial := initial)
      (before := (returned profile).1) (after := (completed profile).1)
      (history := issuedPrefix profile) (extended := history)
      (prior := returnedWorker profile) (base := 393216) (codeBytes := bytes)
      paused (prefix_authentic profile) (initial_valid profile) initial_code (returned_live profile)
  have allActions : history.map Tick.action =
      [.issue 0 false, .issue 0 true, .issue 0 false,
        .issue 1 false, .issue 1 true, .drain 0, .drain 1, .drain 0] := by
    change [.issue 0 false, .issue 0 true, .issue 0 false] ++ suffix.map Tick.action = _
    rw [actionMap]
    rfl
  have allObservations : history.map (fun tick => tick.result.2) = observations profile := by
    change [(low profile).2, (queued profile).2, (returned profile).2] ++
      suffix.map (fun tick => tick.result.2) = _
    rw [observationMap]
    rfl
  obtain ⟨publication, found, publicationAction⟩ :=
    mapped_position Tick.action (entries := history) (index := 6)
      (expected := .drain 1) (by rw [allActions]; rfl)
  have cuts := trace.at found
  have localRead : loadQWord (localCPU (completed profile).1 current).memory 196608 =
      .ok 0x55667788 := by
    have snapshot := (current_ram_after_publication profile).2.2.2
    rw [live] at snapshot
    exact (Prod.mk.inj (Option.some.inj snapshot)).2
  have changedRAM : published (completed profile).1.world ≠
      published (returned profile).1.world := by
    intro same
    have wrong := (current_ram_after_publication profile).2.1
    rw [same, (current_ram_after_publication profile).1] at wrong
    have different : (0 : Word) ≠ 0x55667788 := by decide +kernel
    exact different (Except.ok.inj wrong)
  have changedCPU : localCPU (completed profile).1 current ≠
      localCPU (returned profile).1 (returnedWorker profile) := by
    intro same
    have wrong := localRead
    rw [same, (returned_with_issued_dwords profile).2.2.2.2.2.2.2] at wrong
    have different : (0 : Word) ≠ 0x55667788 := by decide +kernel
    exact different (Except.ok.inj wrong)
  exact ⟨suffix, publication, current, paused, trace, allActions, allObservations,
    found, publicationAction, cuts, live, saved, valid, code, current_caller valid live,
    changedRAM, changedCPU⟩

#print axioms returned_with_issued_dwords
#print axioms retirement_and_publication_positions
#print axioms current_ram_after_publication
#print axioms authentic_pause_with_fresh_memory

end EDSL.Tests.EffectPassiveHistory

#audit_edsl
