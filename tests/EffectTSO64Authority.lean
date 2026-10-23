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
Synthetic MOV DWORD PTR [RDI],ESI; RET, using the checked TSO64 fixture's
actual world and code/caller loans. Actor 11 retains no ordinary capabilities.
RDI selects its mapped private RW allocation at 131072; ESI and that RAM are
zero. A two-instruction code-separated certificate accepts the sequential
execution, including the original stack return and literal final RAM.

The certificate's Head authenticates a successful physical-model store.
The production queue and issue reject it under both authority profiles.
The OrdinaryReady gate cannot be supplied: its queue witness would contradict
the actual prepareQueue error, through ManagedRules.queue_checked. No guessed
successor, alternate executor, resource invalidation, or progress assumption is
used. A same-value store still requires its prestate capability.

These finite model tests establish no target-hardware or general lifecycle claim.
-/

namespace EDSL.Tests.EffectTSO64Authority
open X86 OS.TSO64 OS.TSO64.EffectSimulation

-- These helpers only extract successful production results or decide equality
-- with a constructor. They add no interpreter or global Except equality instance.
private theorem output_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) :
    attempt = .ok (attempt.toOption.get accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private instance {ε α : Type} [DecidableEq ε] [DecidableEq α] :
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

private instance errorDecision {ε α : Type} [DecidableEq ε]
    (attempt : Except ε α) (expected : ε) : Decidable (attempt = .error expected) :=
  match attempt with
  | .ok _ => isFalse (fun same => by cases same)
  | .error actual =>
    match decEq actual expected with
    | .isTrue same => isTrue (congrArg Except.error same)
    | .isFalse different => isFalse (fun same => different (Except.error.inj same))

-- Existence checks are setup obligations, not independent behavioral tests.
-- Little endian: 89 37 C3, followed by padding outside the selected window.
private def setup : Except TSO64.OSFault TSO64.Ready :=
  TSO64.fixture 0x9090909090c33789 0x9090909090909090 19

private theorem setup_present : setup.toOption.isSome = true := by decide +kernel
private def ready : TSO64.Ready := setup.toOption.get setup_present
private def world : World := ready.checked.world

private def entryContext : Context where
  registers register := match register with
    | .rsp => 262144
    | .rdi => 131072
    | _ => 0
  rip := 393216
  flags := 0x200202

-- Retain the fixture's genuine full64 handle at 65536. It cannot supply a
-- managed fallback for this private DWORD store at 131072.
private def make : Except Fault Worker :=
  makeWorker world 11 entryContext ready.codeA ready.callerA [] [ready.atomicA]

private theorem make_present : make.toOption.isSome = true := by decide +kernel
private def worker : Worker := make.toOption.get make_present

private theorem made :
    makeWorker world 11 entryContext ready.codeA ready.callerA [] [ready.atomicA] =
      .ok worker := output_ok make make_present

-- Keep the list constructor visible; getting a worker by reducing the entire
-- concrete attach result needlessly stresses elaboration at depth 128.
private def initial : OS.TSO64.State := ⟨world, [worker]⟩
private def initialCPU : X86.State := localCPU initial worker

private theorem attach_single {before : World} {actor : Nat} {entry : Context}
    {codeId callerId : Nat} {grants : List OS.Ownership.Ticket}
    {atomics : List OS.Atomics64.HandleId64} {attached : Worker}
    (actual : makeWorker before actor entry codeId callerId grants atomics = .ok attached) :
    attach ⟨before, []⟩ actor entry codeId callerId grants atomics =
      .ok ⟨before, [attached]⟩ := by
  simp only [attach, actual, ok_bind, pure_ok, List.nil_append]

private theorem attached :
    attach ⟨world, []⟩ 11 entryContext ready.codeA ready.callerA [] [ready.atomicA] =
      .ok initial := attach_single made

private theorem world_valid : OS.Atomics64.WellFormed world := ready.checked.valid

private theorem empty_world_valid {currentWorld : World}
    (valid : OS.Atomics64.WellFormed currentWorld) (profile : Profile) :
    WellFormed (⟨currentWorld, []⟩ : OS.TSO64.State) profile := by
  refine ⟨valid, ?_⟩
  intro worker member
  cases member

private theorem empty_valid (profile : Profile) :
    WellFormed (⟨world, []⟩ : OS.TSO64.State) profile :=
  empty_world_valid world_valid profile

private theorem initial_valid (profile : Profile) : WellFormed initial profile :=
  attach_valid_for profile (empty_valid profile) attached

private def bytes : List Byte := [0x89, 0x37, 0xc3]
private def instruction : Sequential.Instruction := .legacy .storeEsiRdi

private def graph : Sequential.CFG.Graph := ⟨[
  ⟨0, instruction, true, 1⟩,
  ⟨2, .legacy .ret, false, 0⟩], 1⟩

private def entry : graph.Index := ⟨0, by decide +kernel⟩
private def Current (_ : X86.State) : Prop := True
private def AllowedRead (_ : X86.State) (_ : Sequential.Read) : Prop := True
private def decCurrent (state : X86.State) : Decidable (Current state) := isTrue trivial
private def decReads (state : X86.State) (read : Sequential.Read) :
    Decidable (AllowedRead state read) := isTrue trivial

private def policy : VCGen.Effects.Policy :=
  VCGen.Effects.codeSeparatedPolicy bytes 393216 Current AllowedRead

/-- Independent literal return, RAM, instruction count and ordered reads.
The store's permission probes must not become data-read observations. -/
private def Post (result : Sequential.Result) (events : List AtomicEvent) : Prop :=
  result.state.rip = 0x7000 ∧ result.state.registers .rsp = 262152 ∧
  loadDWord result.state.memory 131072 = .ok 0 ∧
  result.instructions = 2 ∧ result.reads = [⟨.stack, 262144, 8⟩] ∧ events = []

private def decPost (result : Sequential.Result) (events : List AtomicEvent) :
    Decidable (Post result events) := by
  unfold Post
  infer_instance

private def certified : Bool :=
  VCGen.Effects.certifySeparated bytes graph 393216 Current AllowedRead decCurrent decReads
    2 entry initialCPU Post decPost

theorem bounded_effects_accepted : certified = true := by decide +kernel

private theorem cpu_decoded : Sequential.decodeAt initialCPU = .ok instruction := by
  decide +kernel

-- The successor is extracted from the real checked physical store, not supplied
-- as an expected memory snapshot. Only scalar observations below are decided.
private def physicalStore : Except Error X86.State := executeStore initialCPU
private theorem physical_present : physicalStore.toOption.isSome = true := by decide +kernel
private def afterStore : X86.State := physicalStore.toOption.get physical_present

private theorem physical_actual : executeStore initialCPU = .ok afterStore :=
  output_ok physicalStore physical_present

private theorem store_step {before after : X86.State}
    (decoded : Sequential.decodeAt before = .ok (.legacy .storeEsiRdi))
    (stored : executeStore before = .ok after) :
    Sequential.stepWith (Sequential.FlagChoices.uniform false) before =
      .ok ⟨.next after, []⟩ := by
  rw [Sequential.stepWith_eq_executeWith _ decoded,
    Sequential.executeWith_uniform _ _ false rfl]
  simp only [Sequential.execute, Sequential.Instruction.operandReads,
    X86.executeInstruction, stored, ok_bind, pure_ok]

private theorem cpu_actual :
    Sequential.stepWith (Sequential.FlagChoices.uniform false) initialCPU =
      .ok ⟨.next afterStore, []⟩ := store_step cpu_decoded physical_actual

/-- Extract the first-step view from the accepted returning certificate.
Its instruction and whole observation are tied to production decoding/execution. -/
theorem accepted_store_head :
    VCGen.Effects.Head bytes 393216 policy (Sequential.FlagChoices.uniform false)
      initialCPU instruction ⟨.next afterStore, []⟩ := by
  obtain ⟨_result, _events, _run, _post, _bound, trace⟩ :=
    VCGen.Effects.certifySeparated_sound bytes graph 393216 Current AllowedRead decCurrent
      decReads 2 entry initialCPU Post decPost bounded_effects_accepted
      (fun _ => Sequential.FlagChoices.uniform false)
  obtain ⟨decoded, actual, head⟩ := VCGen.Effects.Trace.head trace
  have instructionEq : decoded = instruction :=
    Except.ok.inj (head.decoded.symm.trans cpu_decoded)
  subst decoded
  have observationEq : actual = (⟨.next afterStore, []⟩ : Sequential.Observation) :=
    Except.ok.inj (head.actual.symm.trans cpu_actual)
  subst actual
  exact head

/-- A successful real store advances RIP by two and writes the literal zero
already in RAM. Nonempty prestate intent is checked independently of RAM equality. -/
theorem same_value_physical_store :
    storeIntent instruction initialCPU = some ⟨131072, .dword 0⟩ ∧
    loadDWord initialCPU.memory 131072 = .ok 0 ∧
    Sequential.stepWith (Sequential.FlagChoices.uniform false) initialCPU =
      .ok ⟨.next afterStore, []⟩ ∧
    afterStore.rip = 393218 ∧ loadDWord afterStore.memory 131072 = .ok 0 := by
  refine ⟨?_, ?_, cpu_actual, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem queue_denied (profile : Profile) :
    prepareQueue initial worker instruction profile = .error .noGrant := by
  cases profile <;> decide +kernel

/-- The bridge's prestate queue gate is impossible, despite the accepted
effect Head. Use its actual witness and the production admission converse. -/
theorem no_current_ordinary_ready (profile : Profile) :
    ¬OrdinaryReady initial 0 worker instruction profile := by
  intro readyNow
  obtain ⟨update, effect⟩ := readyNow.queue
  have checked : prepareQueue initial worker instruction profile = .ok update :=
    VCGen.ManagedRules.queue_checked effect
  rw [queue_denied profile] at checked
  cases checked

/-- Exercise real scheduler issue under BOTH profiles. Code/caller resources
are valid; this store is denied with noGrant before its physical execution. -/
theorem current_issue_rejected (profile : Profile) :
    step initial (.issue 0 false) profile = .error .noGrant := by
  cases profile <;> decide +kernel

/-- A real attached well-formed scheduler and accepted physical effect Head
still require the separate current OS gate. No WF premise is postulated. -/
theorem accepted_head_rejects_current_issue (profile : Profile) :
    WellFormed initial profile ∧
    VCGen.Effects.Head bytes 393216 policy (Sequential.FlagChoices.uniform false)
      (localCPU initial worker) instruction ⟨.next afterStore, []⟩ ∧
    ¬OrdinaryReady initial 0 worker instruction profile ∧
    step initial (.issue 0 false) profile = .error .noGrant :=
  ⟨initial_valid profile, accepted_store_head, no_current_ordinary_ready profile,
    current_issue_rejected profile⟩

#print axioms bounded_effects_accepted
#print axioms accepted_store_head
#print axioms same_value_physical_store
#print axioms no_current_ordinary_ready
#print axioms current_issue_rejected
#print axioms accepted_head_rejects_current_issue

end EDSL.Tests.EffectTSO64Authority

#audit_edsl
