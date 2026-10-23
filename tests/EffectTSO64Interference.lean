/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.PlainCallInterference
import tests.TSO64CrossCellFixtures
import EDSL.OS.TSO64.EffectSimulation.Ordinary
import EDSL.OS.TSO64.EffectSimulation.Lifting
import EDSL.OS.TSO64.CellEffects
import EDSL.Audit

/-!
Independent regression tests for the current-state ordinary bridge and
the unfiltered schedule fold. These synthetic fixtures use the existing stable-resource, aligned scalar-RAM, long-mode and
CET-off scheduler assumptions; they make no native or source-language claim.

The resumption starts at an actually issued pair of FIFOs. A real peer drain
changes the reader's local memory before its checked load head is constructed.
The second client relates a ghost word to current registered-cell RAM, and
checks literal action positions, retirement costs and full64 event payloads.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.EffectTSO64Interference
open X86 OS.TSO64 OS.TSO64.EffectSimulation

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private theorem found_ok {α : Type} (value : Option α) (present : value.isSome = true) :
    value = some (value.get present) := by
  cases value with
  | none => cases present
  | some value => rfl

/-- Specialize the existing peer frame while the scheduler state is symbolic. -/
private theorem drain_peer_live {state : OS.TSO64.State} {tid peer : Nat}
    {result : OS.TSO64.State × Observation} {profile : Profile} {worker : Worker}
    (actual : step state (.drain tid) profile = .ok result)
    (live : state.workers[peer]? = some worker) (different : peer ≠ tid) :
    result.1.workers[peer]? = some worker := by
  have frame : result.1.workers[peer]? = state.workers[peer]? :=
    step_peer actual different
  exact frame.trans live

/-- Give tuple eta a symbolic pair, without unfolding a concrete OS fixture. -/
private theorem pair_output {ε α β : Type} {attempt : Except ε (α × β)}
    {result : α × β} (actual : attempt = .ok result) :
    attempt = .ok (result.1, result.2) := by
  cases result
  exact actual

namespace Resumption

-- Reuse the actual resource setup and issued private/managed FIFOs. The reader
-- is at MOV RAX,[RDI], not at a guessed successor of a sequential execution.
def before : OS.TSO64.State := PlainCallInterference.boundary
def reader : Worker := PlainCallInterference.boundaryReader

def publicationAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step before (.drain 1) .sharedCell

theorem publication_succeeds : publicationAttempt.toOption.isSome = true := by
  decide +kernel

def publication : OS.TSO64.State × Observation :=
  checked publicationAttempt publication_succeeds

theorem publication_actual : step before (.drain 1) .sharedCell = .ok publication :=
  checked_ok _ _

def current : OS.TSO64.State := publication.1

theorem current_valid : WellFormed current .sharedCell :=
  step_wellFormed PlainCallInterference.boundary_valid publication_actual

-- This frames the peer WORKER record, which contains no RAM snapshot.
theorem current_live : current.workers[0]? = some reader := by
  have live : before.workers[0]? = some reader := PlainCallInterference.live
  unfold current
  exact drain_peer_live (state := before) (tid := 1) (peer := 0)
    (result := publication) (profile := .sharedCell) (worker := reader)
    publication_actual live (by decide +kernel)

/-- The managed peer publishes a different full word. Its drain does not
publish the reader's unrelated private head. -/
theorem current_reads :
    loadQWord (localCPU current reader).memory 65536 = .ok 0xfedcba9876543210 ∧
    loadQWord (published current.world) 65536 = .ok 0xfedcba9876543210 ∧
    loadQWord (published current.world) 131072 = .ok 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- A peer worker frame must not be strengthened to local-CPU stuttering or
used to reuse a sequential tail about the pre-publication memory. -/
theorem peer_publication_changes_reader_cpu :
    localCPU current reader ≠ localCPU before reader := by
  intro same
  have wrong : (Except.ok (0xfedcba9876543210 : Word) : Except Error Word) =
      .ok 0x1122334455667788 :=
    current_reads.1.symm.trans
      ((congrArg (fun cpu : X86.State => loadQWord cpu.memory 65536) same).trans
        PlainCallInterference.boundary_reads.1)
  have different : (0xfedcba9876543210 : Word) ≠ 0x1122334455667788 := by
    decide +kernel
  exact different (Except.ok.inj wrong)

def bytes : List Byte := [0x48, 0x8b, 0x07]
def instruction : Sequential.Instruction := .loadMem64 .rax (.base .rdi)

-- The policy authorizes this load and its one full-width data read. It grants
-- no OS authority; OrdinaryReady supplies the actual current OS checks.
def policy : X86.VCGen.Effects.Policy where
  Current := fun cpu => cpu.rip = 393219 ∧ cpu.registers .rsp = 262144
  AllowedRead := fun _ read => read = ⟨.data, 65536, 8⟩
  AllowedEffect := fun _ decoded _ => decoded = instruction

theorem current_code : CodeAt (localCPU current reader).memory 393219 bytes := by
  refine ⟨by decide +kernel, ?_⟩
  intro offset byte present
  have bound : offset < 3 := (List.getElem_of_getElem? present).1
  have positions : offset = 0 ∨ offset = 1 ∨ offset = 2 := by omega
  rcases positions with rfl | rfl | rfl
  all_goals
    simp only [bytes, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at present
    subst byte
    decide +kernel

theorem current_decoded :
    Sequential.decodeAt (localCPU current reader) = .ok instruction := by
  decide +kernel

theorem current_ready : OrdinaryReady current 0 reader instruction .sharedCell := by
  have valid := current_valid.2 reader (List.mem_of_getElem? current_live)
  refine ⟨current_live, ?_, valid.1.1, valid.1.2.1, ?_, rfl, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · refine ⟨[()], ?_⟩
    decide +kernel
  · exact ⟨⟨reader.pending, reader.nextStore⟩, .unchanged rfl⟩

/-- Consume the constructive bridge, then use its full-CPU equality to
transfer the literal peer value and register frame to the actual scheduler
worker. Neither a future world nor an intended successor is an input premise. -/
theorem resumed_load_from_current_head (af : Bool) :
    ∃ actual result after,
      X86.VCGen.Effects.Head bytes 393219 policy (Sequential.FlagChoices.uniform af)
        (localCPU current reader) instruction actual ∧
      actual.reads = [⟨.data, 65536, 8⟩] ∧
      step current (.issue 0 af) .sharedCell = .ok result ∧
      result.1.workers[0]? = some after ∧ result.2 = .ordinary 0 ∧
      after.context.registers .rax = 0xfedcba9876543210 ∧
      after.context.registers .rsp = 262144 ∧
      after.context.registers .rbx = 0x8877665544332211 ∧
      result.1.world = current.world ∧ WellFormed result.1 .sharedCell := by
  have address : Sequential.Address.eval (.base .rdi) (localCPU current reader) =
      65536 := by decide +kernel
  have loaded : loadQWord (localCPU current reader).memory
      (Sequential.Address.eval (.base .rdi) (localCPU current reader)) =
        .ok 0xfedcba9876543210 := by
    rw [address]
    exact current_reads.1
  obtain ⟨output, executed, value, frame, _memory, _flags, _rip⟩ :=
    Sequential.execute_loadMem64_context (destination := .rax) af loaded
  rw [address] at executed
  let actual : Sequential.Observation := ⟨.next output, [⟨.data, 65536, 8⟩]⟩
  have stepped : Sequential.stepWith (Sequential.FlagChoices.uniform af)
      (localCPU current reader) = .ok actual := by
    rw [Sequential.stepWith_eq_executeWith _ current_decoded,
      Sequential.executeWith_uniform _ _ af (by rfl)]
    exact executed
  have head : X86.VCGen.Effects.Head bytes 393219 policy
      (Sequential.FlagChoices.uniform af) (localCPU current reader) instruction actual := by
    refine ⟨current_code, ?_, current_decoded, stepped, ?_, rfl, ?_⟩
    · constructor <;> decide +kernel
    · intro read member
      change read = ⟨.data, 65536, 8⟩
      simpa only [actual, List.mem_singleton] using member
    · intro final returned
      cases returned
  obtain ⟨result, success, reified, world, valid⟩ :=
    issue_from_head current_valid current_ready head
  obtain ⟨after, live, reified⟩ := reified
  change result.2 = .ordinary 0 ∧ after.phase = .running ∧
    localCPU result.1 after = output at reified
  have resultValue : after.context.registers .rax = 0xfedcba9876543210 := by
    change (localCPU result.1 after).registers .rax = _
    rw [reified.2.2]
    exact value
  have rsp : after.context.registers .rsp = 262144 := by
    change (localCPU result.1 after).registers .rsp = _
    rw [reified.2.2, frame .rsp (by decide +kernel)]
    decide +kernel
  have rbx : after.context.registers .rbx = 0x8877665544332211 := by
    change (localCPU result.1 after).registers .rbx = _
    rw [reified.2.2, frame .rbx (by decide +kernel)]
    decide +kernel
  exact ⟨actual, result, after, head, rfl, success, live, reified.1,
    resultValue, rsp, rbx, world, valid⟩

end Resumption

namespace Cuts

-- Real bytes: MOV dword [RCX],ESI; LOCK XADD qword [RDX],RSI; RET.
-- The reused setup puts RDX at registered cell B and RCX at privateData+4.
def initialAttempt : Except Fault OS.TSO64.State :=
  TSO64CrossCellFixtures.start 0xc332c10f48f03189 0
    3 0x11223344ffffffff 1 2 0 0

theorem initial_succeeds : initialAttempt.toOption.isSome = true := by decide +kernel
def initial : OS.TSO64.State := checked initialAttempt initial_succeeds

theorem initial_actual : initialAttempt = .ok initial := checked_ok _ _
theorem initial_valid : WellFormed initial .sharedCell :=
  TSO64CrossCellFixtures.start_valid initial_actual

def actions : List Action :=
  [.issue 0 false, .issue 1 false, .issue 0 false, .drain 0,
    .issue 0 true, .issue 1 false, .issue 0 false]

def runAttempt : Except Fault (OS.TSO64.State × List Observation) :=
  schedule initial actions .sharedCell

theorem run_succeeds : runAttempt.toOption.isSome = true := by decide +kernel
def result : OS.TSO64.State × List Observation := checked runAttempt run_succeeds
theorem scheduled : schedule initial actions .sharedCell = .ok result := checked_ok _ _

def target : OS.Atomics64.CellId64 := ⟨1⟩
theorem target_present : (initial.world.cells target).isSome = true := by decide +kernel
def cell : OS.Atomics64.Cell := (initial.world.cells target).get target_present
theorem target_live : initial.world.cells target = some cell := found_ok _ _
theorem target_address : cell.address = 458752 := by decide +kernel

structure RMW where
  position : Nat
  tid : Nat
  delta : Word
  old : Word
  new : Word
  deriving DecidableEq

structure Account where
  positions : Nat
  retired : Nat
  word : Word
  events : List RMW
  deriving DecidableEq

def seed : Account := ⟨0, 0, 0x11223344ffffffff, []⟩

-- A current-RAM assertion, not True, a copy of the whole scheduler, a desired
-- afterworld, or a premise that the chosen suffix will succeed.
def Rel (state : OS.TSO64.State) (ghost : Account) : Prop :=
  state.world.cells target = some cell ∧
    loadQWord (published state.world) cell.address = .ok ghost.word

-- The actual typed publication identities select the tracked cell. Events
-- retain their full64 operands, even when an RMW leaves bits unchanged.
def tick (ghost : Account) (observation : Observation) : Account where
  positions := ghost.positions + 1
  retired := ghost.retired + observation.retired
  word := match PublishedHistory.writeOf observation with
    | none => ghost.word
    | some cause => if cause.cell = target then cause.value else ghost.word
  events := ghost.events ++ match observation with
    | .rmw tid event => [⟨ghost.positions, tid, event.arithmetic.delta,
        event.arithmetic.event.before, event.arithmetic.event.after⟩]
    | _ => []

def Advance (ghost : Account) (_action : Action) (observation : Observation)
    (next : Account) : Prop := next = tick ghost observation

/-- Use the real native origins and their checked OS effects. Ordinary issues
and blocks keep published RAM; private drains frame registered cells; an
RMW or managed drain supplies its actual current-world readback. -/
theorem laws : Simulation .sharedCell Rel Advance := by
  constructor
  intro state after action observation ghost valid related origin
  refine ⟨tick ghost observation, rfl, ?_⟩
  cases origin with
  | ordinary _live _running _code _caller _fetched effect =>
    cases effect with
    | intro _admitted _bounds _decoded _reads _queue _executed finish =>
      cases finish <;> exact related
  | blocked => exact related
  | rmw _live _running _code _caller _fetched _bounds _empty _grant effect =>
    refine ⟨(congrFun effect.os.cells target).trans related.1, ?_⟩
    exact PublishedHistory.rmw_read valid.1 effect.checked target cell related.1
      ghost.word related.2
  | drained _live _fifo _gate changed publication =>
    have cells := (congrFun publication.stable.cells target).trans related.1
    cases changed with
    | ordinary changed =>
      exact ⟨cells, (OS.AtomicFetchAddHistory64.mutate_load valid.1 changed
        target cell related.1).trans related.2⟩
    | managed current changed =>
      exact ⟨cells, PublishedHistory.managed_publication_read valid.1 current changed
        target cell related.1 ghost.word related.2⟩

theorem initially_related : Rel initial seed := by
  refine ⟨target_live, ?_⟩
  decide +kernel

private theorem account_of_lift {first last : Account} {plan : List Action}
    {observations : List Observation} (trace : LiftTrace Advance first plan observations last) :
    last = observations.foldl tick first := by
  induction trace with
  | nil => rfl
  | cons head _tail ih =>
    dsimp only [Advance] at head
    simpa only [List.foldl_cons, ← head] using ih

def Cut (index : Nat) (expected : Account) : Prop :=
  ∃ before,
    schedule initial (actions.take index) .sharedCell =
      .ok (before, result.2.take index) ∧
    schedule before (actions.drop index) .sharedCell =
      .ok (result.1, result.2.drop index) ∧
    loadQWord (published before.world) 458752 = .ok expected.word ∧
    LiftTrace Advance seed (actions.take index) (result.2.take index) expected

-- Expected accounts below are literal contracts, not an expected-value
-- interpreter. Determinism identifies the ghost returned by the schedule-cut fold.
private theorem cut_contract (index : Nat) (expected : Account)
    (literal : (result.2.take index).foldl tick seed = expected) : Cut index expected := by
  have exactRun : schedule initial actions .sharedCell = .ok (result.1, result.2) :=
    pair_output (attempt := schedule initial actions .sharedCell) (result := result) scheduled
  obtain ⟨before, next, prefixRun, suffixRun, related, lifted⟩ :=
    Simulation.schedule_cut (G := Account) (profile := .sharedCell)
      (Rel := Rel) (Advance := Advance) laws
      (initial := initial) (final := result.1) (actions := actions)
      (observations := result.2) (g := seed) initial_valid initially_related exactRun index
  have same : next = expected := (account_of_lift lifted).trans literal
  subst next
  have read := related.2
  rw [target_address] at read
  exact ⟨before, prefixRun, suffixRun, read, lifted⟩

/-- Both stores retire; neither has published the registered target. -/
theorem cut_before_first_block : Cut 2 ⟨2, 2, 0x11223344ffffffff, []⟩ :=
  cut_contract 2 _ (by decide +kernel)

/-- A blocked issue consumes position 2 and no retirement or RMW event. -/
theorem cut_after_first_block : Cut 3 ⟨3, 2, 0x11223344ffffffff, []⟩ :=
  cut_contract 3 _ (by decide +kernel)

/-- The private drain is action 3, still with zero extra instruction credit. -/
theorem cut_after_drain : Cut 4 ⟨4, 2, 0x11223344ffffffff, []⟩ :=
  cut_contract 4 _ (by decide +kernel)

/-- Retry is action 4, not retired index 2. Its full64 +1 carries past bit31;
the peer's still-pending FIFO cannot block this worker's RMW. -/
theorem cut_after_rmw : Cut 5
    ⟨5, 3, 0x1122334500000000, [⟨4, 0, 1, 0x11223344ffffffff, 0x1122334500000000⟩]⟩ :=
  cut_contract 5 _ (by decide +kernel)

/-- The peer's blocked attempt also remains an action position. -/
theorem cut_after_peer_block : Cut 6
    ⟨6, 3, 0x1122334500000000, [⟨4, 0, 1, 0x11223344ffffffff, 0x1122334500000000⟩]⟩ :=
  cut_contract 6 _ (by decide +kernel)

/-- RET adds one instruction. A past-end cut adds no artificial position. -/
theorem cut_past_end : Cut 8
    ⟨7, 4, 0x1122334500000000, [⟨4, 0, 1, 0x11223344ffffffff, 0x1122334500000000⟩]⟩ :=
  cut_contract 8 _ (by decide +kernel)

/-- Check production accounting and FIFO publication independently of the
ghost relation: only worker 0's private dword was drained, worker 1 remains
blocked with its own entry, and the original caller's RET still succeeds. -/
theorem actual_accounting :
    result.2.map Observation.retired = [1, 1, 0, 0, 1, 0, 1] ∧
    result.2[2]? = some (.blocked 0) ∧ result.2[5]? = some (.blocked 1) ∧
    loadDWord (published result.1.world) 131076 = .ok 1 ∧
    loadDWord (published result.1.world) 196612 = .ok 0 ∧
    (result.1.workers[1]?).map (fun worker => worker.pending.length) = some 1 ∧
    collect result.1 0 = .ok 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Cuts
end EDSL.Tests.EffectTSO64Interference

#print axioms EDSL.Tests.EffectTSO64Interference.Resumption.publication_actual
#print axioms EDSL.Tests.EffectTSO64Interference.Resumption.current_valid
#print axioms EDSL.Tests.EffectTSO64Interference.Resumption.current_live
#print axioms EDSL.Tests.EffectTSO64Interference.Resumption.current_reads
#print axioms EDSL.Tests.EffectTSO64Interference.Resumption.peer_publication_changes_reader_cpu
#print axioms EDSL.Tests.EffectTSO64Interference.Resumption.current_code
#print axioms EDSL.Tests.EffectTSO64Interference.Resumption.current_decoded
#print axioms EDSL.Tests.EffectTSO64Interference.Resumption.current_ready
#print axioms EDSL.Tests.EffectTSO64Interference.Resumption.resumed_load_from_current_head
#print axioms EDSL.Tests.EffectTSO64Interference.Cuts.initial_actual
#print axioms EDSL.Tests.EffectTSO64Interference.Cuts.initial_valid
#print axioms EDSL.Tests.EffectTSO64Interference.Cuts.scheduled
#print axioms EDSL.Tests.EffectTSO64Interference.Cuts.laws
#print axioms EDSL.Tests.EffectTSO64Interference.Cuts.initially_related
#print axioms EDSL.Tests.EffectTSO64Interference.Cuts.cut_before_first_block
#print axioms EDSL.Tests.EffectTSO64Interference.Cuts.cut_after_first_block
#print axioms EDSL.Tests.EffectTSO64Interference.Cuts.cut_after_drain
#print axioms EDSL.Tests.EffectTSO64Interference.Cuts.cut_after_rmw
#print axioms EDSL.Tests.EffectTSO64Interference.Cuts.cut_after_peer_block
#print axioms EDSL.Tests.EffectTSO64Interference.Cuts.cut_past_end
#print axioms EDSL.Tests.EffectTSO64Interference.Cuts.actual_accounting
#audit_edsl
