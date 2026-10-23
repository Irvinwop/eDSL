/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import EDSL.OS.TSO64.EffectSimulation.Ordinary
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Owned synthetic scalar loops run through the production scheduler with current
mapped resources. Literal contracts cover arithmetic, signed backedges, RET
with pending stores, delayed DWORD publication, FIFO order and register frames
under both authority profiles. A checked subloan distinguishes guarded fetch
from global executability. Vector-only IMUL and legacy DWORD XCHG fail closed.
-/

namespace EDSL.Tests.TSO64ScalarControl
open X86 OS.TSO64 OS.TSO64.EffectSimulation

private def exceptDecidableEq {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error left, .error right =>
      match decEq left right with
      | .isTrue same => .isTrue (congrArg Except.error same)
      | .isFalse different => .isFalse (fun same => different (Except.error.inj same))
  | .ok left, .ok right =>
      match decEq left right with
      | .isTrue same => .isTrue (congrArg Except.ok same)
      | .isFalse different => .isFalse (fun same => different (Except.ok.inj same))
  | .error _, .ok _ => .isFalse (fun same => by cases same)
  | .ok _, .error _ => .isFalse (fun same => by cases same)

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α) := exceptDecidableEq

private theorem output_ok {ε α : Type} (attempt : Except ε α)
    (present : attempt.toOption.isSome = true) :
    attempt = .ok (attempt.toOption.get present) := by
  cases attempt with
  | error fault => cases present
  | ok value => rfl

private theorem found_ok {α : Type} (attempt : Option α)
    (present : attempt.isSome = true) : attempt = some (attempt.get present) := by
  cases attempt with
  | none => cases present
  | some value => rfl

private structure Prepared where
  state : OS.TSO64.State
  valid : ∀ profile : Profile, WellFormed state profile

/-- Both workers retain resources obtained from checked allocation, protection,
borrowing and attachment. The second worker supplies a real context frame. -/
private def setup (first second : Word) : Except Fault Prepared := do
  let ready ← (TSO64.fixture first second 0x11223344ffffffff).mapError Fault.os
  let empty : OS.TSO64.State := ⟨ready.checked.world, []⟩
  let entryA : Context := TSO64.context 262144 131072 0x11223344 3
  let entryB : Context := TSO64.context 327680 196608 0x55667788 9
  match one : attach empty 11 entryA ready.codeA ready.callerA
      [ready.dataA] [ready.atomicA] with
  | .error fault => .error fault
  | .ok firstState =>
      match two : attach firstState 12 entryB ready.codeB ready.callerB
          [ready.dataB] [ready.atomicB] with
      | .error fault => .error fault
      | .ok state =>
          .ok ⟨state, fun profile =>
            attach_valid_for (state := firstState) (after := state) profile
              (attach_valid_for (state := empty) (after := firstState) profile
                ⟨ready.checked.valid, by
                  intro worker member
                  change worker ∈ ([] : List Worker) at member
                  cases member⟩ one) two⟩

-- Existence checks only extract outputs of the real checked operations.
private theorem setup_present :
    (setup 0xc3fb75ffc0833289 0x9090909090909090).toOption.isSome = true := by
  decide +kernel

private def prepared : Prepared :=
  (setup 0xc3fb75ffc0833289 0x9090909090909090).toOption.get setup_present

private def initial : OS.TSO64.State := prepared.state

/-- MOV DWORD [RDX],ESI; ADD EAX,-1; JNZ back to ADD; RET. -/
private def bytes : List Byte := [0x89, 0x32, 0x83, 0xc0, 0xff, 0x75, 0xfb, 0xc3]

private theorem queued_present (profile : Profile) :
    (step initial (.issue 0 false) profile).toOption.isSome = true := by
  cases profile <;> decide +kernel

private def queued (profile : Profile) : OS.TSO64.State × Observation :=
  (step initial (.issue 0 false) profile).toOption.get (queued_present profile)

private theorem queued_actual (profile : Profile) :
    step initial (.issue 0 false) profile = .ok (queued profile) :=
  output_ok (ε := Fault) (α := OS.TSO64.State × Observation)
    (step initial (.issue 0 false) profile) (queued_present profile)

private theorem queued_valid (profile : Profile) : WellFormed (queued profile).1 profile :=
  step_wellFormed (state := initial) (action := .issue 0 false)
    (result := queued profile) (profile := profile) (prepared.valid profile) (queued_actual profile)

private theorem arithmetic_present (profile : Profile) (af : Bool) :
    (step (queued profile).1 (.issue 0 af) profile).toOption.isSome = true := by
  cases profile <;> cases af <;> decide +kernel

private def arithmetic (profile : Profile) (af : Bool) : OS.TSO64.State × Observation :=
  (step (queued profile).1 (.issue 0 af) profile).toOption.get
    (arithmetic_present profile af)

private theorem arithmetic_actual (profile : Profile) (af : Bool) :
    step (queued profile).1 (.issue 0 af) profile = .ok (arithmetic profile af) :=
  output_ok (ε := Fault) (α := OS.TSO64.State × Observation)
    (step (queued profile).1 (.issue 0 af) profile) (arithmetic_present profile af)

private theorem arithmetic_valid (profile : Profile) (af : Bool) :
    WellFormed (arithmetic profile af).1 profile :=
  step_wellFormed (state := (queued profile).1) (action := .issue 0 af)
    (result := arithmetic profile af) (profile := profile)
    (queued_valid profile) (arithmetic_actual profile af)

private theorem backedge_present (profile : Profile) (af : Bool) :
    (step (arithmetic profile af).1 (.issue 0 (!af)) profile).toOption.isSome = true := by
  cases profile <;> cases af <;> decide +kernel

private def backedge (profile : Profile) (af : Bool) : OS.TSO64.State × Observation :=
  (step (arithmetic profile af).1 (.issue 0 (!af)) profile).toOption.get
    (backedge_present profile af)

private theorem backedge_actual (profile : Profile) (af : Bool) :
    step (arithmetic profile af).1 (.issue 0 (!af)) profile = .ok (backedge profile af) :=
  output_ok (ε := Fault) (α := OS.TSO64.State × Observation)
    (step (arithmetic profile af).1 (.issue 0 (!af)) profile) (backedge_present profile af)

private def tailActions (af : Bool) : List Action :=
  [.issue 0 af, .issue 0 (!af), .issue 0 af, .issue 0 (!af), .issue 0 af]

private theorem returned_present (profile : Profile) (af : Bool) :
    (schedule (backedge profile af).1 (tailActions af) profile).toOption.isSome = true := by
  cases profile <;> cases af <;> decide +kernel

private def returned (profile : Profile) (af : Bool) : OS.TSO64.State × List Observation :=
  (schedule (backedge profile af).1 (tailActions af) profile).toOption.get
    (returned_present profile af)

private theorem drained_present (profile : Profile) (af : Bool) :
    (drain (returned profile af).1 0 profile).toOption.isSome = true := by
  cases profile <;> cases af <;> decide +kernel

private def drained (profile : Profile) (af : Bool) : OS.TSO64.State × Observation :=
  (drain (returned profile af).1 0 profile).toOption.get (drained_present profile af)

private structure MemoryStatus where
  ram : Except Error Word
  localWord : Option (Except Error Word)
  pending : Option Buffer
  nextStore : Option Nat
  collected : Except Fault Word
  deriving DecidableEq

private def memoryStatus (state : OS.TSO64.State) : MemoryStatus where
  ram := loadQWord (published state.world) 131072
  localWord := state.workers[0]?.map fun worker =>
    loadQWord (localCPU state worker).memory 131072
  pending := state.workers[0]?.map fun worker => payload worker.pending
  nextStore := state.workers[0]?.map Worker.nextStore
  collected := collect state 0

private def drainedStore (observation : Observation) : Option (Nat × Store) :=
  match observation with
  | .drained tid entry => some (tid, entry.store)
  | _ => none

private structure RegisterFrame where
  registers : List Word
  pc : Word
  phase : Phase
  deriving DecidableEq

private def registerFrame (worker : Worker) : RegisterFrame :=
  ⟨[.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
      .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15].map worker.context.registers,
    worker.context.rip, worker.phase⟩

/-- Eight decoded issues take the backedge twice, then return through the
original caller slot. Neither arithmetic nor branches publish the real store.
The store retains its DWORD width and its single consumed issue number. -/
theorem loop_returns_zero_before_publication (profile : Profile) (af : Bool) :
    memoryStatus (queued profile).1 =
      ⟨.ok 0, some (.ok 0x11223344), some [⟨131072, .dword 0x11223344⟩],
        some 1, .error .resource⟩ ∧
    memoryStatus (returned profile af).1 =
      ⟨.ok 0, some (.ok 0x11223344), some [⟨131072, .dword 0x11223344⟩],
        some 1, .error .resource⟩ ∧
    (returned profile af).1.workers[0]?.map registerFrame = some
      ⟨[0, 131076, 131072, 0x8877665544332211, 262152, 0x8877665544332211,
        0x11223344, 65536, 0x8877665544332211, 0x8877665544332211,
        0x8877665544332211, 0x8877665544332211, 0x8877665544332211,
        0x8877665544332211, 0x8877665544332211, 0x8877665544332211],
        0x7000, .returned⟩ ∧
    [ (queued profile).2, (arithmetic profile af).2, (backedge profile af).2 ] ++
        (returned profile af).2 =
      [.ordinary 0, .ordinary 0, .ordinary 0, .ordinary 0,
        .ordinary 0, .ordinary 0, .ordinary 0, .returned 0] := by
  cases profile <;> cases af <;> decide +kernel

/-- Publication occurs only at the explicit drain. It preserves the returned
register/result frame and the inactive peer, and collection then returns zero. -/
theorem explicit_drain_publishes_literal_dword (profile : Profile) (af : Bool) :
    memoryStatus (drained profile af).1 =
      ⟨.ok 0x11223344, some (.ok 0x11223344), some [], some 1, .ok 0⟩ ∧
    drainedStore (drained profile af).2 = some (0, ⟨131072, .dword 0x11223344⟩) ∧
    (drained profile af).2.retired = 0 ∧
    (drained profile af).1.workers[0]?.map registerFrame =
      (returned profile af).1.workers[0]?.map registerFrame ∧
    (drained profile af).1.workers[1]?.map registerFrame = some
      ⟨[9, 196612, 196608, 0x8877665544332211, 327680, 0x8877665544332211,
        0x55667788, 65536, 0x8877665544332211, 0x8877665544332211,
        0x8877665544332211, 0x8877665544332211, 0x8877665544332211,
        0x8877665544332211, 0x8877665544332211, 0x8877665544332211],
        393216, .running⟩ ∧
    [65536, 65544, 131080, 196608, 262144, 327680].map
        (loadQWord (published (drained profile af).1.world)) =
      [.ok 0x11223344ffffffff, .ok 0xabcdef0123456789,
        .ok 0, .ok 0, .ok 0x7000, .ok 0x8000] := by
  cases profile <;> cases af <;> decide +kernel

-- Generic proof helpers keep functional CPU and resource-manager states
-- symbolic while applying the public whole-CPU bridge.
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
      | locked current => cases snapshot
      | ordinary current =>
          have same : current = instruction := Option.some.inj snapshot
          cases same
          rfl

private theorem code_of_finite {memory : Memory} {base : Word} {code : List Byte}
    (noWrap : base.toNat + code.length ≤ 2^64)
    (fetched : ∀ index : Fin code.length,
      fetchByte memory (base + BitVec.ofNat 64 index.val) =
        .ok (code[index.val]'index.isLt)) : CodeAt memory base code := by
  refine ⟨noWrap, ?_⟩
  intro offset byte present
  obtain ⟨inside, same⟩ := List.getElem?_eq_some_iff.mp present
  simpa only [same] using fetched ⟨offset, inside⟩

private def noReadPolicy : VCGen.Effects.Policy :=
  ⟨fun _ => True, fun _ _ => False, fun _ _ _ => True⟩

private theorem next_head {code : List Byte} {base : Word} {before output : X86.State}
    {instruction : Sequential.Instruction} {af : Bool}
    (bound : CodeAt before.memory base code)
    (decoded : Sequential.decodeAt before = .ok instruction)
    (executed : Sequential.stepWith (Sequential.FlagChoices.uniform af) before =
      .ok ⟨.next output, []⟩) :
    VCGen.Effects.Head code base noReadPolicy (Sequential.FlagChoices.uniform af)
      before instruction ⟨.next output, []⟩ := by
  refine ⟨bound, trivial, decoded, executed, ?_, ?_, ?_⟩
  · intro read member
    cases member
  · trivial
  · intro _ _
    trivial

private theorem ready_noReads {state : OS.TSO64.State} {worker : Worker} {tid : Nat}
    {instruction : Sequential.Instruction} {profile : Profile}
    (valid : WellFormed state profile)
    (live : state.workers[tid]? = some worker) (running : worker.phase = .running)
    (dispatch : decode (fetchCPU state worker) = .ok (.ordinary instruction))
    (admitted : supported instruction = true) (bounds : codeFits worker instruction.length)
    (noReads : instruction.operandReads (localCPU state worker) = [])
    (noStore : storeIntent instruction (localCPU state worker) = none) :
    OrdinaryReady state tid worker instruction profile := by
  have resources : ResourcesValid state.world worker.resources :=
    (valid.2 worker (List.mem_of_getElem? live)).1
  refine ⟨live, running, resources.1, resources.2.1, dispatch, admitted, bounds, ?_, ?_⟩
  · exact ⟨[], by rw [noReads]; rfl⟩
  · exact ⟨⟨worker.pending, worker.nextStore⟩, .unchanged noStore⟩

private structure ScalarSnapshot where
  value : Word
  pc : Word
  word : Except Error Word
  deriving DecidableEq

private def scalarSnapshot (state : X86.State) : ScalarSnapshot :=
  ⟨state.registers .rax, state.rip, loadQWord state.memory 131072⟩

private def nextSnapshot (attempt : Except Error Sequential.Observation) : Option ScalarSnapshot :=
  match attempt with
  | .ok ⟨.next output, []⟩ => some (scalarSnapshot output)
  | _ => none

private theorem next_snapshot (attempt : Except Error Sequential.Observation)
    (literal : ScalarSnapshot) (snapshot : nextSnapshot attempt = some literal) :
    ∃ output, attempt = .ok ⟨.next output, []⟩ ∧ scalarSnapshot output = literal := by
  cases attempt with
  | error fault => cases snapshot
  | ok actual =>
      rcases actual with ⟨outcome, reads⟩
      cases outcome with
      | atomic event output => cases snapshot
      | returned output => cases snapshot
      | syscall request => cases snapshot
      | next output =>
          cases reads with
          | cons read rest => cases snapshot
          | nil => exact ⟨output, rfl, Option.some.inj snapshot⟩

private theorem checked_next {state : OS.TSO64.State} {worker : Worker} {tid : Nat}
    {instruction : Sequential.Instruction} {af : Bool} {profile : Profile}
    {result : OS.TSO64.State × Observation} {code : List Byte} {base : Word}
    {literal : ScalarSnapshot}
    (valid : WellFormed state profile)
    (ready : OrdinaryReady state tid worker instruction profile)
    (bound : CodeAt (localCPU state worker).memory base code)
    (decoded : Sequential.decodeAt (localCPU state worker) = .ok instruction)
    (snapshot : nextSnapshot (Sequential.stepWith (Sequential.FlagChoices.uniform af)
      (localCPU state worker)) = some literal)
    (issued : step state (.issue tid af) profile = .ok result) :
    ∃ output, Sequential.stepWith (Sequential.FlagChoices.uniform af) (localCPU state worker) =
        .ok ⟨.next output, []⟩ ∧
      Reifies tid result ⟨.next output, []⟩ ∧ scalarSnapshot output = literal ∧
      result.1.world = state.world ∧ WellFormed result.1 profile := by
  obtain ⟨output, executed, observed⟩ := next_snapshot _ literal snapshot
  have head : VCGen.Effects.Head code base noReadPolicy (Sequential.FlagChoices.uniform af)
      (localCPU state worker) instruction ⟨.next output, []⟩ :=
    next_head (code := code) (base := base) (before := localCPU state worker)
      (output := output) (instruction := instruction) (af := af) bound decoded executed
  obtain ⟨produced, actual, reified, world, preserved⟩ :=
    issue_from_head (state := state) (worker := worker) (tid := tid)
      (instruction := instruction) (af := af) (profile := profile)
      (bytes := code) (base := base) (policy := noReadPolicy)
      (actual := ⟨.next output, []⟩) valid ready head
  have same : produced = result := Except.ok.inj (actual.symm.trans issued)
  subst produced
  exact ⟨output, executed, reified, observed, world, preserved⟩

private theorem queued_worker_present (profile : Profile) :
    ((queued profile).1.workers[0]?).isSome = true := by
  cases profile <;> decide +kernel

private def arithmeticWorker (profile : Profile) : Worker :=
  ((queued profile).1.workers[0]?).get (queued_worker_present profile)

private theorem arithmetic_live (profile : Profile) :
    (queued profile).1.workers[0]? = some (arithmeticWorker profile) :=
  found_ok (α := Worker) ((queued profile).1.workers[0]?) (queued_worker_present profile)

/-- Nonlegacy ADD uses the same head-to-issue bridge with a real pending
DWORD. Its full successor CPU must reify the independently required value two,
fallthrough PC and locally forwarded word, while the world remains unchanged. -/
theorem arithmetic_head_reifies_actual_local_cpu (profile : Profile) (af : Bool) :
    ∃ output,
      Sequential.stepWith (Sequential.FlagChoices.uniform af)
          (localCPU (queued profile).1 (arithmeticWorker profile)) =
        .ok ⟨.next output, []⟩ ∧
      Reifies 0 (arithmetic profile af) ⟨.next output, []⟩ ∧
      scalarSnapshot output = ⟨2, 393221, .ok 0x11223344⟩ ∧
      (arithmetic profile af).1.world = (queued profile).1.world ∧
      WellFormed (arithmetic profile af).1 profile := by
  have dispatch : decode (fetchCPU (queued profile).1 (arithmeticWorker profile)) =
      .ok (.ordinary (.addImm32 .rax 0xff false)) :=
    ordinary_snapshot (decode (fetchCPU (queued profile).1 (arithmeticWorker profile)))
      (.addImm32 .rax 0xff false) (by cases profile <;> decide +kernel)
  have ready : OrdinaryReady (queued profile).1 0 (arithmeticWorker profile)
      (.addImm32 .rax 0xff false) profile :=
    ready_noReads (state := (queued profile).1) (worker := arithmeticWorker profile)
      (tid := 0) (instruction := .addImm32 .rax 0xff false) (profile := profile)
      (queued_valid profile) (arithmetic_live profile)
      (by cases profile <;> decide +kernel) dispatch rfl
      (by cases profile <;> decide +kernel) rfl rfl
  have code : CodeAt (localCPU (queued profile).1 (arithmeticWorker profile)).memory
      393216 bytes :=
    code_of_finite (memory := (localCPU (queued profile).1 (arithmeticWorker profile)).memory)
      (base := 393216) (code := bytes) (by decide +kernel)
      (by cases profile <;> decide +kernel)
  exact checked_next (state := (queued profile).1) (worker := arithmeticWorker profile)
    (tid := 0) (instruction := .addImm32 .rax 0xff false) (af := af) (profile := profile)
    (result := arithmetic profile af) (code := bytes) (base := 393216)
    (literal := ⟨2, 393221, .ok 0x11223344⟩) (queued_valid profile) ready code
    (by cases profile <;> decide +kernel)
    (by cases profile <;> cases af <;> decide +kernel) (arithmetic_actual profile af)

private theorem arithmetic_worker_present (profile : Profile) (af : Bool) :
    ((arithmetic profile af).1.workers[0]?).isSome = true := by
  cases profile <;> cases af <;> decide +kernel

private def branchWorker (profile : Profile) (af : Bool) : Worker :=
  ((arithmetic profile af).1.workers[0]?).get (arithmetic_worker_present profile af)

private theorem branch_live (profile : Profile) (af : Bool) :
    (arithmetic profile af).1.workers[0]? = some (branchWorker profile af) :=
  found_ok (α := Worker) ((arithmetic profile af).1.workers[0]?)
    (arithmetic_worker_present profile af)

/-- The head-to-issue law lifts an actual legacy JNZ over the pending
store. Reification covers the entire CPU; the independent finite observation
requires the signed target, the computed value two and the buffered word. -/
theorem backedge_head_reifies_actual_local_cpu (profile : Profile) (af : Bool) :
    ∃ output,
      Sequential.stepWith (Sequential.FlagChoices.uniform (!af))
          (localCPU (arithmetic profile af).1 (branchWorker profile af)) =
        .ok ⟨.next output, []⟩ ∧
      Reifies 0 (backedge profile af) ⟨.next output, []⟩ ∧
      scalarSnapshot output = ⟨2, 393218, .ok 0x11223344⟩ ∧
      (backedge profile af).1.world = (arithmetic profile af).1.world ∧
      WellFormed (backedge profile af).1 profile := by
  have dispatch : decode (fetchCPU (arithmetic profile af).1 (branchWorker profile af)) =
      .ok (.ordinary (.legacy (.jnz 0xfb))) :=
    ordinary_snapshot (decode (fetchCPU (arithmetic profile af).1 (branchWorker profile af)))
      (.legacy (.jnz 0xfb)) (by cases profile <;> cases af <;> decide +kernel)
  have ready : OrdinaryReady (arithmetic profile af).1 0 (branchWorker profile af)
      (.legacy (.jnz 0xfb)) profile :=
    ready_noReads (state := (arithmetic profile af).1) (worker := branchWorker profile af)
      (tid := 0) (instruction := .legacy (.jnz 0xfb)) (profile := profile)
      (arithmetic_valid profile af) (branch_live profile af)
      (by cases profile <;> cases af <;> decide +kernel) dispatch rfl
      (by cases profile <;> cases af <;> decide +kernel) rfl rfl
  have code : CodeAt (localCPU (arithmetic profile af).1 (branchWorker profile af)).memory
      393216 bytes :=
    code_of_finite (memory := (localCPU (arithmetic profile af).1 (branchWorker profile af)).memory)
      (base := 393216) (code := bytes) (by decide +kernel)
      (by cases profile <;> cases af <;> decide +kernel)
  exact checked_next (state := (arithmetic profile af).1) (worker := branchWorker profile af)
    (tid := 0) (instruction := .legacy (.jnz 0xfb)) (af := !af) (profile := profile)
    (result := backedge profile af) (code := bytes) (base := 393216)
    (literal := ⟨2, 393218, .ok 0x11223344⟩) (arithmetic_valid profile af) ready code
    (by cases profile <;> cases af <;> decide +kernel)
    (by cases profile <;> cases af <;> decide +kernel) (backedge_actual profile af)

/-- Two DWORD stores precede the same counted loop. The second captures EAX=3
before arithmetic changes it; its different address makes FIFO reversal visible. -/
private theorem fifo_setup_present :
    (setup 0x75ffc08301893289 0x909090909090c3fb).toOption.isSome = true := by
  decide +kernel

private def fifoInitial : OS.TSO64.State :=
  ((setup 0x75ffc08301893289 0x909090909090c3fb).toOption.get fifo_setup_present).state

private def fifo (profile : Profile) (af : Bool) :
    Except Fault (MemoryStatus × MemoryStatus × MemoryStatus ×
      Option (Nat × Store) × Option (Nat × Store) × List Nat) := do
  let before ← schedule fifoInitial
    [.issue 0 false, .issue 0 true, .issue 0 af, .issue 0 (!af),
      .issue 0 af, .issue 0 (!af), .issue 0 af, .issue 0 (!af), .issue 0 af] profile
  let first ← drain before.1 0 profile
  let last ← drain first.1 0 profile
  return (memoryStatus before.1, memoryStatus first.1, memoryStatus last.1,
    drainedStore first.2, drainedStore last.2,
    (before.2 ++ [first.2, last.2]).map Observation.retired)

-- Stage concrete tuple equality to keep synthesis within the unchanged recursion bound.
private instance : DecidableEq (Nat × Store) := inferInstance
private instance : DecidableEq (Option (Nat × Store)) := inferInstance
private instance : DecidableEq (Option (Nat × Store) × List Nat) := inferInstance
private instance : DecidableEq
    (Option (Nat × Store) × Option (Nat × Store) × List Nat) := inferInstance
private instance : DecidableEq
    (MemoryStatus × Option (Nat × Store) × Option (Nat × Store) × List Nat) := inferInstance
private instance : DecidableEq
    (MemoryStatus × MemoryStatus × Option (Nat × Store) × Option (Nat × Store) × List Nat) :=
  inferInstance
private instance : DecidableEq
    (MemoryStatus × MemoryStatus × MemoryStatus ×
      Option (Nat × Store) × Option (Nat × Store) × List Nat) := inferInstance
private instance : DecidableEq
    (Except Fault (MemoryStatus × MemoryStatus × MemoryStatus ×
      Option (Nat × Store) × Option (Nat × Store) × List Nat)) := inferInstance

/-- The first drain exposes only the oldest low DWORD. The second publishes
the pre-arithmetic high DWORD, then enables collection of the computed zero. -/
theorem loop_fifo_publication_order (profile : Profile) (af : Bool) :
    fifo profile af = .ok
      (⟨.ok 0, some (.ok 0x0000000311223344),
          some [⟨131072, .dword 0x11223344⟩, ⟨131076, .dword 3⟩],
          some 2, .error .resource⟩,
        ⟨.ok 0x11223344, some (.ok 0x0000000311223344),
          some [⟨131076, .dword 3⟩], some 2, .error .resource⟩,
        ⟨.ok 0x0000000311223344, some (.ok 0x0000000311223344),
          some [], some 2, .ok 0⟩,
        some (0, ⟨131072, .dword 0x11223344⟩),
        some (0, ⟨131076, .dword 3⟩), [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0]) := by
  cases profile <;> cases af <;> decide +kernel

/-- Obtain the actual code allocation ticket from the fixture's existing loan,
then borrow just EB 02 from that same RX allocation through the checked API. -/
private def shortLoanSetup : Except Fault Prepared := do
  let ready ← (TSO64.fixture 0x909090c3909002eb 0x9090909090909090 19).mapError Fault.os
  let some original := ready.checked.world.legacy.shared.loans ready.codeA | throw .resource
  let (checked, code) ←
    (TSO64.borrow ready.checked 23 original.ticket 11 ⟨393216, 2⟩).mapError Fault.os
  let empty : OS.TSO64.State := ⟨checked.world, []⟩
  match attached : attach empty 11 (TSO64.context 262144 131072 0x11223344 3)
      code ready.callerA [ready.dataA] [ready.atomicA] with
  | .error fault => .error fault
  | .ok state => .ok ⟨state, fun profile =>
      attach_valid_for (state := empty) (after := state) profile
        ⟨checked.valid, by
          intro worker member
          change worker ∈ ([] : List Worker) at member
          cases member⟩ attached⟩

private theorem short_loan_present : shortLoanSetup.toOption.isSome = true := by decide +kernel
private def shortLoanInitial : OS.TSO64.State :=
  (shortLoanSetup.toOption.get short_loan_present).state

private structure LoanSnapshot where
  pc : Word
  label : Observation
  loan : OS.AddressSpace.Region
  globalFetch : Except Error Byte
  globalDecode : Option Sequential.Instruction
  nextIssue : Except Fault Unit
  deriving DecidableEq

private def loanEscape (profile : Profile) (af : Bool) : Except Fault LoanSnapshot := do
  let jumped ← step shortLoanInitial (.issue 0 af) profile
  let some worker := jumped.1.workers[0]? | throw .missingWorker
  return ⟨worker.context.rip, jumped.2, worker.resources.code.loan.region,
    fetchByte (published jumped.1.world) 393220,
    (Sequential.decodeAt (sharedCPU jumped.1 worker)).toOption,
    (step jumped.1 (.issue 0 (!af)) profile).map (fun _ => ())⟩

/-- EB 02 succeeds inside a two-byte retained loan. Its target RET is globally
executable in the very same allocation, but the next original-loan fetch fails. -/
theorem branch_cannot_expand_original_code_loan (profile : Profile) (af : Bool) :
    loanEscape profile af = .ok
      ⟨393220, .ordinary 0, ⟨393216, 2⟩, .ok 0xc3, some (.legacy .ret),
        .error (.machine (.inaccessibleInstruction 393220))⟩ := by
  cases profile <;> cases af <;> decide +kernel

private def rejected (first : Word) (profile : Profile) (af : Bool) : Except Fault Unit := do
  let ready ← (TSO64.fixture first 0x9090909090909090 0x11223344ffffffff).mapError Fault.os
  let state ← TSO64.start ready 0x11223344 0x55667788 3
  let _ ← step state (.issue 0 af) profile
  return ()

/-- Actual mapped IMUL64 bytes cannot acquire correlated undefined flags from
the scheduler's Bool action. DWORD memory XCHG cannot become a qword RMW. -/
theorem vector_imul_and_dword_xchg_rejected (profile : Profile) (af : Bool) :
    rejected 0x909090c3c6af0f48 profile af = .error .unsupported ∧
    rejected 0x9090909090c30787 profile af = .error .unsupported := by
  cases profile <;> cases af <;> exact ⟨by decide +kernel, by decide +kernel⟩

#print axioms loop_returns_zero_before_publication
#print axioms explicit_drain_publishes_literal_dword
#print axioms arithmetic_head_reifies_actual_local_cpu
#print axioms backedge_head_reifies_actual_local_cpu
#print axioms loop_fifo_publication_order
#print axioms branch_cannot_expand_original_code_loan
#print axioms vector_imul_and_dword_xchg_rejected

end EDSL.Tests.TSO64ScalarControl

#audit_edsl
