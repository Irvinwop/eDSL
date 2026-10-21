/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.PlainResources.Manager
import EDSL.X86.CodeCheck

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.PlainResources
open X86 OS OS.AddressSpace Grading.ConcurrentTask

structure Choice where
  site : Plain64.Site
  value : Word
  counter : Nat
  occurrence : Nat

def input (choice : Choice) (target : Atomics64.CellId64) (cell : Atomics64.Cell) : Plain64.Input :=
  match choice.site.kind with
  | .loadAcquire => .loadAcquire choice.site.image target cell choice.occurrence
  | .storeRelease => .storeRelease choice.site.image target cell choice.value choice.occurrence

@[simp] theorem input_site (choice : Choice) (target : Atomics64.CellId64) (cell : Atomics64.Cell) :
    (input choice target cell).site = choice.site := by
  cases choice with
  | mk site value counter occurrence => cases site with
    | mk kind image => cases kind <;> rfl

@[simp] theorem input_target (choice : Choice) (target : Atomics64.CellId64) (cell : Atomics64.Cell) :
    (input choice target cell).target = target := by
  cases selected : choice.site.kind <;> simp only [input, selected, Plain64.Input.target]

@[simp] theorem input_cell (choice : Choice) (target : Atomics64.CellId64) (cell : Atomics64.Cell) :
    (input choice target cell).cell = cell := by
  cases selected : choice.site.kind <;> simp only [input, selected, Plain64.Input.cell]

def context (image : OS.ScalarCall64.Image) (target stack value : Word) : TSO64.Context where
  registers register := match register with
    | .rsp => stack
    | .rdi => target
    | .rsi => value
    | _ => 0x8877665544332211
  rip := image.base
  flags := 0x202

structure Checked (world : Atomics64.State) where
  state : TSO64.State
  sameWorld : state.world = world
  valid : TSO64.WellFormed state .sharedCell

private theorem attach_world {before after : TSO64.State} {actor code caller : Nat}
    {entry : TSO64.Context} {atomic : Atomics64.HandleId64}
    (success : TSO64.attach before actor entry code caller [] [atomic] = .ok after) :
    after.world = before.world := by
  cases made : TSO64.makeWorker before.world actor entry code caller [] [atomic] with
  | error fault => simp [TSO64.attach, made] at success
  | ok worker =>
    simp only [TSO64.attach, made, ok_bind, pure_ok, Except.ok.injEq] at success
    cases success
    rfl

def attach {world : Atomics64.State} (before : Checked world) (actor : Nat)
    (entry : TSO64.Context) (code caller : Nat) (atomic : Atomics64.HandleId64) :
    Except TSO64.Fault (Checked world) :=
  match success : TSO64.attach before.state actor entry code caller [] [atomic] with
  | .error fault => .error fault
  | .ok after => .ok ⟨after, (attach_world success).trans before.sameWorld,
      TSO64.attach_valid_for .sharedCell before.valid success⟩

/-- Counter labels are independent of allocation, current authority and empty
entry FIFOs. This preserves every actual attached worker field except the
requested sequence label; no resource descriptor is synthesized. -/
def setCounters {world : Atomics64.State} (before : Checked world)
    (first second : Nat) : Checked world where
  state := ⟨before.state.world, before.state.workers.map fun worker =>
    { worker with nextStore := if worker.resources.actor = 11 then first else second }⟩
  sameWorld := before.sameWorld
  valid := by
    refine ⟨before.valid.1, ?_⟩
    intro worker member
    obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
    cases same
    exact before.valid.2 original originalMember

def start {original : Space} {layout : Layout} {old : Word}
    (resources : Ready original layout old) (first second : Choice) :
    Except TSO64.Fault (Checked resources.managed.world) := do
  let before : Checked resources.managed.world :=
    ⟨⟨resources.managed.world, []⟩, rfl, resources.managed.valid, by simp⟩
  let one ← attach before 11
    (context first.site.image resources.cell.address layout.stackA first.value)
    resources.codeA resources.callerA resources.atomicA
  let two ← attach one 12
    (context second.site.image resources.cell.address layout.stackB second.value)
    resources.codeB resources.callerB resources.atomicB
  return setCounters two first.counter second.counter

structure Started {original : Space} {layout : Layout} {old : Word}
    (resources : Ready original layout old) (first second : Choice) where
  checked : Checked resources.managed.world
  performed : start resources first second = .ok checked

def checkedStart {original : Space} {layout : Layout} {old : Word}
    (resources : Ready original layout old) (first second : Choice) :
    Except TSO64.Fault (Started resources first second) :=
  match success : start resources first second with
  | .error fault => .error fault
  | .ok checked => .ok ⟨checked, success⟩

def secondArgument (chosen : Plain64.Input) (worker : TSO64.Worker) : Prop :=
  match chosen with
  | .loadAcquire .. => True
  | .storeRelease _ _ _ value _ => worker.context.registers .rsi = value

private instance (chosen : Plain64.Input) (worker : TSO64.Worker) :
    Decidable (secondArgument chosen worker) := by
  cases chosen <;> unfold secondArgument <;> infer_instance

theorem arguments_of_registers {chosen : Plain64.Input} {worker : TSO64.Worker}
    (rdi : worker.context.registers .rdi = chosen.cell.address)
    (rsi : secondArgument chosen worker) : Plain64.Arguments chosen worker := by
  intro index argument found
  by_cases zero : index.val = 0
  · simp only [Plain64.Input.argument, zero, ↓reduceIte, Option.some.injEq] at found
    cases found
    simpa only [PureCall.Argument.Holds, PureCall.argumentRegister, zero] using rdi
  · by_cases one : index.val = 1
    · cases chosen with
      | loadAcquire image target cell occurrence =>
        simp [Plain64.Input.argument, one] at found
      | storeRelease image target cell value occurrence =>
        simp only [Plain64.Input.argument, one, ↓reduceIte] at found
        cases found
        simpa only [secondArgument, PureCall.Argument.Holds, PureCall.argumentRegister, one] using rsi
    · simp [Plain64.Input.argument, zero, one] at found

private def present (chosen : Plain64.Input) (worker : TSO64.Worker) : Prop :=
  worker.phase = .running ∧ worker.context.rip = chosen.site.image.base ∧
  worker.context.registers .rdi = chosen.cell.address ∧ secondArgument chosen worker ∧
  0 < chosen.site.image.bytes.length ∧ canonical chosen.site.image.base = true ∧
  Borrowing.Subregion ⟨chosen.site.image.base, chosen.site.image.bytes.length⟩
    worker.resources.code.loan.region ∧
  worker.context.registers .rsp = worker.resources.callerAddress ∧
  ((worker.context.registers .rsp).toNat + 8) % 16 = 0 ∧
  worker.context.flags.getLsbD 10 = false ∧
  (worker.context.registers .rsp).toNat + 8 < 2^64 ∧
  canonical (worker.context.registers .rsp + 8) = true

private instance (chosen : Plain64.Input) (worker : TSO64.Worker) :
    Decidable (present chosen worker) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

structure EntryEvidence (chosen : Plain64.Input) (before : TSO64.State) (worker : TSO64.Worker) : Type where
  facts : Plain64.Entry chosen before worker

theorem caller_aligned {chosen : Plain64.Input} {before : TSO64.State} {worker : TSO64.Worker}
    (entry : Plain64.Entry chosen before worker) : worker.resources.callerAddress.toNat % 8 = 0 := by
  have aligned := entry.scalar.aligned
  rw [entry.originalRsp] at aligned
  omega

/-- Only current finite checks: actual full-width registers, complete code
bytes, current target identity/descriptor/handle, and the ORIGINAL caller loan.
There is no method, graph, selected source, execution or desired reply check. -/
def currentEntry (chosen : Plain64.Input) (before : TSO64.State) (worker : TSO64.Worker)
    (valid : Atomics64.WellFormed before.world) :
    Except TSO64.Fault (EntryEvidence chosen before worker) := do
  if basics : present chosen worker then
    if code : checkCode (TSO64.published before.world) chosen.site.image.base chosen.site.image.bytes = true then
      if live : before.world.cells chosen.target = some chosen.cell then
        match selected : TSO64.atomicFor before.world worker.resources chosen.cell.address with
        | none => throw .noAtomicGrant
        | some (identifier, handle, descriptor) =>
          if linked : descriptor = chosen.cell ∧ handle.cell = chosen.target then
            match caller : Borrowing.loadWord64 before.world.legacy.shared worker.resources.actor
                worker.resources.caller.identifier worker.resources.callerAddress with
            | .error _ => throw .callerSlot
            | .ok continuation =>
              if canonical : X86.canonical continuation = true then
                return ⟨by
                  obtain ⟨running, pc, rdi, rsi, nonempty, base, fits, rsp,
                    aligned, direction, bound, postCanonical⟩ := basics
                  exact ⟨running, pc, arguments_of_registers rdi rsi, nonempty, base,
                    checkCode_sound _ _ _ code, fits, rsp,
                    ⟨aligned, direction, bound, postCanonical⟩, live, (valid.cells _ _ live).2,
                    ⟨identifier, handle, by simpa only [linked.1] using selected, linked.2⟩,
                    ⟨continuation, caller, canonical⟩⟩⟩
              else throw .callerSlot
          else throw .noAtomicGrant
      else throw .noAtomicGrant
    else throw .codeBounds
  else throw .resource

def pairInputs (first second : Plain64.Input) : Fin 2 → Plain64.Input :=
  fun tid => if tid.val = 0 then first else second

theorem pre_pair {catalog : Plain64.Catalog} {world : Atomics64.State}
    {first second : TSO64.Worker} {inputA inputB : Plain64.Input}
    (valid : TSO64.WellFormed ⟨world, [first, second]⟩ .sharedCell)
    (members : inputA.site ∈ catalog ∧ inputB.site ∈ catalog)
    (entryA : Plain64.Entry inputA ⟨world, [first, second]⟩ first)
    (entryB : Plain64.Entry inputB ⟨world, [first, second]⟩ second)
    (privateSlots : Ownership.Disjoint first.resources.caller.loan.region second.resources.caller.loan.region)
    (separated :
      Ownership.Disjoint ⟨inputA.site.image.base, inputA.site.image.bytes.length⟩ first.resources.caller.loan.region ∧
      Ownership.Disjoint ⟨inputA.site.image.base, inputA.site.image.bytes.length⟩ second.resources.caller.loan.region ∧
      Ownership.Disjoint ⟨inputB.site.image.base, inputB.site.image.bytes.length⟩ first.resources.caller.loan.region ∧
      Ownership.Disjoint ⟨inputB.site.image.base, inputB.site.image.bytes.length⟩ second.resources.caller.loan.region) :
    Plain64.Pre catalog ⟨world, [first, second]⟩ (pairInputs inputA inputB) := by
  refine ⟨valid, ?_, ?_, ?_, ?_⟩
  · intro tid
    rcases tid with ⟨tid, bound⟩
    have cases : tid = 0 ∨ tid = 1 := by change tid < 2 at bound; omega
    rcases cases with rfl | rfl
    · exact members.1
    · exact members.2
  · intro tid
    rcases tid with ⟨tid, bound⟩
    have cases : tid = 0 ∨ tid = 1 := by change tid < 2 at bound; omega
    rcases cases with rfl | rfl
    · exact ⟨first, rfl, entryA⟩
    · exact ⟨second, rfl, entryB⟩
  · intro i j left right different atLeft atRight
    rcases i with ⟨i, boundI⟩
    rcases j with ⟨j, boundJ⟩
    have casesI : i = 0 ∨ i = 1 := by change i < 2 at boundI; omega
    have casesJ : j = 0 ∨ j = 1 := by change j < 2 at boundJ; omega
    rcases casesI with rfl | rfl <;> rcases casesJ with rfl | rfl
    all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at atLeft atRight
    all_goals subst left; subst right
    · exact False.elim (different rfl)
    · exact privateSlots
    · exact Ownership.disjoint_symm privateSlots
    · exact False.elim (different rfl)
  · intro i j caller live
    rcases i with ⟨i, boundI⟩
    rcases j with ⟨j, boundJ⟩
    have casesI : i = 0 ∨ i = 1 := by change i < 2 at boundI; omega
    have casesJ : j = 0 ∨ j = 1 := by change j < 2 at boundJ; omega
    rcases casesI with rfl | rfl <;> rcases casesJ with rfl | rfl
    all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at live
    all_goals subst caller
    · exact separated.1
    · exact separated.2.1
    · exact separated.2.2.1
    · exact separated.2.2.2

def allReadOnly (space : Space) (region : Region) : Bool :=
  region.addresses.all fun address =>
    match space.cells address with
    | none => false
    | some cell => decide (cell.permissions = readOnly)

theorem allReadOnly_inside {space : Space} {region : Region}
    (checked : allReadOnly space region = true) {address : Word} (inside : region.Contains address) :
    ∃ cell, space.cells address = some cell ∧ cell.permissions = readOnly := by
  have atAddress := List.all_eq_true.mp checked address (contains_mem_addresses region address inside)
  cases live : space.cells address with
  | none => simp [live] at atAddress
  | some cell => exact ⟨cell, rfl, of_decide_eq_true (by simpa only [live] using atAddress)⟩

structure Cohort (original : Space) (catalog : Plain64.Catalog) (layout : Layout)
    (old : Word) (first second : Choice) where
  resources : Ready original layout old
  workerA : TSO64.Worker
  workerB : TSO64.Worker
  attached : ∃ before, start resources first second = .ok before ∧
    before.state = ⟨resources.managed.world, [workerA, workerB]⟩
  pre : Plain64.Pre catalog ⟨resources.managed.world, [workerA, workerB]⟩
    (pairInputs (input first resources.target resources.cell) (input second resources.target resources.cell))
  counterA : workerA.nextStore = first.counter
  counterB : workerB.nextStore = second.counter
  emptyA : workerA.pending = []
  emptyB : workerB.pending = []
  protectedA : allReadOnly resources.managed.world.legacy.shared.resources.space
    workerA.resources.caller.loan.region = true
  protectedB : allReadOnly resources.managed.world.legacy.shared.resources.space
    workerB.resources.caller.loan.region = true

def Cohort.state {original : Space} {catalog : Plain64.Catalog} {layout : Layout}
    {old : Word} {first second : Choice} (cohort : Cohort original catalog layout old first second) :
    TSO64.State := ⟨cohort.resources.managed.world, [cohort.workerA, cohort.workerB]⟩

def Cohort.inputs {original : Space} {catalog : Plain64.Catalog} {layout : Layout}
    {old : Word} {first second : Choice} (cohort : Cohort original catalog layout old first second) :
    Fin cohort.state.workers.length → Plain64.Input :=
  pairInputs (input first cohort.resources.target cohort.resources.cell)
    (input second cohort.resources.target cohort.resources.cell)

theorem Cohort.closedPre {original : Space} {catalog : Plain64.Catalog} {layout : Layout}
    {old : Word} {first second : Choice} (cohort : Cohort original catalog layout old first second) :
    Plain64.ClosedPre catalog cohort.state cohort.inputs := by
  refine ⟨cohort.pre, ?_⟩
  intro worker member
  rcases List.mem_cons.mp member with same | member
  · cases same; exact cohort.emptyA
  · rcases List.mem_cons.mp member with same | member
    · cases same; exact cohort.emptyB
    · cases member

theorem state_pair {before : TSO64.State} {world : Atomics64.State}
    {first second : TSO64.Worker} (same : before.world = world)
    (workers : before.workers = [first, second]) : before = ⟨world, [first, second]⟩ := by
  cases before
  cases same
  cases workers
  rfl

/-- Construct useful finite current cohorts through actual setup and attach.
Failure is explicit: unavailable mappings, overlap, unsupported addresses,
wrong permissions/resources/caller values or present entry mismatches produce
an error. The only checks after setup concern independently defined `Pre` data.
No whole Claim or successful future execution is an input. -/
def construct (original : Space) (catalog : Plain64.Catalog) (first second : Choice)
    (layout : Layout) (old : Word) : Except TSO64.Fault (Cohort original catalog layout old first second) := do
  let resources ← (setup original first.site.image second.site.image layout old).mapError TSO64.Fault.os
  let attached ← checkedStart resources first second
  let before := attached.checked
  match workers : before.state.workers with
  | [workerA, workerB] =>
    let pair : TSO64.State := ⟨resources.managed.world, [workerA, workerB]⟩
    have same : before.state = pair := state_pair before.sameWorld workers
    have valid : TSO64.WellFormed pair .sharedCell := by simpa only [same] using before.valid
    let inputA := input first resources.target resources.cell
    let inputB := input second resources.target resources.cell
    let entryA ← currentEntry inputA pair workerA valid.1
    let entryB ← currentEntry inputB pair workerB valid.1
    if members : inputA.site ∈ catalog ∧ inputB.site ∈ catalog then
      if privateSlots : Ownership.Disjoint workerA.resources.caller.loan.region workerB.resources.caller.loan.region then
        if separated :
            Ownership.Disjoint ⟨inputA.site.image.base, inputA.site.image.bytes.length⟩ workerA.resources.caller.loan.region ∧
            Ownership.Disjoint ⟨inputA.site.image.base, inputA.site.image.bytes.length⟩ workerB.resources.caller.loan.region ∧
            Ownership.Disjoint ⟨inputB.site.image.base, inputB.site.image.bytes.length⟩ workerA.resources.caller.loan.region ∧
            Ownership.Disjoint ⟨inputB.site.image.base, inputB.site.image.bytes.length⟩ workerB.resources.caller.loan.region then
          if controls : workerA.nextStore = first.counter ∧ workerB.nextStore = second.counter ∧
              workerA.pending = [] ∧ workerB.pending = [] then
            if protection : allReadOnly pair.world.legacy.shared.resources.space workerA.resources.caller.loan.region = true ∧
                allReadOnly pair.world.legacy.shared.resources.space workerB.resources.caller.loan.region = true then
              return ⟨resources, workerA, workerB, ⟨before, attached.performed, same⟩,
                pre_pair valid members entryA.facts entryB.facts privateSlots separated,
                controls.1, controls.2.1, controls.2.2.1, controls.2.2.2, protection.1, protection.2⟩
            else throw .callerSlot
          else throw .resource
        else throw .codeBounds
      else throw .callerSlot
    else throw .unsupported
  | _ => throw .missingWorker

end EDSL.Corpus.PlainResources

#audit_edsl
