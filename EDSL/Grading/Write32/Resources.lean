/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Write32.Contract
import EDSL.OS.WordResources

set_option warningAsError true

namespace EDSL.Grading.Write32
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS
open EDSL.Grading.Trace

/-- Registration resource descriptor fixes the seed and immutable call
handles. Every actual step uses a separate current evolving OS state. -/
structure Resources where
  seed : Borrowing.State
  call : EDSL.OS.WordResources.Call
  argument : Word
  oldValue : BitVec 32

def resourceInput (resource : Resources) : Input :=
  ⟨resource.call.targetPointer, resource.argument, resource.oldValue, resource.call.returnAddress⟩

/-- Present current resources and fixed ABI inputs. Every resource contract
fact here is checked before execution; trace policy is solely Claim evidence. -/
structure ResourcePre (bytes : List Byte) (resource : Resources) (initial : State) : Prop where
  current : EDSL.OS.WordResources.Current resource.call resource.seed initial
  code : resource.call.bytes = bytes
  entry : initial.rip = resource.call.code
  stack : initial.registers .rsp = resource.call.stack
  pointer : initial.registers .rdi = resource.call.targetPointer
  source : initial.registers .rsi = resource.argument
  oldValue : loadDWord initial.memory resource.call.targetPointer = .ok resource.oldValue

theorem ResourcePre.machine {bytes resource initial} (pre : ResourcePre bytes resource initial) :
    Pre bytes (resourceInput resource) initial := by
  have contract := pre.current.contract
  refine ⟨?_, pre.pointer, pre.source, pre.oldValue, ?_, ?_, ?_, ?_,
    contract.returnCanonical, ?_, ?_⟩
  · rw [pre.current.coupled, pre.entry, ← pre.code]
    exact contract.code
  · rw [pre.current.coupled]
    exact contract.word.writable
  · rw [pre.entry, ← pre.code]
    exact contract.codeDisjoint
  · rw [pre.stack]
    exact contract.stackDisjoint
  · rw [pre.current.coupled, pre.stack]
    exact contract.stack
  · rw [pre.stack]
    exact contract.stackBound
  · rw [pre.stack]
    exact contract.postStackCanonical

/-- Target operand reads use the CURRENT owner/ticket authorization gate,
complete-word containment and an actual successful load. Stack reads use
their current loan. No additional shared target loan is manufactured. -/
def ReadAllowed (call : EDSL.OS.WordResources.Call) (shared : Borrowing.State)
    (before : State) (read : Read) : Prop :=
  match read.kind with
  | .stack => read.address = call.stack ∧ read.bytes = 8 ∧
      ArrayResources.ReadPermission shared call.worker read
  | .data => read.address = call.targetPointer ∧ read.bytes = 4 ∧
      ∃ allocation value,
        Ownership.authorize shared.resources (Threads.principal call.worker) call.ticket = .ok allocation ∧
        Ownership.containsWord allocation call.targetPointer = true ∧
        loadDWord before.memory call.targetPointer = .ok value

/-- Existing current owner authority and all-four-byte permissions suffice
for a real readable operand, without creating a mutation-blocking loan. -/
theorem current_target_read {call : EDSL.OS.WordResources.Call} {shared before}
    (current : EDSL.OS.WordResources.Current call shared before) :
    ReadAllowed call shared before ⟨.data, call.targetPointer, 4⟩ ∧
      OperandReadSucceeds before ⟨.data, call.targetPointer, 4⟩ := by
  obtain ⟨allocation, authorized, fits⟩ := current.contract.word.authorize
  obtain ⟨value, observed⟩ := current.contract.word.load_exists
  have loaded : loadDWord before.memory call.targetPointer = .ok value := by
    rw [current.coupled]
    exact observed
  exact ⟨⟨rfl, rfl, allocation, value, authorized, fits, loaded⟩, rfl, value, loaded⟩

/-- Generic trace policy binds fixed target handles to current authority,
actual decoded store intent, successful checked mutation, and actual RAM. -/
def resourceRules (call : EDSL.OS.WordResources.Call) : Rules Borrowing.State where
  Current := EDSL.OS.WordResources.Current call
  ReadAllowed := ReadAllowed call
  Effect shared before instruction observation evolved :=
    FetchAllowed call.code call.bytes.length before instruction ∧
      EDSL.OS.WordResources.WordEffect (Threads.principal call.worker) call.ticket call.targetPointer
        shared before instruction observation evolved

def ResourcePolicy (resource : Resources) (initial : State) : Prop :=
  Policy (resourceRules resource.call) resource.seed initial

/-- Frames accumulated along the ACTUAL lifted path. All allocation owner/
epoch metadata, all loans, all cell permissions and every outside-target cell
survive. No OS-only steps, loan creation or ownership transfer are permitted. -/
structure Frame (target : Word) (seed evolved : Borrowing.State) : Prop where
  history : Borrowing.History seed evolved
  allocations : evolved.resources.allocations = seed.resources.allocations
  frontier : evolved.resources.frontier = seed.resources.frontier
  loans : evolved.loans = seed.loans
  nextLoan : evolved.nextLoan = seed.nextLoan
  permissions : ∀ query, (evolved.resources.space.cells query).map AddressSpace.Cell.permissions =
    (seed.resources.space.cells query).map AddressSpace.Cell.permissions
  outside : ∀ query, ¬(AddressSpace.wordRegion target).Contains query →
    evolved.resources.space.cells query = seed.resources.space.cells query

theorem Frame.refl (target : Word) (seed : Borrowing.State) : Frame target seed seed :=
  ⟨.refl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem history_trans {a b c : Borrowing.State}
    (first : Borrowing.History a b) (last : Borrowing.History b c) : Borrowing.History a c := by
  induction first with
  | refl => exact last
  | next step _ ih => exact .next step (ih last)

theorem Frame.trans {target : Word} {a b c : Borrowing.State}
    (first : Frame target a b) (last : Frame target b c) : Frame target a c :=
  ⟨history_trans first.history last.history,
    last.allocations.trans first.allocations, last.frontier.trans first.frontier,
    last.loans.trans first.loans, last.nextLoan.trans first.nextLoan,
    fun query => (last.permissions query).trans (first.permissions query),
    fun query outside => (last.outside query outside).trans (first.outside query outside)⟩

theorem wordEffect_frame {owner ticket target shared before instruction observation evolved}
    (effect : EDSL.OS.WordResources.WordEffect owner ticket target shared before instruction observation evolved) :
    Frame target shared evolved := by
  cases effect with
  | readOnly _ => exact Frame.refl _ _
  | store _ success =>
    have frame := Mutex.store_effect success
    exact ⟨.next (.mutate success) .refl, frame.allocations, frame.frontier,
      frame.loans, frame.nextLoan, frame.permissions, frame.outside⟩

/-- Prefix extraction gives a world chained from the registration seed at
EACH actual continuing prefix, with current code/stack/ticket and full frame. -/
theorem ResourcePolicy.prefix {resource initial} (policy : ResourcePolicy resource initial)
    {choices before count reads} (block : Block choices initial before count reads) :
    ∃ shared,
      LiftedBlock (resourceRules resource.call) choices initial resource.seed before shared count reads ∧
      EDSL.OS.WordResources.Current resource.call shared before ∧ Frame resource.call.targetPointer resource.seed shared := by
  obtain ⟨shared, lifted, current⟩ := policy_prefix policy block
  refine ⟨shared, lifted, current, ?_⟩
  exact LiftedBlock.fold (rules := resourceRules resource.call) (Frame.refl resource.call.targetPointer)
    (fun _ _ _ first last => Frame.trans first last)
    (fun _ _ _ _ _ effect => wordEffect_frame effect.2) lifted

/-- Returned witness is indexed by the same actual AF stream, initial state,
Result and whole execution. A fresh unrelated final OS world cannot satisfy
this predicate without also supplying the complete checked step chain. -/
def ResourceReturn (resource : Resources) (initial : State) (result : Result) : Prop :=
  ∀ choices, Sequential.Executes choices initial result →
    ∃ evolved,
      LiftedExecutes (resourceRules resource.call) choices initial resource.seed result evolved ∧
      EDSL.OS.WordResources.Current resource.call evolved result.state ∧
      Frame resource.call.targetPointer resource.seed evolved

theorem ResourcePolicy.returned {resource initial} (policy : ResourcePolicy resource initial)
    {result : Result} : ResourceReturn resource initial result := by
  intro choices execution
  obtain ⟨evolved, lifted, current⟩ := policy_return policy execution
  refine ⟨evolved, lifted, current, ?_⟩
  exact LiftedExecutes.fold (rules := resourceRules resource.call) (Frame.refl resource.call.targetPointer)
    (fun _ _ _ first last => Frame.trans first last)
    (fun _ _ _ _ _ effect => wordEffect_frame effect.2) lifted

/-- Every initially live unrelated loan keeps its record and exact cells at
return; the final witness comes from the actual execution, not a new world. -/
theorem ResourcePolicy.loan_frame {resource initial}
    (pre : ResourcePre bytes resource initial) (policy : ResourcePolicy resource initial)
    {choices result} (execution : Sequential.Executes choices initial result) :
    ∃ evolved,
      LiftedExecutes (resourceRules resource.call) choices initial resource.seed result evolved ∧
      EDSL.OS.WordResources.Current resource.call evolved result.state ∧
      (∀ identifier loan, resource.seed.loans identifier = some loan →
        evolved.loans identifier = some loan ∧
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = resource.seed.resources.space.cells query) := by
  obtain ⟨evolved, lifted, current, frame⟩ := policy.returned choices execution
  refine ⟨evolved, lifted, current, ?_⟩
  intro identifier loan live
  have retained : evolved.loans identifier = some loan := by rw [frame.loans]; exact live
  refine ⟨retained, ?_⟩
  have below := (pre.current.contract.wellFormed.2 identifier loan live).1
  exact (frame.history.loan_stable pre.current.contract.wellFormed identifier below loan retained).2

end EDSL.Grading.Write32
