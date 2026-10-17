/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.StoreReturnValue64.Contract
import EDSL.OS.WordResources64.Span

set_option warningAsError true

namespace EDSL.Grading.StoreReturnValue64
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS EDSL.Grading.Trace
open EDSL.OS.WordResources64

/-- Present owner/ticket authority and actual width-specific successful load.
Four-byte reads may use any complete subspan of the owned target. -/
def TargetReadAllowed (call : Call) (shared : Borrowing.State) (before : State) (read : Read) : Prop :=
  match read.bytes with
  | 4 => Borrowing.Subregion (AddressSpace.wordRegion read.address) (AddressSpace.qwordRegion call.targetPointer) ∧
      ∃ allocation value,
        Ownership.authorize shared.resources (Threads.principal call.worker) call.ticket = .ok allocation ∧
        Ownership.containsWord allocation read.address = true ∧
        loadDWord before.memory read.address = .ok value
  | 8 => read.address = call.targetPointer ∧
      ∃ allocation value,
        Ownership.authorize shared.resources (Threads.principal call.worker) call.ticket = .ok allocation ∧
        Ownership.containsQWord allocation read.address = true ∧
        loadQWord before.memory read.address = .ok value
  | _ => False

/-- Current held loans remain real read authority for supported DATA4/8,
including code, caller-stack and unrelated loans. STACK reads keep the original
eight-byte caller-slot rule. No target loan is manufactured. -/
def ReadAllowed (call : Call) (shared : Borrowing.State) (before : State) (read : Read) : Prop :=
  match read.kind with
  | .stack => read.address = call.stack ∧ read.bytes = 8 ∧
      ArrayResources.ReadPermission shared call.worker read
  | .data => TargetReadAllowed call shared before read ∨
      ((read.bytes = 4 ∨ read.bytes = 8) ∧
        ArrayResources.ReadPermission shared call.worker read ∧ OperandReadSucceeds before read)

theorem current_subword_read {call : Call} {shared : Borrowing.State} {before : State}
    {address : Word} (current : Current call shared before)
    (span : Borrowing.Subregion (AddressSpace.wordRegion address) (AddressSpace.qwordRegion call.targetPointer)) :
    ReadAllowed call shared before ⟨.data, address, 4⟩ ∧
      OperandReadSucceeds before ⟨.data, address, 4⟩ := by
  have word := current.contract.word.subword span
  obtain ⟨allocation, authorized, fits⟩ := word.authorize
  obtain ⟨value, observed⟩ := word.load_exists
  have loaded : loadDWord before.memory address = .ok value := by
    rw [current.coupled]
    exact observed
  exact ⟨Or.inl ⟨span, allocation, value, authorized, fits, loaded⟩, rfl, value, loaded⟩

theorem current_target_read {call : Call} {shared : Borrowing.State} {before : State}
    (current : Current call shared before) :
    ReadAllowed call shared before ⟨.data, call.targetPointer, 8⟩ ∧
      OperandReadSucceeds before ⟨.data, call.targetPointer, 8⟩ := by
  obtain ⟨allocation, authorized, fits⟩ := current.contract.word.authorize
  obtain ⟨value, observed⟩ := current.contract.word.load_exists
  have loaded : loadQWord before.memory call.targetPointer = .ok value := by
    rw [current.coupled]
    exact observed
  exact ⟨Or.inl ⟨rfl, allocation, value, authorized, fits, loaded⟩, value, loaded⟩

/-- A held read-only loan supplies actual data, with no write permission.
Recorded width chooses the corresponding real machine load primitive. -/
theorem current_loan_read {call : Call} {shared : Borrowing.State} {before : State}
    {address : Word} {width : Nat} (current : Current call shared before)
    (supported : width = 4 ∨ width = 8)
    (permission : ArrayResources.ReadPermission shared call.worker ⟨.data, address, width⟩) :
    ReadAllowed call shared before ⟨.data, address, width⟩ ∧
      OperandReadSucceeds before ⟨.data, address, width⟩ := by
  have succeeds : OperandReadSucceeds before ⟨.data, address, width⟩ := by
    obtain ⟨identifier, loan, authorized, span⟩ := permission
    rcases supported with width | width
    · subst width
      obtain ⟨value, loaded⟩ := Borrowing.loadWord_exists shared _ identifier address loan
        current.contract.wellFormed authorized span
      obtain ⟨_, _, _, observed⟩ := Borrowing.loadWord_ok _ _ _ _ _ loaded
      exact ⟨rfl, value, by rw [current.coupled]; exact observed⟩
    · subst width
      obtain ⟨value, loaded⟩ := Borrowing.loadWord64_exists shared _ identifier address loan
        current.contract.wellFormed authorized span
      obtain ⟨_, _, _, observed⟩ := Borrowing.loadWord64_ok _ _ _ _ _ loaded
      exact ⟨value, by rw [current.coupled]; exact observed⟩
  exact ⟨Or.inr ⟨supported, permission, succeeds⟩, succeeds⟩

/-- Current unborrowed ownership excludes ANY held read loan covering a byte
of the target allocation, independently of how many readable neighbors exist. -/
theorem current_no_target_loan_read {call : Call} {shared : Borrowing.State} {before : State}
    (current : Current call shared before) {read : Read}
    (positive : 0 < read.bytes)
    (inside : (AddressSpace.qwordRegion call.targetPointer).Contains read.address)
    (permission : ArrayResources.ReadPermission shared call.worker read) : False := by
  obtain ⟨identifier, loan, authorized, fits⟩ := permission
  have live := (Borrowing.authorize_ok _ _ _ _ authorized).1
  obtain ⟨allocation, found, _, _, contains, _⟩ := current.contract.word
  obtain ⟨borrowed, borrowedAt, _, _, loanSpan, _, _⟩ :=
    (current.contract.wellFormed.2 _ _ live).2
  have different := (current.contract.unborrowed _ _ live).symm
  have separate := current.contract.wellFormed.1.2 _ _ _ _ found borrowedAt different
  have owned := Ownership.containsQWord_inside allocation call.targetPointer read.address contains inside
  have lower := fits.1
  have upper := fits.2
  change loan.region.base.toNat ≤ read.address.toNat at lower
  change read.address.toNat + read.bytes ≤ loan.region.base.toNat + loan.region.length at upper
  have loanInside : loan.region.Contains read.address := ⟨lower, by omega⟩
  exact (Ownership.disjoint_outside separate (Borrowing.subregion_inside loanSpan loanInside)) owned

theorem readAllowed_subword_span {call : Call} {shared : Borrowing.State} {before : State}
    {address : Word} (current : Current call shared before)
    (inside : (AddressSpace.qwordRegion call.targetPointer).Contains address)
    (allowed : ReadAllowed call shared before ⟨.data, address, 4⟩) :
    Borrowing.Subregion (AddressSpace.wordRegion address) (AddressSpace.qwordRegion call.targetPointer) := by
  rcases allowed with target | ⟨_, permission, _⟩
  · exact target.1
  · exact False.elim (current_no_target_loan_read current (by change 0 < 4; decide) inside permission)

/-- Task-local ordinary effects preserve the actual width in checked histories.
Atomic RMW, syscalls and writes crossing the target are excluded. -/
inductive SpanEffect (owner : Nat) (ticket : Ownership.Ticket) (target : Word) :
    Borrowing.State → State → Sequential.Instruction → Observation → Borrowing.State → Prop where
  | readOnly {shared before instruction observation}
      (allowed : CFG.readOnly instruction = true) :
      SpanEffect owner ticket target shared before instruction observation shared
  | store32 {shared evolved before instruction observation address value}
      (intent : instruction.storeIntent before = some (address, value))
      (span : Borrowing.Subregion (AddressSpace.wordRegion address) (AddressSpace.qwordRegion target))
      (success : Borrowing.mutate shared (.store owner ticket address value) = .ok (evolved, none)) :
      SpanEffect owner ticket target shared before instruction observation evolved
  | store64 {shared evolved before instruction observation value}
      (intent : instruction.storeIntent64 before = some (target, value))
      (success : Borrowing.mutate shared (.store64 owner ticket target value) = .ok (evolved, none)) :
      SpanEffect owner ticket target shared before instruction observation evolved

theorem SpanEffect.raw {owner ticket target shared before instruction observation evolved}
    (effect : SpanEffect owner ticket target shared before instruction observation evolved) :
    RawEffect target before instruction := by
  cases effect with
  | readOnly allowed => exact .readOnly allowed
  | store32 intent span _ => exact .store32 intent span
  | store64 intent _ => exact .store64 intent
theorem spanEffect_frame {owner ticket target shared before instruction observation evolved}
    (effect : SpanEffect owner ticket target shared before instruction observation evolved) :
    Frame target shared evolved := by
  cases effect with
  | readOnly _ => exact Frame.refl _ _
  | store32 _ span success => exact Frame.store32 span success
  | store64 intent success => exact wordEffect_frame (observation := observation) (.store64 intent success)

def resourceRules (call : Call) : Rules Borrowing.State where
  Current := Current call
  ReadAllowed := ReadAllowed call
  Effect shared before instruction observation evolved :=
    FetchAllowed call.code call.bytes.length before instruction ∧
      SpanEffect (Threads.principal call.worker) call.ticket call.targetPointer
        shared before instruction observation evolved

def ResourcePolicy (resource : Resources) (initial : State) : Prop :=
  Policy (resourceRules resource.call) resource.seed initial

theorem ResourcePolicy.prefix {resource initial} (policy : ResourcePolicy resource initial)
    {choices before count reads} (block : Block choices initial before count reads) :
    ∃ shared,
      LiftedBlock (resourceRules resource.call) choices initial resource.seed before shared count reads ∧
      Current resource.call shared before ∧ Frame resource.call.targetPointer resource.seed shared := by
  obtain ⟨shared, lifted, current⟩ := policy_prefix policy block
  exact ⟨shared, lifted, current,
    LiftedBlock.fold (rules := resourceRules resource.call) (Frame.refl resource.call.targetPointer)
      (fun _ _ _ first last => Frame.trans first last)
      (fun _ _ _ _ _ effect => spanEffect_frame effect.2) lifted⟩

theorem ResourcePolicy.rejects_instruction {resource initial before}
    (policy : ResourcePolicy resource initial) (reachable : Reachable initial before)
    {instruction} (decoded : Sequential.decodeAt before = .ok instruction)
    (forbidden : ¬RawEffect resource.call.targetPointer before instruction) : False := by
  obtain ⟨_, _, _, block⟩ := reachable
  obtain ⟨Inv, start, advance⟩ := policy
  obtain ⟨ghost, _, inside⟩ := policy_prefix_invariant advance block start
  obtain ⟨_, expected, actual, enabled⟩ := advance ghost before inside
  have same := Except.ok.inj (actual.symm.trans decoded)
  cases same
  obtain ⟨_, _, _, _, effect, _⟩ := enabled false
  exact forbidden effect.2.raw

/-- Returned resources belong to the same actual path under the new rules,
including all narrow effects/reads, live loan contents and another arbitrary
full64 checked mutation. -/
def ResourceReturn (resource : Resources) (initial : State) (result : Result) : Prop :=
  ∀ choices, Sequential.Executes choices initial result →
    ∃ evolved,
      LiftedExecutes (resourceRules resource.call) choices initial resource.seed result evolved ∧
      Current resource.call evolved result.state ∧
      Frame resource.call.targetPointer resource.seed evolved ∧
      (∀ identifier loan, resource.seed.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = resource.seed.resources.space.cells query) ∧
      (∀ nextValue : Word, ∃ nextWorld,
        Borrowing.mutate evolved (.store64 (Threads.principal resource.call.worker)
          resource.call.ticket resource.call.targetPointer nextValue) = .ok (nextWorld, none))

theorem ResourcePolicy.returned {bytes resource initial} (pre : ResourcePre bytes resource initial)
    (policy : ResourcePolicy resource initial) {result : Result} :
    ResourceReturn resource initial result := by
  intro choices execution
  obtain ⟨evolved, lifted, current⟩ := policy_return policy execution
  have frame : Frame resource.call.targetPointer resource.seed evolved :=
    LiftedExecutes.fold (rules := resourceRules resource.call) (Frame.refl resource.call.targetPointer)
      (fun _ _ _ first last => Frame.trans first last)
      (fun _ _ _ _ _ effect => spanEffect_frame effect.2) lifted
  exact ⟨evolved, lifted, current, frame,
    fun _ _ live => frame.loan_contents pre.current.contract.wellFormed live,
    fun value => current_store64_enabled current value⟩

theorem readAllowed_of_strict {call shared before read}
    (allowed : WordResources64.ReadAllowed call shared before read) :
    ReadAllowed call shared before read := by
  rcases read with ⟨kind, address, bytes⟩
  cases kind with
  | stack => exact allowed
  | data =>
    obtain ⟨same, width, allocation, value, authorized, fits, loaded⟩ := allowed
    change address = call.targetPointer at same
    change bytes = 8 at width
    subst address
    subst bytes
    exact Or.inl ⟨rfl, allocation, value, authorized, fits, loaded⟩

theorem spanEffect_of_strict {owner ticket target shared before instruction observation evolved}
    (effect : WordResources64.WordEffect owner ticket target shared before instruction observation evolved) :
    SpanEffect owner ticket target shared before instruction observation evolved := by
  cases effect with
  | readOnly allowed => exact .readOnly allowed
  | store64 intent success => exact .store64 intent success

theorem resourcePolicy_of_strict {resource initial}
    (policy : EDSL.StoreLoad64.ResourcePolicy resource initial) : ResourcePolicy resource initial :=
  Policy.mono policy (fun _ _ current => current)
    (fun _ _ _ allowed => readAllowed_of_strict allowed)
    (fun _ _ _ _ _ effect => ⟨effect.1, spanEffect_of_strict effect.2⟩)

end EDSL.Grading.StoreReturnValue64
