/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.StackFrame
import EDSL.X86.CallReturn.Execution

set_option warningAsError true

namespace EDSL.OS.StackFrame.CPU
open X86 AddressSpace

/-- Couple a real checked CPU store to the actual owner mutation. The OS
endpoint is the result of that mutation and has exactly the CPU's full RAM. -/
theorem store_current {frame : Descriptor} {shared : Shared} {before after : X86.State}
    {address value : Word} (current : Current frame shared before) (slot : Slot frame address)
    (stored : storeQWord before.memory address value = .ok after.memory) :
    ∃ evolved, Borrowing.mutate shared (.store64 frame.owner frame.ticket address value) =
        .ok (evolved, none) ∧
      Current frame evolved after ∧ PrivateWrite frame shared evolved ∧
      Borrowing.StoreEffect64 shared evolved address value := by
  obtain ⟨evolved, success⟩ := current_store64_enabled current slot value
  have effect := Borrowing.store64_effect success
  have machineStore : storeQWord (toMemory shared.resources.space) address value =
      .ok after.memory := by rwa [← current.coupled]
  have coupled : after.memory = toMemory evolved.resources.space :=
    Except.ok.inj (machineStore.symm.trans effect.machine)
  exact ⟨evolved, success, ⟨(contract_store64 current.contract success).1, coupled⟩,
    .store64 slot success, effect⟩

/-- CALL return-address stores use private stack authority, independently of
ordinary DATA store intents. The exact target and return word are CPU-derived. -/
theorem call_current {frame : Descriptor} {shared : Shared} {before after : X86.State}
    {displacement : BitVec 32} {af : Bool} {reads : List CallReturn.Read}
    (current : Current frame shared before) (slot : Slot frame (CallReturn.stackDestination before))
    (actual : CallReturn.execute before (.callRelative32 displacement) af =
      .ok ⟨.next after, reads⟩) :
    ∃ evolved, Borrowing.mutate shared (.store64 frame.owner frame.ticket
        (CallReturn.stackDestination before) (CallReturn.returnAddress before)) = .ok (evolved, none) ∧
      Current frame evolved after ∧ PrivateWrite frame shared evolved ∧
      Borrowing.StoreEffect64 shared evolved (CallReturn.stackDestination before)
        (CallReturn.returnAddress before) :=
  store_current current slot (CallReturn.execute_call_context actual).2.1

/-- PUSH uses the old source register, including PUSH RSP, as the actual CPU
semantics do. This grants no ordinary DATA store permission. -/
theorem push_current {frame : Descriptor} {shared : Shared} {before after : X86.State}
    {source : Register} {prefixed af : Bool} {reads : List CallReturn.Read}
    (current : Current frame shared before) (slot : Slot frame (CallReturn.stackDestination before))
    (actual : CallReturn.execute before (.push64 source prefixed) af = .ok ⟨.next after, reads⟩) :
    ∃ evolved, Borrowing.mutate shared (.store64 frame.owner frame.ticket
        (CallReturn.stackDestination before) (before.registers source)) = .ok (evolved, none) ∧
      Current frame evolved after ∧ PrivateWrite frame shared evolved ∧
      Borrowing.StoreEffect64 shared evolved (CallReturn.stackDestination before)
        (before.registers source) :=
  store_current current slot (CallReturn.execute_push_context actual).1

/-- Successful POP observes the currently owned word and preserves the same OS
world. In particular the read creates no loan that could freeze a later CALL. -/
theorem pop_current {frame : Descriptor} {shared : Shared} {before after : X86.State}
    {destination : Register} {prefixed af : Bool} {reads : List CallReturn.Read}
    (current : Current frame shared before) (slot : Slot frame (before.registers .rsp))
    (actual : CallReturn.execute before (.pop64 destination prefixed) af = .ok ⟨.next after, reads⟩) :
    Current frame shared after ∧
      Borrowing.loadOwnedWord64 shared frame.owner frame.ticket (before.registers .rsp) =
        .ok (after.registers destination) ∧
      (∀ read, read ∈ reads → ReadAllowed frame shared read) := by
  obtain ⟨value, owned, loaded, _, allowed⟩ := current_privateSlot current slot
  have facts := CallReturn.execute_pop_context actual
  have same : value = after.registers destination := Except.ok.inj (loaded.symm.trans facts.1)
  refine ⟨current.sameMemory facts.2.2.2.2.1, by rwa [← same], ?_⟩
  intro read member
  rw [facts.2.2.2.2.2.1] at member
  exact List.mem_singleton.mp member ▸ allowed

/-- A private RET reads actual current owned RAM; a ghost target cannot replace
it. This lemma deliberately requires the CPU's actual canonicality check. -/
theorem private_ret_current {frame : Descriptor} {shared : Shared} {before after : X86.State}
    {af : Bool} {reads : List CallReturn.Read}
    (current : Current frame shared before) (slot : Slot frame (before.registers .rsp))
    (actual : CallReturn.execute before (.sequential (.legacy .ret)) af =
      .ok ⟨.returned after, reads⟩) :
    Current frame shared after ∧
      Borrowing.loadOwnedWord64 shared frame.owner frame.ticket (before.registers .rsp) = .ok after.rip ∧
      (∀ read, read ∈ reads → ReadAllowed frame shared read) := by
  obtain ⟨target, loaded, _, state, readTrace⟩ := CallReturn.execute_ret_success_iff.mp actual
  obtain ⟨value, owned, observed, _, allowed⟩ := current_privateSlot current slot
  have same : value = target := Except.ok.inj (observed.symm.trans loaded)
  subst after
  refine ⟨current.sameMemory rfl, by simpa only [← same] using owned, ?_⟩
  intro read member
  rw [readTrace] at member
  exact List.mem_singleton.mp member ▸ allowed

/-- The retained original caller loan supplies the terminal RET without any
private-slot authority. Its target remains the actual immutable caller word. -/
theorem original_ret {frame : Descriptor} {shared : Shared} {before : X86.State}
    (current : Current frame shared before) (original : before.registers .rsp = frame.top) (af : Bool) :
    CallReturn.execute before (.sequential (.legacy .ret)) af =
      .ok ⟨.returned { before.writeRegister .rsp (before.registers .rsp + 8) with
        rip := frame.call.returnAddress }, [⟨.stack, before.registers .rsp, 8⟩]⟩ ∧
      ReadAllowed frame shared ⟨.stack, before.registers .rsp, 8⟩ := by
  refine ⟨CallReturn.execute_ret_success_iff.mpr ⟨frame.call.returnAddress, ?_,
    current.contract.pureCall.returnCanonical, rfl, rfl⟩, ?_⟩
  · rw [original]
    exact current.originalStack
  · rw [original]
    exact originalStack_readAllowed current.contract

/-- Complete natural slot containment makes a private RET strictly below the
frozen original slot; this is independent of code position and target value. -/
theorem private_not_original {frame : Descriptor} {shared : Shared} {before : X86.State}
    (current : Current frame shared before) (slot : Slot frame (before.registers .rsp)) :
    before.registers .rsp ≠ frame.top := by
  have bounds := current.contract.slot_bounds slot
  intro same
  rw [same] at bounds
  omega

/-- CPU effects carry the actual checked owner mutation. Other instructions
must establish both absence of a store intent in this sibling ISA and exact
full-memory equality. Atomic/ordinary DATA writers need another resource rule. -/
inductive Effect (frame : Descriptor) : Shared → Shared → X86.State → X86.State →
    CallReturn.Instruction → Prop where
  | call {shared evolved before after displacement}
      (slot : Slot frame (CallReturn.stackDestination before))
      (success : Borrowing.mutate shared (.store64 frame.owner frame.ticket
        (CallReturn.stackDestination before) (CallReturn.returnAddress before)) = .ok (evolved, none)) :
      Effect frame shared evolved before after (.callRelative32 displacement)
  | push {shared evolved before after source prefixed}
      (slot : Slot frame (CallReturn.stackDestination before))
      (success : Borrowing.mutate shared (.store64 frame.owner frame.ticket
        (CallReturn.stackDestination before) (before.registers source)) = .ok (evolved, none)) :
      Effect frame shared evolved before after (.push64 source prefixed)
  | unchanged {shared before after instruction}
      (noWrite : instruction.writeEffect before = none)
      (memory : after.memory = before.memory) :
      Effect frame shared shared before after instruction

/-- The decoded instruction, actual raw execution, boundary observation and OS
effect all share their exact pre-state. RAM-derived internal RET is relabeled
only by the concrete frozen-slot adapter. -/
def Step (frame : Descriptor) (shared evolved : Shared) (before after : X86.State)
    (af : Bool) (observation : CallReturn.Observation) : Prop :=
  ∃ instruction raw, CallReturn.decodeAt before = .ok instruction ∧
    CallReturn.execute before instruction af = .ok raw ∧
    CallReturn.cpu raw.result = some after ∧
    observation = CallReturn.atBoundary frame.top before raw ∧
    Effect frame shared evolved before after instruction ∧
    ∀ read, read ∈ raw.reads → ReadAllowed frame shared read

theorem Step.machine {frame shared evolved before after af observation}
    (step : Step frame shared evolved before after af observation) :
    CallReturn.boundaryStep frame.top af before = .ok observation := by
  obtain ⟨instruction, raw, decoded, actual, _, observed, _, _⟩ := step
  exact CallReturn.boundaryStep_success_iff.mpr
    ⟨raw, (CallReturn.rawStep_eq_execute af decoded).trans actual, observed⟩

theorem Step.cpu {frame shared evolved before after af observation}
    (step : Step frame shared evolved before after af observation) :
    CallReturn.cpu observation.result = some after := by
  obtain ⟨_, raw, _, _, result, observed, _, _⟩ := step
  subst observation
  exact (CallReturn.atBoundary_cpu _ _ raw).trans result

theorem Step.reads {frame shared evolved before after af observation}
    (step : Step frame shared evolved before after af observation) :
    ∀ read, read ∈ observation.reads → ReadAllowed frame shared read := by
  obtain ⟨_, raw, _, _, _, observed, _, reads⟩ := step
  subst observation
  simpa only [CallReturn.atBoundary_reads] using reads

/-- Every OS write in a checked CPU step comes from that step's actual CALL or
PUSH, while read-only steps retain the exact same world. -/
theorem Step.history {frame shared evolved before after af observation}
    (step : Step frame shared evolved before after af observation) :
    PrivateHistory frame shared evolved := by
  obtain ⟨_, _, _, _, _, _, effect, _⟩ := step
  cases effect with
  | call slot success | push slot success => exact .next (.store64 slot success) .refl
  | unchanged _ _ => exact .refl

theorem Step.current {frame shared evolved before after af observation}
    (step : Step frame shared evolved before after af observation)
    (current : Current frame shared before) : Current frame evolved after := by
  obtain ⟨instruction, raw, _, actual, cpu, _, effect, _⟩ := step
  cases effect with
  | call slot success =>
    obtain ⟨_, memory, stored, same⟩ := CallReturn.execute_call_success_iff.mp actual
    subst raw
    have afterEq : CallReturn.callState before _ memory = after := Option.some.inj cpu
    have effect := Borrowing.store64_effect success
    refine ⟨(contract_store64 current.contract success).1, ?_⟩
    have sameStore : storeQWord (toMemory shared.resources.space)
        (CallReturn.stackDestination before) (CallReturn.returnAddress before) = .ok memory := by
      rwa [← current.coupled]
    have memoryEq := Except.ok.inj (sameStore.symm.trans effect.machine)
    rw [← afterEq]
    exact memoryEq
  | push slot success =>
    obtain ⟨memory, stored, same⟩ := CallReturn.execute_push_success_iff.mp actual
    subst raw
    have afterEq : CallReturn.pushState before _ memory = after := Option.some.inj cpu
    have effect := Borrowing.store64_effect success
    refine ⟨(contract_store64 current.contract success).1, ?_⟩
    have sameStore := stored
    rw [current.coupled] at sameStore
    have memoryEq := Except.ok.inj (sameStore.symm.trans effect.machine)
    rw [← afterEq]
    exact memoryEq
  | unchanged _ memory => exact current.sameMemory memory

theorem call_step {frame : Descriptor} {shared : Shared} {before after : X86.State}
    {displacement : BitVec 32} {af : Bool} {reads : List CallReturn.Read}
    (current : Current frame shared before) (slot : Slot frame (CallReturn.stackDestination before))
    (decoded : CallReturn.decodeAt before = .ok (.callRelative32 displacement))
    (actual : CallReturn.execute before (.callRelative32 displacement) af = .ok ⟨.next after, reads⟩) :
    ∃ evolved, Step frame shared evolved before after af ⟨.next after, reads⟩ := by
  obtain ⟨evolved, success, _, _, _⟩ := call_current current slot actual
  refine ⟨evolved, .callRelative32 displacement, ⟨.next after, reads⟩,
    decoded, actual, rfl, rfl, .call slot success, ?_⟩
  intro read member
  rw [(CallReturn.execute_call_context actual).2.2.2.2.2.1] at member
  cases member

theorem push_step {frame : Descriptor} {shared : Shared} {before after : X86.State}
    {source : Register} {prefixed af : Bool} {reads : List CallReturn.Read}
    (current : Current frame shared before) (slot : Slot frame (CallReturn.stackDestination before))
    (decoded : CallReturn.decodeAt before = .ok (.push64 source prefixed))
    (actual : CallReturn.execute before (.push64 source prefixed) af = .ok ⟨.next after, reads⟩) :
    ∃ evolved, Step frame shared evolved before after af ⟨.next after, reads⟩ := by
  obtain ⟨evolved, success, _, _, _⟩ := push_current current slot actual
  refine ⟨evolved, .push64 source prefixed, ⟨.next after, reads⟩,
    decoded, actual, rfl, rfl, .push slot success, ?_⟩
  intro read member
  rw [(CallReturn.execute_push_context actual).2.2.2.2.1] at member
  cases member

/-- Present current resources and target canonicality construct the CALL's
successful checked store and actual CPU/OS step; no future success is assumed. -/
theorem call_enabled {frame : Descriptor} {shared : Shared} {before : X86.State}
    (current : Current frame shared before) (slot : Slot frame (CallReturn.stackDestination before))
    (displacement : BitVec 32) (af : Bool)
    (decoded : CallReturn.decodeAt before = .ok (.callRelative32 displacement))
    (canonicalTarget : canonical (CallReturn.callTarget before displacement) = true) :
    ∃ evolved, let after := CallReturn.callState before displacement (toMemory evolved.resources.space)
      CallReturn.execute before (.callRelative32 displacement) af = .ok ⟨.next after, []⟩ ∧
      Step frame shared evolved before after af ⟨.next after, []⟩ ∧
      Current frame evolved after ∧
      Borrowing.mutate shared (.store64 frame.owner frame.ticket
        (CallReturn.stackDestination before) (CallReturn.returnAddress before)) = .ok (evolved, none) := by
  obtain ⟨evolved, success⟩ := current_store64_enabled current slot (CallReturn.returnAddress before)
  have stored := (Borrowing.store64_effect success).machine
  rw [← current.coupled] at stored
  have actual := CallReturn.execute_call before displacement af _ canonicalTarget stored
  have step : Step frame shared evolved before
      (CallReturn.callState before displacement (toMemory evolved.resources.space)) af
      ⟨.next (CallReturn.callState before displacement (toMemory evolved.resources.space)), []⟩ :=
    ⟨.callRelative32 displacement, _, decoded, actual, rfl, rfl, .call slot success,
      by intro read member; cases member⟩
  exact ⟨evolved, actual, step, step.current current, success⟩

/-- PUSH is enabled by present private-slot authority for any source word.
The source is evaluated before either the CPU or OS stack store occurs. -/
theorem push_enabled {frame : Descriptor} {shared : Shared} {before : X86.State}
    (current : Current frame shared before) (slot : Slot frame (CallReturn.stackDestination before))
    (source : Register) (prefixed af : Bool)
    (decoded : CallReturn.decodeAt before = .ok (.push64 source prefixed)) :
    ∃ evolved, let after := CallReturn.pushState before prefixed (toMemory evolved.resources.space)
      CallReturn.execute before (.push64 source prefixed) af = .ok ⟨.next after, []⟩ ∧
      Step frame shared evolved before after af ⟨.next after, []⟩ ∧
      Current frame evolved after ∧
      Borrowing.mutate shared (.store64 frame.owner frame.ticket
        (CallReturn.stackDestination before) (before.registers source)) = .ok (evolved, none) := by
  obtain ⟨evolved, success⟩ := current_store64_enabled current slot (before.registers source)
  have stored := (Borrowing.store64_effect success).machine
  rw [← current.coupled] at stored
  have actual := CallReturn.execute_push before source prefixed af _ stored
  have step : Step frame shared evolved before
      (CallReturn.pushState before prefixed (toMemory evolved.resources.space)) af
      ⟨.next (CallReturn.pushState before prefixed (toMemory evolved.resources.space)), []⟩ :=
    ⟨.push64 source prefixed, _, decoded, actual, rfl, rfl, .push slot success,
      by intro read member; cases member⟩
  exact ⟨evolved, actual, step, step.current current, success⟩

theorem pop_step {frame : Descriptor} {shared : Shared} {before after : X86.State}
    {destination : Register} {prefixed af : Bool} {reads : List CallReturn.Read}
    (current : Current frame shared before) (slot : Slot frame (before.registers .rsp))
    (decoded : CallReturn.decodeAt before = .ok (.pop64 destination prefixed))
    (actual : CallReturn.execute before (.pop64 destination prefixed) af = .ok ⟨.next after, reads⟩) :
    Step frame shared shared before after af ⟨.next after, reads⟩ := by
  exact ⟨.pop64 destination prefixed, ⟨.next after, reads⟩, decoded, actual, rfl, rfl,
    .unchanged rfl (CallReturn.execute_pop_context actual).2.2.2.2.1,
    (pop_current current slot actual).2.2⟩

theorem private_ret_step {frame : Descriptor} {shared : Shared} {before after : X86.State}
    {af : Bool} {reads : List CallReturn.Read}
    (current : Current frame shared before) (slot : Slot frame (before.registers .rsp))
    (decoded : CallReturn.decodeAt before = .ok (.sequential (.legacy .ret)))
    (actual : CallReturn.execute before (.sequential (.legacy .ret)) af =
      .ok ⟨.returned after, reads⟩) :
    Step frame shared shared before after af ⟨.next after, reads⟩ := by
  obtain ⟨target, _, _, state, _⟩ := CallReturn.execute_ret_success_iff.mp actual
  refine ⟨.sequential (.legacy .ret), ⟨.returned after, reads⟩,
    decoded, actual, rfl, ?_, .unchanged rfl (by rw [state]; rfl),
    (private_ret_current current slot actual).2.2⟩
  simp [CallReturn.atBoundary, private_not_original current slot]

theorem original_ret_step {frame : Descriptor} {shared : Shared} {before : X86.State}
    (current : Current frame shared before) (original : before.registers .rsp = frame.top) (af : Bool)
    (decoded : CallReturn.decodeAt before = .ok (.sequential (.legacy .ret))) :
    Step frame shared shared before
      { before.writeRegister .rsp (before.registers .rsp + 8) with rip := frame.call.returnAddress }
      af ⟨.returned { before.writeRegister .rsp (before.registers .rsp + 8) with
        rip := frame.call.returnAddress }, [⟨.stack, before.registers .rsp, 8⟩]⟩ := by
  obtain ⟨actual, allowed⟩ := original_ret current original af
  refine ⟨.sequential (.legacy .ret), _, decoded, actual, rfl, ?_, .unchanged rfl rfl, ?_⟩
  · simp [CallReturn.atBoundary, original]
  · intro read member
    exact List.mem_singleton.mp member ▸ allowed

/-- Explicit read-only rule for embedded arithmetic/control instructions. Both
CPU full-memory equality and each actual read's current permission are checked. -/
theorem unchanged_step {frame : Descriptor} {shared : Shared} {before after : X86.State}
    {instruction : CallReturn.Instruction} {af : Bool} {raw : CallReturn.Observation}
    (decoded : CallReturn.decodeAt before = .ok instruction)
    (actual : CallReturn.execute before instruction af = .ok raw)
    (cpu : CallReturn.cpu raw.result = some after)
    (noWrite : instruction.writeEffect before = none) (memory : after.memory = before.memory)
    (reads : ∀ read, read ∈ raw.reads → ReadAllowed frame shared read) :
    Step frame shared shared before after af (CallReturn.atBoundary frame.top before raw) :=
  ⟨instruction, raw, decoded, actual, cpu, rfl, .unchanged noWrite memory, reads⟩

/-- A continuing checked CPU trace. The OS world is threaded through each
concrete step, rather than attached as an unrelated endpoint witness. -/
inductive History (frame : Descriptor) : CallReturn.Choices → Shared → X86.State →
    Shared → X86.State → Nat → List CallReturn.Read → Prop where
  | nil {choices shared machine} : History frame choices shared machine shared machine 0 []
  | next {choices shared evolved final before middle after count reads rest}
      (step : Step frame shared evolved before middle (choices 0) ⟨.next middle, reads⟩)
      (tail : History frame (choices.drop 1) evolved middle final after count rest) :
      History frame choices shared before final after (count + 1) (reads ++ rest)

theorem History.machine {frame choices shared before final after count reads}
    (history : History frame choices shared before final after count reads) :
    CallReturn.BlockFrom frame.top choices before after count reads := by
  induction history with
  | nil => exact .nil
  | next step _ ih => exact .next step.machine ih

theorem History.privateHistory {frame choices shared before final after count reads}
    (history : History frame choices shared before final after count reads) :
    PrivateHistory frame shared final := by
  induction history with
  | nil => exact .refl
  | next step _ ih => exact step.history.trans ih

theorem History.current {frame choices shared before final after count reads}
    (history : History frame choices shared before final after count reads)
    (current : Current frame shared before) : Current frame final after := by
  induction history with
  | nil => exact current
  | next step _ ih => exact ih (step.current current)

theorem History.preserves {frame choices shared before final after count reads}
    (history : History frame choices shared before final after count reads) :
    Preservation frame shared final := history.privateHistory.preserves

/-- Returning checked executions include the actual terminal RET, preserving
the same frozen original-slot boundary throughout all intermediate states. -/
inductive Execution (frame : Descriptor) : CallReturn.Choices → Shared → X86.State →
    Shared → CallReturn.Result → Prop where
  | ret {choices shared evolved before after reads}
      (step : Step frame shared evolved before after (choices 0) ⟨.returned after, reads⟩) :
      Execution frame choices shared before evolved ⟨after, 1, reads⟩
  | next {choices shared evolved final before middle result reads}
      (step : Step frame shared evolved before middle (choices 0) ⟨.next middle, reads⟩)
      (tail : Execution frame (choices.drop 1) evolved middle final result) :
      Execution frame choices shared before final (result.prepend 1 reads)

theorem Execution.machine {frame choices shared before final result}
    (execution : Execution frame choices shared before final result) :
    CallReturn.ExecutesFrom frame.top choices before result := by
  induction execution with
  | ret step => exact .ret step.machine
  | next step _ ih => exact .next step.machine ih

theorem Execution.privateHistory {frame choices shared before final result}
    (execution : Execution frame choices shared before final result) :
    PrivateHistory frame shared final := by
  induction execution with
  | ret step => exact step.history
  | next step _ ih => exact step.history.trans ih

theorem Execution.current {frame choices shared before final result}
    (execution : Execution frame choices shared before final result)
    (current : Current frame shared before) : Current frame final result.state := by
  induction execution with
  | ret step => exact step.current current
  | next step _ ih => exact ih (step.current current)

theorem Execution.preserves {frame choices shared before final result}
    (execution : Execution frame choices shared before final result) :
    Preservation frame shared final := execution.privateHistory.preserves

theorem History.then_execution {frame choices shared before evolved middle count reads final result}
    (history : History frame choices shared before evolved middle count reads)
    (tail : Execution frame (choices.drop count) evolved middle final result) :
    Execution frame choices shared before final (result.prepend count reads) := by
  induction history with
  | nil => simpa [Sequential.Result.prepend] using tail
  | @next choices shared nextShared evolved before nextCpu middle count firstReads rest step _ ih =>
    have finish := ih (by simpa [Sequential.ChoiceStream.drop, Nat.add_comm] using tail)
    simpa [Sequential.Result.prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using
      Execution.next step finish

end EDSL.OS.StackFrame.CPU
