/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Run
import EDSL.OS.TSO64.Access
import EDSL.X86.VCGen.Core
import EDSL.Concurrency.ModuloCounter

set_option warningAsError true

/-!
Static atomic-method certificates and rules for the actual TSO64 scheduler.
These rules use Sequential and LockedAdd64 execution; they introduce no second
instruction interpreter. Physical execution retains the existing long-mode,
CET-off, scalar RAM/translation/alias and managed-resource assumptions.
-/

namespace EDSL.X86.VCGen.AtomicMethods
open OS OS.TSO64

deriving instance DecidableEq for OS.TSO64.Decoded

def instructionLength : OS.TSO64.Decoded → Nat
  | .ordinary instruction => instruction.length
  | .locked instruction => instruction.length

/-- A static relative cutpoint. This is certificate data, never a dispatch
table for the scheduler. Both bounds and actual finite-byte decoding are checked. -/
def nodeMatches (bytes : List Byte) (offset : Nat) (instruction : OS.TSO64.Decoded) : Bool :=
  match OS.TSO64.decode (Sequential.codeState bytes offset) with
  | .error _ => false
  | .ok actual => decide (actual = instruction)

def Node (bytes : List Byte) (offset : Nat) (instruction : OS.TSO64.Decoded) : Prop :=
  offset < bytes.length ∧ offset + instructionLength instruction ≤ bytes.length ∧
    nodeMatches bytes offset instruction = true

instance (bytes : List Byte) (offset : Nat) (instruction : OS.TSO64.Decoded) :
    Decidable (Node bytes offset instruction) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem Node.actual {bytes : List Byte} {offset : Nat} {instruction : OS.TSO64.Decoded}
    (node : Node bytes offset instruction) :
    OS.TSO64.decode (Sequential.codeState bytes offset) = .ok instruction := by
  have matched := node.2.2
  cases decoded : OS.TSO64.decode (Sequential.codeState bytes offset) with
  | error fault => simp [nodeMatches, decoded] at matched
  | ok actual =>
    have same : actual = instruction := by simpa only [nodeMatches, decoded, decide_eq_true_eq] using matched
    exact congrArg Except.ok same

private theorem first_fetch {initial : X86.State} {instruction : OS.TSO64.Decoded}
    (decoded : OS.TSO64.decode initial = .ok instruction) :
    ∃ byte, fetchByte initial.memory initial.rip = .ok byte := by
  cases first : fetchByte initial.memory initial.rip with
  | error fault => simp [OS.TSO64.decode, first, Except.mapError] at decoded
  | ok byte => exact ⟨byte, rfl⟩

/-- Transport the existing two production decoders together. Locked fetch
no-wrap is an explicit gate; ordinary transport needs only successful fetches. -/
theorem decode_transport {source destination : X86.State} {instruction : OS.TSO64.Decoded}
    (transport : Sequential.SuccessfulFetchTransport source destination)
    (lockedBound : ∀ locked, instruction = .locked locked → destination.rip.toNat + 5 ≤ 2^64)
    (decoded : OS.TSO64.decode source = .ok instruction) :
    OS.TSO64.decode destination = .ok instruction := by
  obtain ⟨byte, first⟩ := first_fetch decoded
  have next := transport 0 (by decide) byte (by simpa only [BitVec.add_zero] using first)
  simp only [BitVec.add_zero] at next
  by_cases lock : byte = 0xf0#8
  · subst byte
    have actual : ∃ locked, instruction = .locked locked ∧
        LockedAdd64.decodeAt source = .ok locked := by
      cases output : LockedAdd64.decodeAt source with
      | error fault => simp [OS.TSO64.decode, first, output, Except.mapError] at decoded
      | ok locked =>
        simp [OS.TSO64.decode, first, output, Except.mapError] at decoded
        exact ⟨locked, decoded.symm, rfl⟩
    obtain ⟨locked, rfl, actual⟩ := actual
    have code := LockedAdd64.decodeAt_code actual
    have destinationCode : CodeAt destination.memory destination.rip locked.bytes := by
      refine ⟨lockedBound locked rfl, ?_⟩
      intro offset byte present
      have bound := (List.getElem_of_getElem? present).1
      exact transport offset (by change offset < 5 at bound; omega) byte (code.2 offset byte present)
    simp [OS.TSO64.decode, next, LockedAdd64.decodeAt_of_code locked destinationCode,
      Except.mapError]
  · have actual : ∃ ordinary, instruction = .ordinary ordinary ∧
        Sequential.decodeAt source = .ok ordinary := by
      cases output : Sequential.decodeAt source with
      | error fault => simp [OS.TSO64.decode, first, lock, output, Except.mapError] at decoded
      | ok ordinary =>
        simp [OS.TSO64.decode, first, lock, output, Except.mapError] at decoded
        exact ⟨ordinary, decoded.symm, rfl⟩
    obtain ⟨ordinary, rfl, actual⟩ := actual
    simp [OS.TSO64.decode, next, lock, Sequential.decodeAt_transport transport actual,
      Except.mapError]

private theorem offset_nat {bytes : List Byte} {memory : Memory} {base : Word}
    (code : CodeAt memory base bytes) {offset : Nat} (inside : offset < bytes.length) :
    (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
  have small : offset < 2^64 := by have := code.1; omega
  have sum : base.toNat + offset < 2^64 := by have := code.1; omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt sum]

/-- Turn static whole-window decoding into actual current decoding. The
five-byte gate is needed only at a locked node, including an end-of-space case. -/
theorem Node.decoded {bytes : List Byte} {offset : Nat} {instruction : OS.TSO64.Decoded}
    (node : Node bytes offset instruction) (size : bytes.length ≤ 64)
    {base : Word} {memory : Memory} (code : CodeAt memory base bytes)
    (state : X86.State) (ram : state.memory = memory)
    (pc : state.rip = base + BitVec.ofNat 64 offset) :
    OS.TSO64.decode state = .ok instruction := by
  apply decode_transport (Sequential.code_fetch_transport code size offset node.1 state ram pc) ?_ node.actual
  intro locked same
  rw [pc, offset_nat code node.1]
  have := code.1
  have bound := node.2.1
  rw [same] at bound
  change offset + 5 ≤ bytes.length at bound
  omega

/-- Guarded code fetch agrees on the entire admitted window, using the current
original code loan. This supplies bounds from present code/resources. -/
theorem guarded_code {state : OS.TSO64.State} {worker : Worker} {base : Word} {bytes : List Byte}
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region) :
    CodeAt (fetchCPU state worker).memory base bytes := by
  refine ⟨code.1, ?_⟩
  intro offset byte present
  have inside := (List.getElem_of_getElem? present).1
  have natural := offset_nat code inside
  have contained : worker.resources.code.loan.region.Contains (base + BitVec.ofNat 64 offset) := by
    have lower := fits.1
    have upper := fits.2
    change worker.resources.code.loan.region.base.toNat ≤ _ ∧
      _ < worker.resources.code.loan.region.base.toNat + worker.resources.code.loan.region.length
    rw [natural]
    change worker.resources.code.loan.region.base.toNat ≤ base.toNat at lower
    change base.toNat + bytes.length ≤
      worker.resources.code.loan.region.base.toNat + worker.resources.code.loan.region.length at upper
    constructor <;> omega
  have fetched := code.2 offset byte present
  unfold fetchByte at fetched ⊢
  simp only [fetchCPU, cpu, decide_eq_true contained, Bool.and_true]
  exact fetched

/-- Empty own FIFO identifies the local projection with the current world.
Peer memory updates remain visible; there is no invocation-memory snapshot. -/
theorem localCPU_empty {state : OS.TSO64.State} {worker : Worker} (empty : worker.pending = []) :
    localCPU state worker = sharedCPU state worker := by
  simp [localCPU, sharedCPU, empty, payload, StoreBuffer.Mixed.view]

/-- Successful peer actions retain the literal worker and its original
resources; current shared bytes may change. -/
theorem peer_frame {state : OS.TSO64.State} {action : Action} {result : OS.TSO64.State × Observation}
    {tid : Nat} {worker : Worker} (live : state.workers[tid]? = some worker)
    (different : tid ≠ (match action with | .issue thread _ | .drain thread => thread))
    (success : OS.TSO64.step state action = .ok result) :
    result.1.workers[tid]? = some worker ∧ Stable state.world result.1.world := by
  cases action <;> exact ⟨(step_peer success different).trans live, step_stable success⟩

theorem atomicFor_stable {before after : World} (stable : Stable before after)
    (resources : Resources) (address : Word) :
    atomicFor after resources address = atomicFor before resources address := by
  simp only [atomicFor, stable.authorize]

/-- The original loan read survives every successful action, including peer
RMWs and FIFO publication. This is a frame on protected bytes, not shared data. -/
theorem step_loan_read {before : OS.TSO64.State} {action : Action}
    {result : OS.TSO64.State × Observation} (valid : WellFormed before)
    (success : OS.TSO64.step before action = .ok result)
    {borrower identifier : Nat} {address value : Word}
    (read : Borrowing.loadWord64 before.world.legacy.shared borrower identifier address = .ok value) :
    Borrowing.loadWord64 result.1.world.legacy.shared borrower identifier address = .ok value := by
  obtain ⟨loan, authority, fits, observed⟩ := Borrowing.loadWord64_ok _ _ _ _ _ read
  obtain ⟨live, owns⟩ := Borrowing.authorize_ok _ _ _ _ authority
  have current := step_stable success
  have finalAuthority : Borrowing.authorize result.1.world.legacy.shared borrower identifier = .ok loan := by
    simp [Borrowing.authorize, current.loans, live, owns]
  apply Borrowing.loadWord64_success _ _ _ _ _ loan finalAuthority fits
  apply (loadQWord_congr _ _ _ ?_).trans observed
  intro offset bound
  have loanValid := (valid.1.legacy.shared.2 identifier loan live).2
  obtain ⟨_, _, _, _, _, regionValid, _⟩ := loanValid
  exact (AddressSpace.toMemory_agrees_at _ _ _
    (step_loan_contents valid success live _
      (Borrowing.qword_inside loan regionValid address fits offset bound))).1

private theorem decode_ordinary {state : X86.State} {instruction : Sequential.Instruction}
    (decoded : OS.TSO64.decode state = .ok (.ordinary instruction)) :
    Sequential.decodeAt state = .ok instruction := by
  obtain ⟨byte, first⟩ := first_fetch decoded
  by_cases lock : byte = 0xf0#8
  · subst byte
    cases result : LockedAdd64.decodeAt state <;>
      simp [OS.TSO64.decode, first, result, Except.mapError] at decoded
  · cases result : Sequential.decodeAt state with
    | error fault => simp [OS.TSO64.decode, first, lock, result, Except.mapError] at decoded
    | ok actual =>
      simp [OS.TSO64.decode, first, lock, result, Except.mapError] at decoded
      cases decoded
      rfl

private theorem decode_locked {state : X86.State} {instruction : LockedAdd64.Instruction}
    (decoded : OS.TSO64.decode state = .ok (.locked instruction)) :
    LockedAdd64.decodeAt state = .ok instruction := by
  obtain ⟨byte, first⟩ := first_fetch decoded
  by_cases lock : byte = 0xf0#8
  · subst byte
    cases result : LockedAdd64.decodeAt state with
    | error fault => simp [OS.TSO64.decode, first, result, Except.mapError] at decoded
    | ok actual =>
      simp [OS.TSO64.decode, first, result, Except.mapError] at decoded
      cases decoded
      rfl
  · cases result : Sequential.decodeAt state <;>
      simp [OS.TSO64.decode, first, lock, result, Except.mapError] at decoded

theorem Node.codeFits {bytes : List Byte} {offset : Nat} {instruction : OS.TSO64.Decoded}
    (node : Node bytes offset instruction) {state : OS.TSO64.State} {worker : Worker} {base : Word}
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region)
    (pc : worker.context.rip = base + BitVec.ofNat 64 offset) :
    codeFits worker (instructionLength instruction) := by
  have natural := offset_nat code node.1
  have lower := fits.1
  have upper := fits.2
  have span := node.2.1
  change worker.resources.code.loan.region.base.toNat ≤ base.toNat at lower
  change base.toNat + bytes.length ≤
    worker.resources.code.loan.region.base.toNat + worker.resources.code.loan.region.length at upper
  change worker.resources.code.loan.region.base.toNat ≤ worker.context.rip.toNat ∧
    worker.context.rip.toNat + instructionLength instruction ≤
      worker.resources.code.loan.region.base.toNat + worker.resources.code.loan.region.length
  rw [pc, natural]
  constructor <;> omega

/-- Ordinary VC rule: clients discharge the production executor and its current
read gates. The rule derives the scheduler step, rather than assuming one. -/
theorem issue_ordinary {bytes : List Byte} {offset : Nat} {instruction : Sequential.Instruction}
    (node : Node bytes offset (.ordinary instruction)) (size : bytes.length ≤ 64)
    {state : OS.TSO64.State} {worker : Worker} {tid : Nat} {base : Word}
    (valid : WellFormed state) (live : state.workers[tid]? = some worker)
    (running : worker.phase = .running) (empty : worker.pending = [])
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region)
    (pc : worker.context.rip = base + BitVec.ofNat 64 offset)
    (admitted : supported instruction = true)
    (noStore : storeIntent instruction (localCPU state worker) = none)
    (reads : ∃ units, (instruction.operandReads (localCPU state worker)).mapM (checkRead state worker) = .ok units)
    {observation : Sequential.Observation} {af : Bool}
    (executed : Sequential.execute (localCPU state worker) instruction af = .ok observation) :
    issue state tid af = finishOrdinary state tid worker [] observation := by
  have resource := (valid.2 worker (List.mem_of_getElem? live)).1
  have fetched := node.decoded size (guarded_code code fits) (fetchCPU state worker) rfl pc
  have ordinary := decode_ordinary (node.decoded size code (sharedCPU state worker) rfl pc)
  have localDecoded : Sequential.decodeAt (localCPU state worker) = .ok instruction := by
    rw [localCPU_empty empty]
    exact ordinary
  obtain ⟨units, checked⟩ := reads
  have bounds : codeFits worker instruction.length := node.codeFits code fits pc
  simp [issue, live, running, resource.1, resource.2.1, fetched, OS.TSO64.ordinary,
    admitted, bounds, localDecoded, checked, prepareQueue, noStore, empty, executed, Except.mapError]

/-- LOCK rule derives enabledness from CURRENT authority and the current
world invariant. Source/base aliases and source RSP retain their ISA meaning. -/
theorem issue_locked {bytes : List Byte} {offset : Nat} {instruction : LockedAdd64.Instruction}
    (node : Node bytes offset (.locked instruction)) (size : bytes.length ≤ 64)
    {state : OS.TSO64.State} {worker : Worker} {tid : Nat} {base : Word}
    (valid : WellFormed state) (live : state.workers[tid]? = some worker)
    (running : worker.phase = .running) (empty : worker.pending = [])
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region)
    (pc : worker.context.rip = base + BitVec.ofNat 64 offset)
    {identifier : Atomics64.HandleId64} {handle : Atomics64.Handle} {cell : Atomics64.Cell}
    (selected : atomicFor state.world worker.resources
      (worker.context.registers instruction.base) = some (identifier, handle, cell)) (af : Bool) :
    ∃ output machine,
      issue state tid af = .ok (install state tid output.1
        { worker with context := .ofCPU machine.state }, .rmw tid output.2) ∧
      Atomics64.FetchAddMachineEffect state.world worker.resources.actor identifier
        (sharedCPU state worker) instruction output machine := by
  have resource := (valid.2 worker (List.mem_of_getElem? live)).1
  have fetched := node.decoded size (guarded_code code fits) (fetchCPU state worker) rfl pc
  have locked := decode_locked (node.decoded size code (sharedCPU state worker) rfl pc)
  obtain ⟨_, authority, address⟩ := atomicFor_sound selected
  obtain ⟨output, changed, executed⟩ := Atomics64.fetchAdd_step_enabled _ _ _ _ _ _ _
    valid.1 authority rfl address.symm locked
  have bounds : codeFits worker instruction.length := node.codeFits code fits pc
  change atomicFor state.world worker.resources ((sharedCPU state worker).registers instruction.base) =
    some (identifier, handle, cell) at selected
  refine ⟨output, _, ?_, Atomics64.fetchAdd_step_effect _ _ _ _ _ _ _ _
    changed authority rfl address.symm locked⟩
  simp [issue, live, running, resource.1, resource.2.1, fetched, OS.TSO64.locked,
    bounds, empty, locked, selected, changed, executed, Except.mapError]

/-- Padding admitted by the production sequential target profile. -/
inductive Padding where
  | endbr64
  | nop (encoding : Sequential.NopEncoding)
  deriving DecidableEq, Repr

def Padding.instruction : Padding → Sequential.Instruction
  | .endbr64 => .endbr64IbtDisabled
  | .nop encoding => .nop encoding

/-- Complete static family: arbitrary padding, full-width register copy,
exact encoded full-width LOCK XADD, and RET, with no ignored suffix. -/
inductive Shape (bytes : List Byte) (input : Register) (locked : LockedAdd64.Instruction) :
    Nat → List Padding → Prop where
  | body {offset}
      (copy : Node bytes offset (.ordinary (.movReg64 locked.source input)))
      (rmw : Node bytes (offset + 3) (.locked locked))
      (ret : Node bytes (offset + 8) (.ordinary (.legacy .ret)))
      (extent : offset + 9 = bytes.length) : Shape bytes input locked offset []
  | pad {offset padding rest}
      (node : Node bytes offset (.ordinary padding.instruction))
      (tail : Shape bytes input locked (offset + padding.instruction.length) rest) :
      Shape bytes input locked offset (padding :: rest)

def checkFrom (bytes : List Byte) (input : Register) (locked : LockedAdd64.Instruction) :
    Nat → List Padding → Bool
  | offset, [] => decide (Node bytes offset (.ordinary (.movReg64 locked.source input))) &&
      decide (Node bytes (offset + 3) (.locked locked)) &&
      decide (Node bytes (offset + 8) (.ordinary (.legacy .ret))) &&
      decide (offset + 9 = bytes.length)
  | offset, padding :: rest => decide (Node bytes offset (.ordinary padding.instruction)) &&
      checkFrom bytes input locked (offset + padding.instruction.length) rest

/-- A finite checker of code shape only. Functional claims additionally use
the universal symbolic rules below and explicit current-resource admission. -/
def check (bytes : List Byte) (input : Register) (locked : LockedAdd64.Instruction)
    (padding : List Padding) : Bool :=
  decide (bytes.length ≤ 64) && checkFrom bytes input locked 0 padding

theorem checkFrom_sound {bytes : List Byte} {input : Register} {locked : LockedAdd64.Instruction}
    {offset : Nat} {padding : List Padding}
    (accepted : checkFrom bytes input locked offset padding = true) :
    Shape bytes input locked offset padding := by
  induction padding generalizing offset with
  | nil =>
    have parts := accepted
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at parts
    exact .body parts.1.1.1 parts.1.1.2 parts.1.2 parts.2
  | cons padding rest ih =>
    have parts := accepted
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at parts
    exact .pad parts.1 (ih parts.2)

theorem check_sound {bytes : List Byte} {input : Register} {locked : LockedAdd64.Instruction}
    {padding : List Padding} (accepted : check bytes input locked padding = true) :
    bytes.length ≤ 64 ∧ Shape bytes input locked 0 padding := by
  have parts := Bool.and_eq_true_iff.mp accepted
  exact ⟨of_decide_eq_true parts.1, checkFrom_sound parts.2⟩

/-- A symbolic register assertion, expressed through the existing machine's
register-write operation. It is not an instruction executor. -/
def written (registers : Register → Word) (destination : Register) (value : Word) : Register → Word :=
  (X86.State.writeRegister ⟨registers, 0, 0, Sequential.codeMemory []⟩ destination value).registers

@[simp] theorem written_same (registers : Register → Word) (destination : Register) (value : Word) :
    written registers destination value destination = value := by
  simp [written, X86.State.writeRegister]

@[simp] theorem written_other (registers : Register → Word) (destination : Register) (value : Word)
    (register : Register) (other : register ≠ destination) :
    written registers destination value register = registers register := by
  simp [written, X86.State.writeRegister, other]

/-- Fixed independent invocation data. No invocation memory value is retained.
The selected persistent target is the base AFTER the input copy, so base/source
aliases obey the existing ISA instead of receiving an incorrect entry-base rule.

Total returning methods exclude a source RSP: a general old-word RSP write
cannot promise RET through the original slot. The primitive LOCK rule above
continues to support RSP and aliases. ABI users specialize source to RAX. -/
structure Method where
  bytes : List Byte
  input : Register
  locked : LockedAdd64.Instruction
  base : Word
  entry : Register → Word
  resources : Resources
  identifier : Atomics64.HandleId64
  handle : Atomics64.Handle
  cell : Atomics64.Cell
  returnAddress : Word
  size : bytes.length ≤ 64
  sourceNotRsp : locked.source ≠ .rsp
  originalRsp : entry .rsp = resources.callerAddress
  returnCanonical : canonical returnAddress = true
  stackNoWrap : (entry .rsp).toNat + 8 < 2^64

def Method.copied (method : Method) : Register → Word :=
  written method.entry method.locked.source (method.entry method.input)

def Method.responded (method : Method) (event : Atomics64.FetchAddEvent) : Register → Word :=
  written method.entry method.locked.source event.arithmetic.event.before

/-- Conditions on the CURRENT world, preserved by actual successful actions.
Selection is an executable present-authority gate, not a desired post-state. -/
structure Current (method : Method) (state : OS.TSO64.State) : Prop where
  valid : WellFormed state
  code : CodeAt (published state.world) method.base method.bytes
  fits : Borrowing.Subregion ⟨method.base, method.bytes.length⟩ method.resources.code.loan.region
  caller : Borrowing.loadWord64 state.world.legacy.shared method.resources.actor
    method.resources.caller.identifier method.resources.callerAddress = .ok method.returnAddress
  selected : atomicFor state.world method.resources (method.copied method.locked.base) =
    some (method.identifier, method.handle, method.cell)

theorem Current.step {method : Method} {before : OS.TSO64.State} {action : Action}
    {result : OS.TSO64.State × Observation} (current : Current method before)
    (success : OS.TSO64.step before action = .ok result) : Current method result.1 := by
  exact ⟨step_wellFormed current.valid success, step_code success current.code, current.fits,
    step_loan_read current.valid success current.caller,
    (atomicFor_stable (step_stable success) _ _).trans current.selected⟩

/-- Proof-side cutpoints. The actual scheduler still fetches and decodes at
its current RIP. An RMW point retains its real typed event through RET. -/
inductive Point where
  | preamble (offset : Nat) (padding : List Padding)
  | rmw (offset : Nat)
  | ret (offset : Nat) (event : Atomics64.FetchAddEvent)
  | done (event : Atomics64.FetchAddEvent)

def Point.remaining : Point → Nat
  | .preamble _ padding => padding.length + 3
  | .rmw _ => 2
  | .ret _ _ => 1
  | .done _ => 0

def Point.events : Point → List Atomics64.FetchAddEvent
  | .preamble _ _ | .rmw _ => []
  | .ret _ event | .done event => [event]

structure EventCorrect (method : Method) (event : Atomics64.FetchAddEvent) : Prop where
  actor : event.actor = method.resources.actor
  handle : event.handle = method.identifier
  cell : event.cell = method.handle.cell
  address : event.arithmetic.event.address = method.cell.address
  input : event.arithmetic.delta = method.entry method.input
  arithmetic : Concurrency.ModuloCounter.Step event.arithmetic.event.before
    (method.entry method.input) event.arithmetic.event.before event.arithmetic.event.after

/-- Exact RF/stack assertions at each relative cutpoint. The returned value
is the old word from an actual event, independently of intervening target writes. -/
def At (method : Method) (point : Point) (worker : Worker) : Prop :=
  worker.resources = method.resources ∧ worker.pending = [] ∧
    match point with
    | .preamble offset padding => worker.phase = .running ∧
        worker.context.rip = method.base + BitVec.ofNat 64 offset ∧
        worker.context.registers = method.entry ∧
        Shape method.bytes method.input method.locked offset padding
    | .rmw offset => worker.phase = .running ∧
        worker.context.rip = method.base + BitVec.ofNat 64 offset ∧
        worker.context.registers = method.copied ∧
        Node method.bytes offset (.locked method.locked) ∧
        Node method.bytes (offset + 5) (.ordinary (.legacy .ret))
    | .ret offset event => worker.phase = .running ∧
        worker.context.rip = method.base + BitVec.ofNat 64 offset ∧
        worker.context.registers = method.responded event ∧
        Node method.bytes offset (.ordinary (.legacy .ret)) ∧ EventCorrect method event
    | .done event => worker.phase = .returned ∧
        worker.context.rip = method.returnAddress ∧
        worker.context.registers = written (method.responded event) .rsp (method.entry .rsp + 8) ∧
        EventCorrect method event

def ownEvent (tid : Nat) : Observation → Option Atomics64.FetchAddEvent
  | .rmw thread event => if thread = tid then some event else none
  | _ => none

private theorem padding_execute (state : X86.State) (padding : Padding) (af : Bool) :
    Sequential.execute state padding.instruction af = .ok
      ⟨.next { state with rip := state.rip + BitVec.ofNat 64 padding.instruction.length }, []⟩ := by
  cases padding <;> rfl

private theorem install_self {state : OS.TSO64.State} {tid : Nat} {worker : Worker}
    (live : state.workers[tid]? = some worker) (world : World) (replacement : Worker) :
    (install state tid world replacement).workers[tid]? = some replacement :=
  List.getElem?_set_self (List.getElem_of_getElem? live).1

private theorem flag_lookup {state : OS.TSO64.State} {tid : Nat} {worker : Worker}
    (live : state.workers[tid]? = some worker) {value : Word}
    (preserved : value = worker.context.flags &&& ~~~arithmeticFlagMask) :
    ∀ prior, state.workers[tid]? = some prior → value = prior.context.flags &&& ~~~arithmeticFlagMask := by
  intro prior priorLive
  have same : prior = worker := Option.some.inj (priorLive.symm.trans live)
  subst prior
  exact preserved

/-- One retiring own step, constructed from present conditions. This record is
proof evidence; the scheduler's only transition function remains TSO64.issue. -/
structure Advance (method : Method) (tid : Nat) (state : OS.TSO64.State) (point : Point)
    (af : Bool) where
  result : OS.TSO64.State × Observation
  next : Point
  worker : Worker
  actual : issue state tid af = .ok result
  live : result.1.workers[tid]? = some worker
  located : At method next worker
  progress : next.remaining + 1 = point.remaining
  events : point.events ++ (ownEvent tid result.2).toList = next.events
  retired : result.2.retired = 1
  flags : ∀ prior, state.workers[tid]? = some prior →
    worker.context.flags &&& ~~~arithmeticFlagMask = prior.context.flags &&& ~~~arithmeticFlagMask

/-- Universal symbolic straight-line rule. Padding and MOV use the existing
executor; LOCK uses its real joint typed effect; RET uses the original CURRENT
caller read and canonical target. No successful future step is an assumption. -/
theorem advance {method : Method} {tid : Nat} {state : OS.TSO64.State} {point : Point}
    {worker : Worker} (current : Current method state) (live : state.workers[tid]? = some worker)
    (located : At method point worker) (unfinished : point.remaining ≠ 0) (af : Bool) :
    Nonempty (Advance method tid state point af) := by
  rcases located with ⟨resources, empty, location⟩
  have fits : Borrowing.Subregion ⟨method.base, method.bytes.length⟩ worker.resources.code.loan.region := by
    rw [resources]
    exact current.fits
  cases point with
  | preamble offset padding =>
    rcases location with ⟨running, pc, registers, shape⟩
    cases shape with
    | @pad offset padding rest node tail =>
      let middle : X86.State := { localCPU state worker with
        rip := worker.context.rip + BitVec.ofNat 64 padding.instruction.length }
      have executed : Sequential.execute (localCPU state worker) padding.instruction af =
          .ok ⟨.next middle, []⟩ := padding_execute _ _ _
      have admitted : supported padding.instruction = true := by cases padding <;> rfl
      have noStore : storeIntent padding.instruction (localCPU state worker) = none := by cases padding <;> rfl
      have reads : ∃ units, (padding.instruction.operandReads (localCPU state worker)).mapM
          (checkRead state worker) = .ok units := by
        refine ⟨[], ?_⟩
        cases padding <;> rfl
      let after : Worker := { worker with context := .ofCPU middle, pending := [] }
      have actual : issue state tid af = .ok (install state tid state.world after, .ordinary tid) := by
        rw [issue_ordinary node method.size current.valid live running empty current.code fits pc
          admitted noStore reads executed]
        rfl
      refine ⟨⟨_, .preamble (offset + padding.instruction.length) rest, after, actual,
        install_self live _ _, ?_, ?_, rfl, rfl, flag_lookup live rfl⟩⟩
      · refine ⟨resources, rfl, running, ?_, registers, tail⟩
        change worker.context.rip + BitVec.ofNat 64 padding.instruction.length = _
        rw [pc, BitVec.ofNat_add, BitVec.add_assoc]
      · simp only [Point.remaining, List.length_cons]
    | @body offset copy rmw ret extent =>
      let middle : X86.State := { (localCPU state worker).writeRegister method.locked.source
        ((localCPU state worker).registers method.input) with rip := worker.context.rip + 3 }
      have executed : Sequential.execute (localCPU state worker)
          (.movReg64 method.locked.source method.input) af = .ok ⟨.next middle, []⟩ := rfl
      let after : Worker := { worker with context := .ofCPU middle, pending := [] }
      have actual : issue state tid af = .ok (install state tid state.world after, .ordinary tid) := by
        rw [issue_ordinary copy method.size current.valid live running empty current.code fits pc
          rfl rfl ⟨[], rfl⟩ executed]
        rfl
      refine ⟨⟨_, .rmw (offset + 3), after, actual, install_self live _ _, ?_, rfl, rfl, rfl,
        flag_lookup live rfl⟩⟩
      refine ⟨resources, rfl, running, ?_, ?_, rmw, ?_⟩
      · change worker.context.rip + 3 = _
        rw [pc, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      · change ((localCPU state worker).writeRegister method.locked.source
          ((localCPU state worker).registers method.input)).registers = method.copied
        simp only [localCPU, cpu, registers, Method.copied, written, X86.State.writeRegister]
      · simpa only [Nat.add_assoc] using ret
  | rmw offset =>
    rcases location with ⟨running, pc, registers, node, ret⟩
    have selected : atomicFor state.world worker.resources (worker.context.registers method.locked.base) =
        some (method.identifier, method.handle, method.cell) := by
      rw [resources, registers]
      exact current.selected
    obtain ⟨output, machine, actual, effect⟩ := issue_locked node method.size current.valid live running
      empty current.code fits pc selected af
    let after : Worker := { worker with context := .ofCPU machine.state }
    have authority := (atomicFor_sound selected).2.1
    have identities := Atomics64.fetchAdd_identity _ _ _ _ _ _ _ effect.checked authority
    have sound := Atomics64.fetchAdd_sound _ _ _ _ _ effect.checked
    have delta : output.2.arithmetic.delta = method.entry method.input := by
      rw [effect.delta]
      change worker.context.registers method.locked.source = _
      rw [registers]
      exact written_same _ _ _
    have correct : EventCorrect method output.2 := by
      refine ⟨?_, sound.2.2.2.2, identities.1, identities.2, delta, ?_⟩
      · simpa only [resources] using sound.2.2.2.1
      · exact ⟨rfl, by rw [← delta]; exact effect.cpu.modular⟩
    refine ⟨⟨_, .ret (offset + 5) output.2, after, actual, install_self live _ _, ?_, rfl, ?_, rfl,
      flag_lookup live effect.cpu.nonarithmetic_flags⟩⟩
    · refine ⟨resources, empty, running, ?_, ?_, ret, correct⟩
      · change machine.state.rip = _
        rw [effect.rip]
        change worker.context.rip + 5 = _
        rw [pc, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      · change machine.state.registers = _
        rw [effect.cpu.registers]
        funext register
        simp only [X86.State.writeRegister, sharedCPU, cpu, registers, Method.copied,
          Method.responded, written]
        split <;> rfl
    · simp [Point.events, ownEvent]
  | ret offset event =>
    rcases location with ⟨running, pc, registers, node, correct⟩
    have stack : worker.context.registers .rsp = method.resources.callerAddress := by
      rw [registers, Method.responded, written_other _ _ _ _ (Ne.symm method.sourceNotRsp)]
      exact method.originalRsp
    have word := (Borrowing.loadWord64_ok _ _ _ _ _ current.caller).choose_spec.2.2
    have originalRead := readWord_of_loadQWord _ _ _ word
    have localRead : readWord (localCPU state worker).memory (worker.context.registers .rsp) =
        .ok method.returnAddress := by
      rw [localCPU_empty empty, stack]
      exact originalRead
    have stackGate : checkRead state worker ⟨.stack, worker.context.registers .rsp, 8⟩ = .ok () := by
      simp [checkRead, stack, resources, current.caller, Except.mapError]
    let middle : X86.State := { (localCPU state worker).writeRegister .rsp
      (worker.context.registers .rsp + 8) with rip := method.returnAddress }
    have executed : Sequential.execute (localCPU state worker) (.legacy .ret) af =
        .ok ⟨.returned middle, [⟨.stack, worker.context.registers .rsp, 8⟩]⟩ := by
      change readWord (localCPU state worker).memory ((localCPU state worker).registers .rsp) =
        .ok method.returnAddress at localRead
      simp only [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
        executeRet, localRead, method.returnCanonical, ↓reduceIte,
        ok_bind, pure_ok]
      rfl
    have noStore : storeIntent (.legacy .ret) (localCPU state worker) = none := rfl
    have reads : ∃ units, ((Sequential.Instruction.legacy .ret).operandReads (localCPU state worker)).mapM
        (checkRead state worker) = .ok units := by
      change checkRead state worker ⟨.stack, (localCPU state worker).registers .rsp, 8⟩ = .ok () at stackGate
      exact ⟨[()], by simp only [Sequential.Instruction.operandReads, List.mapM_cons,
        stackGate, ok_bind, List.mapM_nil, pure_ok]⟩
    let after : Worker := { worker with context := .ofCPU middle, phase := .returned, pending := [] }
    have actual : issue state tid af = .ok (install state tid state.world after, .returned tid) := by
      rw [issue_ordinary node method.size current.valid live running empty current.code fits pc
        rfl noStore reads executed]
      rfl
    refine ⟨⟨_, .done event, after, actual, install_self live _ _, ?_, rfl, ?_, rfl,
      flag_lookup live rfl⟩⟩
    · refine ⟨resources, rfl, rfl, rfl, ?_, correct⟩
      have rsp : worker.context.registers .rsp = method.entry .rsp := stack.trans method.originalRsp.symm
      change ((localCPU state worker).writeRegister .rsp (worker.context.registers .rsp + 8)).registers = _
      simp only [localCPU, cpu, registers, rsp, written, X86.State.writeRegister]
    · simp [Point.events, ownEvent]
  | done event => exact False.elim (unfinished rfl)

def ownIssue (tid : Nat) : Action → Nat
  | .issue thread _ => if thread = tid then 1 else 0
  | .drain _ => 0

def ownIssues (tid : Nat) : List Action → Nat
  | [] => 0
  | action :: rest => ownIssue tid action + ownIssues tid rest

private theorem peer_event {before : OS.TSO64.State} {action : Action}
    {result : OS.TSO64.State × Observation} {tid : Nat}
    (different : tid ≠ (match action with | .issue thread _ | .drain thread => thread))
    (success : OS.TSO64.step before action = .ok result) : ownEvent tid result.2 = none := by
  cases step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue step finish => cases finish <;> rfl
  | blocked => rfl
  | rmw => simp only [ownEvent, ite_eq_right (Ne.symm different)]
  | drained => rfl

theorem At.zero_returned {method : Method} {point : Point} {worker : Worker}
    (located : At method point worker) (zero : point.remaining = 0) : worker.phase = .returned := by
  cases point with
  | preamble offset padding => simp [Point.remaining] at zero
  | rmw offset => cases zero
  | ret offset event => cases zero
  | done event => exact located.2.2.1

/-- Every successful action preserves the symbolic method invariant. Own
drain/blocked cases are excluded by the derived empty FIFO. Peer actions use
the literal-worker frame and may change the current shared target. -/
theorem step_preserves {method : Method} {tid : Nat} {state : OS.TSO64.State} {point : Point}
    {worker : Worker} (current : Current method state) (live : state.workers[tid]? = some worker)
    (located : At method point worker) {action : Action} {result : OS.TSO64.State × Observation}
    (success : OS.TSO64.step state action = .ok result) :
    ∃ next after, result.1.workers[tid]? = some after ∧ At method next after ∧
      next.remaining + ownIssue tid action = point.remaining ∧
      point.events ++ (ownEvent tid result.2).toList = next.events ∧
      after.context.flags &&& ~~~arithmeticFlagMask = worker.context.flags &&& ~~~arithmeticFlagMask := by
  cases action with
  | issue thread af =>
    by_cases same : thread = tid
    · subst thread
      have unfinished : point.remaining ≠ 0 := by
        intro zero
        have returned := located.zero_returned zero
        simp [OS.TSO64.step, issue, live, returned] at success
      obtain ⟨advanced⟩ := advance current live located unfinished af
      have equal : advanced.result = result := Except.ok.inj (advanced.actual.symm.trans success)
      subst result
      exact ⟨advanced.next, advanced.worker, advanced.live, advanced.located,
        by simpa [ownIssue] using advanced.progress, advanced.events, advanced.flags worker live⟩
    · have different : tid ≠ thread := Ne.symm same
      have peer := (peer_frame (action := .issue thread af) live different success).1
      exact ⟨point, worker, peer, located, by simp [ownIssue, same],
        by rw [peer_event (action := .issue thread af) different success]; simp, rfl⟩
  | drain thread =>
    by_cases same : thread = tid
    · subst thread
      simp [OS.TSO64.step, drain, live, located.2.1] at success
    · have different : tid ≠ thread := Ne.symm same
      exact ⟨point, worker, (peer_frame (action := .drain thread) live different success).1,
        located, by simp [ownIssue],
        by rw [peer_event (action := .drain thread) different success]; simp, rfl⟩

private theorem filterMap_cons (f : α → Option β) (head : α) (tail : List α) :
    (head :: tail).filterMap f = (f head).toList ++ tail.filterMap f := by
  cases present : f head <;> simp [present]

/-- All finite actual interleaving prefixes, without labels, protocol gates,
fairness, or a fixed initial target value. The event list records exact own
RMW occurrences, even when input or old word is zero. -/
theorem schedule_preserves {method : Method} {tid : Nat} {state : OS.TSO64.State} {point : Point}
    {worker : Worker} (current : Current method state) (live : state.workers[tid]? = some worker)
    (located : At method point worker) {actions : List Action}
    {result : OS.TSO64.State × List Observation} (success : schedule state actions = .ok result) :
    Current method result.1 ∧ ∃ next after,
      result.1.workers[tid]? = some after ∧ At method next after ∧
      next.remaining + ownIssues tid actions = point.remaining ∧
      point.events ++ result.2.filterMap (ownEvent tid) = next.events ∧
      after.context.flags &&& ~~~arithmeticFlagMask = worker.context.flags &&& ~~~arithmeticFlagMask := by
  induction actions generalizing state point worker result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    exact ⟨current, point, worker, live, located, rfl, by simp, rfl⟩
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok success
    obtain ⟨middle, middleWorker, middleLive, middleAt, progress, events, flags⟩ :=
      step_preserves current live located first
    obtain ⟨finalCurrent, final, after, finalLive, finalAt, tailProgress, tailEvents, tailFlags⟩ :=
      ih (current.step first) middleLive middleAt following
    rw [same]
    refine ⟨finalCurrent, final, after, finalLive, finalAt, ?_, ?_, tailFlags.trans flags⟩
    · simp only [ownIssues]
      omega
    · rw [filterMap_cons, ← List.append_assoc, events]
      exact tailEvents

/-- Current enabledness at every unfinished admitted cutpoint. A hostile
scheduler can delay this enabled issue indefinitely; no fairness is inferred. -/
theorem enabled {method : Method} {tid : Nat} {state : OS.TSO64.State} {point : Point}
    {worker : Worker} (current : Current method state) (live : state.workers[tid]? = some worker)
    (located : At method point worker) (unfinished : point.remaining ≠ 0) (af : Bool) :
    ∃ result, issue state tid af = .ok result ∧ result.2.retired = 1 := by
  obtain ⟨advanced⟩ := advance current live located unfinished af
  exact ⟨advanced.result, advanced.actual, advanced.retired⟩

/-- A constructed own-only completion of exactly the remaining instruction
count, with arbitrary AF at each step. This is bounded OWN progress, separate
from any claim about scheduling fairness or physical instruction minima. -/
theorem complete {method : Method} {tid : Nat} {state : OS.TSO64.State} {point : Point}
    {worker : Worker} (current : Current method state) (live : state.workers[tid]? = some worker)
    (located : At method point worker) (choices : Nat → Bool) :
    ∃ actions result after event,
      actions.length = point.remaining ∧
      (∀ action ∈ actions, ∃ af, action = .issue tid af) ∧
      schedule state actions = .ok result ∧ result.1.workers[tid]? = some after ∧
      At method (.done event) after := by
  have termination : ∀ count state point worker, point.remaining = count →
      Current method state → state.workers[tid]? = some worker → At method point worker →
      ∀ choices : Nat → Bool, ∃ actions result after event,
        actions.length = count ∧ (∀ action ∈ actions, ∃ af, action = .issue tid af) ∧
        schedule state actions = .ok result ∧ result.1.workers[tid]? = some after ∧
        At method (.done event) after := by
    intro count
    induction count with
    | zero =>
      intro state point worker zero current live located choices
      cases point with
      | preamble offset padding => simp [Point.remaining] at zero
      | rmw offset => cases zero
      | ret offset event => cases zero
      | done event => exact ⟨[], (state, []), worker, event, rfl, by simp, rfl, live, located⟩
    | succ count ih =>
      intro state point worker remaining current live located choices
      have unfinished : point.remaining ≠ 0 := by omega
      obtain ⟨advanced⟩ := advance current live located unfinished (choices 0)
      have nextCount : advanced.next.remaining = count := by have := advanced.progress; omega
      obtain ⟨actions, result, after, event, length, own, scheduled, finalLive, finalAt⟩ :=
        ih advanced.result.1 advanced.next advanced.worker nextCount
          (current.step (action := .issue tid (choices 0)) advanced.actual)
          advanced.live advanced.located (fun index => choices (index + 1))
      refine ⟨.issue tid (choices 0) :: actions, (result.1, advanced.result.2 :: result.2), after, event,
        by simp [length], ?_, ?_, finalLive, finalAt⟩
      · intro action member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨choices 0, rfl⟩
        · exact own action later
      · simp only [schedule, OS.TSO64.step, advanced.actual, ok_bind, scheduled, pure_ok]
  exact termination point.remaining state point worker rfl current live located choices

/-- Independent function result and ABI-relevant register/stack frame.
The trace theorem separately preserves nonarithmetic flags, including DF. -/
structure BodyPost (method : Method) (worker : Worker) (event : Atomics64.FetchAddEvent) : Prop where
  phase : worker.phase = .returned
  resources : worker.resources = method.resources
  empty : worker.pending = []
  rip : worker.context.rip = method.returnAddress
  response : worker.context.registers method.locked.source = event.arithmetic.event.before
  rsp : worker.context.registers .rsp = method.entry .rsp + 8
  registers : ∀ register, register ≠ method.locked.source → register ≠ .rsp →
    worker.context.registers register = method.entry register
  correct : EventCorrect method event

theorem At.done_post {method : Method} {event : Atomics64.FetchAddEvent} {worker : Worker}
    (located : At method (.done event) worker) : BodyPost method worker event := by
  rcases located with ⟨resources, empty, phase, pc, registers, correct⟩
  refine ⟨phase, resources, empty, pc, ?_, ?_, ?_, correct⟩
  · rw [registers, written_other _ _ _ _ method.sourceNotRsp]
    exact written_same _ _ _
  · rw [registers]
    exact written_same _ _ _
  · intro register sourceNe rspNe
    rw [registers, written_other _ _ _ _ rspNe]
    exact written_other _ _ _ _ sourceNe

theorem At.returned_done {method : Method} {point : Point} {worker : Worker}
    (located : At method point worker) (returned : worker.phase = .returned) :
    ∃ event, point = .done event := by
  cases point with
  | done event => exact ⟨event, rfl⟩
  | preamble offset padding | rmw offset | ret offset event =>
    have running := located.2.2.1
    rw [returned] at running
    cases running

/-- Universal body correctness for EVERY admitted initial RF/resources, every
successful finite interleaving trace, and every completed own outcome. There
is exactly one own RMW occurrence. Its delta is the original argument and RET
returns its real old word. No protocol/label-matching premise appears here.

Peer actions are the actual TSO64 actions and may update this same target.
The caller loan and code remain current by the core frames. This standalone
unlabelled theorem does not assert complete-call matching or LegalHistory. -/
theorem all_completed {method : Method} {tid : Nat} {state : OS.TSO64.State} {padding : List Padding}
    {initial : Worker} (current : Current method state) (live : state.workers[tid]? = some initial)
    (entry : At method (.preamble 0 padding) initial) {actions : List Action}
    {result : OS.TSO64.State × List Observation} (success : schedule state actions = .ok result)
    {final : Worker} (finalLive : result.1.workers[tid]? = some final)
    (returned : final.phase = .returned) :
    Current method result.1 ∧ ∃ event,
      BodyPost method final event ∧ result.2.filterMap (ownEvent tid) = [event] ∧
      ownIssues tid actions = padding.length + 3 ∧
      final.context.flags &&& ~~~arithmeticFlagMask = initial.context.flags &&& ~~~arithmeticFlagMask := by
  obtain ⟨finalCurrent, point, after, afterLive, located, progress, events, flags⟩ :=
    schedule_preserves current live entry success
  have equal : after = final := Option.some.inj (afterLive.symm.trans finalLive)
  subst after
  obtain ⟨event, rfl⟩ := located.returned_done returned
  exact ⟨finalCurrent, event, located.done_post,
    by simpa only [Point.events, List.nil_append] using events,
    by simpa only [Point.remaining, Nat.zero_add] using progress, flags⟩

private theorem locked_location {method : Method} {state : OS.TSO64.State} {point : Point}
    {worker : Worker} (current : Current method state) (located : At method point worker)
    (running : worker.phase ≠ .returned) {instruction : LockedAdd64.Instruction}
    (decoded : OS.TSO64.decode (fetchCPU state worker) = .ok (.locked instruction)) :
    ∃ offset, point = .rmw offset ∧ instruction = method.locked := by
  have fits : Borrowing.Subregion ⟨method.base, method.bytes.length⟩ worker.resources.code.loan.region := by
    rw [located.1]
    exact current.fits
  have code := guarded_code current.code fits
  cases point with
  | preamble offset padding =>
    rcases located.2.2 with ⟨_, pc, _, shape⟩
    cases shape with
    | pad node tail =>
      have expected := node.decoded method.size code (fetchCPU state worker) rfl pc
      rw [expected] at decoded
      cases decoded
    | body copy rmw ret extent =>
      have expected := copy.decoded method.size code (fetchCPU state worker) rfl pc
      rw [expected] at decoded
      cases decoded
  | rmw offset =>
    rcases located.2.2 with ⟨_, pc, _, node, _⟩
    have expected := node.decoded method.size code (fetchCPU state worker) rfl pc
    rw [expected] at decoded
    have same : method.locked = instruction := OS.TSO64.Decoded.locked.inj (Except.ok.inj decoded)
    exact ⟨offset, rfl, same.symm⟩
  | ret offset event =>
    rcases located.2.2 with ⟨_, pc, _, node, _⟩
    have expected := node.decoded method.size code (fetchCPU state worker) rfl pc
    rw [expected] at decoded
    cases decoded
  | done event => exact False.elim (running located.2.2.1)

/-- An actual own RMW has the statically checked family instruction and real
prestate input. Its old word comes from the current typed effect, not a value
stored at invocation. The identifier is the actual selected handle. -/
theorem rmw_origin {method : Method} {state after : OS.TSO64.State} {tid : Nat} {point : Point}
    {worker : Worker} (current : Current method state) (live : state.workers[tid]? = some worker)
    (located : At method point worker) {action : Action} {event : Atomics64.FetchAddEvent}
    (success : OS.TSO64.step state action = .ok (after, .rmw tid event)) :
    ∃ offset af identifier machine,
      point = .rmw offset ∧ action = .issue tid af ∧
      Atomics64.FetchAddMachineEffect state.world method.resources.actor identifier
        (sharedCPU state worker) method.locked (after.world, event) machine ∧
      worker.context.registers method.locked.source = method.entry method.input ∧
      loadQWord (published state.world) event.arithmetic.event.address = .ok event.arithmetic.event.before := by
  cases step_origin success with
  | ordinary originLive running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue step finish => cases finish
  | @rmw tid af issuing instruction identifier output machine originLive running code caller fetched bounds empty grant effect =>
    have same := Option.some.inj (originLive.symm.trans live)
    subst worker
    obtain ⟨offset, pointEq, instructionEq⟩ := locked_location current located running fetched
    subst point
    subst instructionEq
    refine ⟨offset, af, identifier, machine, rfl, rfl, ?_, ?_, effect.cpu.old⟩
    · simpa only [install, located.1] using effect
    · rw [located.2.2.2.2.1]
      exact written_same _ _ _

/-- Initial own-empty FIFO and running phase are established by the real
resource attachment constructor, then retained by the no-store body theorem. -/
theorem entry_of_makeWorker {method : Method} {padding : List Padding}
    (shape : Shape method.bytes method.input method.locked 0 padding)
    {world : World} {actor : Nat} {context : Context} {codeId callerId : Nat}
    {grants : List Ownership.Ticket} {atomics : List Atomics64.HandleId64} {worker : Worker}
    (made : makeWorker world actor context codeId callerId grants atomics = .ok worker)
    (resources : worker.resources = method.resources) (registers : context.registers = method.entry)
    (pc : context.rip = method.base) : At method (.preamble 0 padding) worker := by
  obtain ⟨_, running, empty, same⟩ := makeWorker_valid made
  refine ⟨resources, empty, running, ?_, ?_, shape⟩
  · simpa only [same, BitVec.add_zero] using pc
  · rw [same]
    exact registers

/-- Extract one occurrence with its exact same-run prefix and suffix.
The trace is still the production schedule; no labelled replay is introduced. -/
theorem schedule_observation_origin {state : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} (success : schedule state actions = .ok result)
    {observation : Observation} (member : observation ∈ result.2) :
    ∃ priorActions before action after suffix prefixObservations suffixObservations,
      actions = priorActions ++ action :: suffix ∧
      result.2 = prefixObservations ++ observation :: suffixObservations ∧
      schedule state priorActions = .ok (before, prefixObservations) ∧
      OS.TSO64.step before action = .ok (after, observation) ∧
      schedule after suffix = .ok (result.1, suffixObservations) := by
  induction actions generalizing state result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    cases member
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok success
    rw [same] at member ⊢
    rcases List.mem_cons.mp member with equal | later
    · subst observation
      exact ⟨[], state, action, head.1, rest, [], tail.2, rfl, rfl, rfl, first, following⟩
    · obtain ⟨priorActions, before, origin, after, suffix, prefixObs, suffixObs,
        decomposition, observations, scheduled, actual, finished⟩ := ih following later
      refine ⟨action :: priorActions, before, origin, after, suffix, head.2 :: prefixObs, suffixObs,
        ?_, ?_, ?_, actual, finished⟩
      · simp only [List.cons_append, decomposition]
      · simp only [List.cons_append, observations]
      · simp only [schedule, first, ok_bind, scheduled, pure_ok]

private theorem ownEvent_some {tid : Nat} {observation : Observation} {event : Atomics64.FetchAddEvent}
    (present : ownEvent tid observation = some event) : observation = .rmw tid event := by
  cases observation with
  | rmw thread observed =>
    by_cases same : thread = tid
    · subst thread
      simp only [ownEvent, ite_true, Option.some.injEq] at present
      subst observed
      rfl
    · simp [ownEvent, same] at present
  | ordinary _ | returned _ | blocked _ | drained _ _ => cases present

/-- Exact occurrence evidence for later call/ABI adapters. Prefix/suffix
positions distinguish even identical zero-update events. The unique event list
from all_completed supplies occurrence uniqueness independently of its values. -/
def RMWOrigin (method : Method) (tid : Nat) (state : OS.TSO64.State) (actions : List Action)
    (result : OS.TSO64.State × List Observation) (event : Atomics64.FetchAddEvent) : Prop :=
  ∃ priorActions before worker af machine after suffix prefixObs suffixObs,
    actions = priorActions ++ .issue tid af :: suffix ∧
    result.2 = prefixObs ++ .rmw tid event :: suffixObs ∧
    schedule state priorActions = .ok (before, prefixObs) ∧
    before.workers[tid]? = some worker ∧ worker.pending = [] ∧
    worker.context.registers method.locked.source = method.entry method.input ∧
    OS.TSO64.step before (.issue tid af) = .ok (after, .rmw tid event) ∧
    Atomics64.FetchAddMachineEffect before.world method.resources.actor method.identifier
      (sharedCPU before worker) method.locked (after.world, event) machine ∧
    loadQWord (published before.world) event.arithmetic.event.address = .ok event.arithmetic.event.before ∧
    schedule after suffix = .ok (result.1, suffixObs)

/-- The universal result, plus a same-run real typed origin for its unique
RMW occurrence. This binds current bytes, operands, arithmetic and RET together
without assuming invocation/point/response labels or Protocol acceptance. -/
theorem all_completed_origin {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {padding : List Padding} {initial : Worker} (current : Current method state)
    (live : state.workers[tid]? = some initial) (entry : At method (.preamble 0 padding) initial)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule state actions = .ok result) {final : Worker}
    (finalLive : result.1.workers[tid]? = some final) (returned : final.phase = .returned) :
    Current method result.1 ∧ ∃ event,
      BodyPost method final event ∧ result.2.filterMap (ownEvent tid) = [event] ∧
      RMWOrigin method tid state actions result event ∧ ownIssues tid actions = padding.length + 3 ∧
      final.context.flags &&& ~~~arithmeticFlagMask = initial.context.flags &&& ~~~arithmeticFlagMask := by
  obtain ⟨finalCurrent, event, post, unique, count, flags⟩ :=
    all_completed current live entry success finalLive returned
  have member : event ∈ result.2.filterMap (ownEvent tid) := by rw [unique]; simp
  obtain ⟨observation, member, present⟩ := List.mem_filterMap.mp member
  have same := ownEvent_some present
  subst observation
  obtain ⟨priorActions, before, action, after, suffix, prefixObs, suffixObs,
    decomposition, observations, scheduled, actual, finished⟩ := schedule_observation_origin success member
  obtain ⟨originCurrent, point, worker, originLive, located, _, _, _⟩ :=
    schedule_preserves current live entry scheduled
  obtain ⟨offset, af, identifier, machine, _, actionEq, effect, source, old⟩ :=
    rmw_origin originCurrent originLive located actual
  have handle := (Atomics64.fetchAdd_sound _ _ _ _ _ effect.checked).2.2.2.2
  have identifierEq : identifier = method.identifier := handle.symm.trans post.correct.handle
  rw [identifierEq] at effect
  subst action
  exact ⟨finalCurrent, event, post, unique,
    ⟨priorActions, before, worker, af, machine, after, suffix, prefixObs, suffixObs,
      decomposition, observations, scheduled, originLive, located.2.1, source, actual, effect, old, finished⟩,
    count, flags⟩

/-- Every successful interleaving with the full own-instruction budget has
already returned. This is a finite own-progress bound, not scheduler fairness. -/
theorem enough_own_issues {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {padding : List Padding} {initial : Worker} (current : Current method state)
    (live : state.workers[tid]? = some initial) (entry : At method (.preamble 0 padding) initial)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule state actions = .ok result)
    (enough : padding.length + 3 ≤ ownIssues tid actions) :
    ∃ final, result.1.workers[tid]? = some final ∧ final.phase = .returned ∧ final.pending = [] := by
  obtain ⟨_, point, final, finalLive, located, progress, _, _⟩ :=
    schedule_preserves current live entry success
  have zero : point.remaining = 0 := by
    change point.remaining + ownIssues tid actions = padding.length + 3 at progress
    omega
  exact ⟨final, finalLive, located.zero_returned zero, located.2.1⟩

end EDSL.X86.VCGen.AtomicMethods

#audit_edsl
