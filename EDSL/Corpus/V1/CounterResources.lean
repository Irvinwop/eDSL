/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterResources.Image
import EDSL.Corpus.V1.CounterRetirement

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Actual present inputs for two counter workers in one compiler's complete loaded
ELF. Both production attachments consume the real manager's current loans and
singleton handles. The initial state is the successful output of the second
attachment, rather than an independently assigned worker fixture.

The two uint32 counts, upper RSI halves and complete modeled flags are arbitrary
and independent. Other registers use a convenient fixed value. There is no
all-register inhabitance claim, DF restriction, future execution, return value
or desired counter result in this construction. Store sequence labels start at
zero independently of iteration counts.

The imported long-mode/CET-off, coherent scalar WB RAM, stable translation and
no-alias, protected-loan and logical-authority assumptions remain. Actors 11/12
are logical principals, not scheduler tids or native identity authentication.
No native execution, physical security or additional corpus credit is claimed.
-/

namespace EDSL.Corpus.V1.CounterResources
open X86 OS OS.AddressSpace OS.TSO64 OS.TSO64.EffectSimulation

abbrev Compiler := CounterCommon.Compiler

def actor (slot : Fin 2) : Nat := if slot.val = 0 then 11 else 12

def stack (slot : Fin 2) : Word :=
  if slot.val = 0 then PlainResources.standard.stackA else PlainResources.standard.stackB

def continuation (slot : Fin 2) : Word :=
  if slot.val = 0 then PlainResources.standard.returnA else PlainResources.standard.returnB

/-- Names are selected from the actual setup output. -/
def codeId (compiler : Compiler) (old : Word) (slot : Fin 2) : Nat :=
  if slot.val = 0 then (Image.resources compiler old).codeA else (Image.resources compiler old).codeB

def callerId (compiler : Compiler) (old : Word) (slot : Fin 2) : Nat :=
  if slot.val = 0 then (Image.resources compiler old).callerA else (Image.resources compiler old).callerB

def atomicId (compiler : Compiler) (old : Word) (slot : Fin 2) : Atomics64.HandleId64 :=
  if slot.val = 0 then (Image.resources compiler old).atomicA else (Image.resources compiler old).atomicB

/-- Concatenation retains all upper input bits; count admission observes low32. -/
def argument (count upper : BitVec 32) : Word := upper ++ count

theorem argument_low32 (count upper : BitVec 32) :
    (argument count upper).setWidth 32 = count :=
  BitVec.setWidth_append_eq_right

theorem argument_upper32 (count upper : BitVec 32) :
    (argument count upper).extractLsb' 32 32 = upper :=
  BitVec.extractLsb'_append_eq_left

def context (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) : Context where
  registers register := match register with
    | .rsp => stack slot
    | .rdi => (Image.resources compiler old).cell.address
    | .rsi => argument (count slot) (upper slot)
    | _ => 0x8877665544332211
  rip := (Image.image compiler).base
  flags := flags slot

def emptyState (compiler : Compiler) (old : Word) : TSO64.State :=
  ⟨(Image.resources compiler old).managed.world, []⟩

/-- The first real attach is total for every contextual input. -/
theorem first_total (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    (TSO64.attach (emptyState compiler old) 11 (context compiler old count upper flags 0)
      (codeId compiler old 0) (callerId compiler old 0) [] [atomicId compiler old 0]).toOption.isSome = true := by
  cases compiler <;> buffer_resource_kernel_rfl

def first (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) : TSO64.State :=
  (TSO64.attach (emptyState compiler old) 11 (context compiler old count upper flags 0)
    (codeId compiler old 0) (callerId compiler old 0) [] [atomicId compiler old 0]).toOption.get
      (first_total compiler old count upper flags)

theorem first_attached (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    TSO64.attach (emptyState compiler old) 11 (context compiler old count upper flags 0)
      (codeId compiler old 0) (callerId compiler old 0) [] [atomicId compiler old 0] =
      .ok (first compiler old count upper flags) :=
  PlainResources.checked_get _ (first_total compiler old count upper flags)

/-- The second real attach consumes the first operation's actual result. -/
theorem second_total (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    (TSO64.attach (first compiler old count upper flags) 12 (context compiler old count upper flags 1)
      (codeId compiler old 1) (callerId compiler old 1) [] [atomicId compiler old 1]).toOption.isSome = true := by
  cases compiler <;> buffer_resource_kernel_rfl

def initial (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) : TSO64.State :=
  (TSO64.attach (first compiler old count upper flags) 12 (context compiler old count upper flags 1)
    (codeId compiler old 1) (callerId compiler old 1) [] [atomicId compiler old 1]).toOption.get
      (second_total compiler old count upper flags)

theorem second_attached (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    TSO64.attach (first compiler old count upper flags) 12 (context compiler old count upper flags 1)
      (codeId compiler old 1) (callerId compiler old 1) [] [atomicId compiler old 1] =
      .ok (initial compiler old count upper flags) :=
  PlainResources.checked_get _ (second_total compiler old count upper flags)

private theorem attach_world {before after : TSO64.State} {principal code caller : Nat}
    {entry : Context} {identifier : Atomics64.HandleId64}
    (success : TSO64.attach before principal entry code caller [] [identifier] = .ok after) :
    after.world = before.world := by
  cases made : TSO64.makeWorker before.world principal entry code caller [] [identifier] with
  | error fault => simp [TSO64.attach, made] at success
  | ok worker =>
    simp only [TSO64.attach, made, ok_bind, pure_ok, Except.ok.injEq] at success
    cases success
    rfl

theorem initial_world (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    (initial compiler old count upper flags).world = (Image.resources compiler old).managed.world :=
  (attach_world (second_attached compiler old count upper flags)).trans
    (attach_world (first_attached compiler old count upper flags))

/-- Authority is preserved by production attach under the explicit ownedOnly
profile. No Plain64 scalar-entry or shared-cell gate is used. -/
theorem wellFormed (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    WellFormed (initial compiler old count upper flags) .ownedOnly := by
  have emptyValid : WellFormed (emptyState compiler old) .ownedOnly :=
    ⟨(Image.resources compiler old).managed.valid, by simp [emptyState]⟩
  exact TSO64.attach_valid_for .ownedOnly
    (TSO64.attach_valid_for .ownedOnly emptyValid (first_attached compiler old count upper flags))
    (second_attached compiler old count upper flags)

/-- A normalization view only. Its equality to both actual output projections
is proved below; this expression does not supply current authority. -/
def workerView (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) : Worker where
  context := context compiler old count upper flags slot
  resources := {
    actor := actor slot
    code := ⟨codeId compiler old slot, ⟨⟨0, 0⟩, 23, actor slot,
      ⟨(Image.image compiler).base, (Image.image compiler).bytes.length⟩⟩⟩
    caller := ⟨callerId compiler old slot, ⟨⟨slot.val + 1, 0⟩, 21 + slot.val,
      actor slot, ⟨stack slot, 8⟩⟩⟩
    callerAddress := stack slot
    grants := []
    atomics := [atomicId compiler old slot] }
  phase := .running
  pending := []
  nextStore := 0

theorem workers_view (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    (initial compiler old count upper flags).workers =
      [workerView compiler old count upper flags 0, workerView compiler old count upper flags 1] := by
  cases compiler <;> buffer_resource_kernel_rfl

theorem workerUniverse2 (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    (initial compiler old count upper flags).workers.length = 2 := by
  rw [workers_view]
  rfl

/-- Project the worker from the actual attachment result. -/
def worker (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) : Worker :=
  (initial compiler old count upper flags).workers[slot.val]'(by
    rw [workerUniverse2]; exact slot.isLt)

theorem worker_live (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    (initial compiler old count upper flags).workers[slot.val]? =
      some (worker compiler old count upper flags slot) :=
  List.getElem?_eq_getElem (by rw [workerUniverse2]; exact slot.isLt)

theorem worker_view (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    worker compiler old count upper flags slot = workerView compiler old count upper flags slot := by
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl <;> simp only [worker, workers_view,
    List.getElem_cons_zero, List.getElem_cons_succ] <;> rfl

theorem quiescent (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    Quiescent (initial compiler old count upper flags) := by
  intro current member
  rw [workers_view] at member
  rcases List.mem_cons.mp member with same | member
  · cases same; rfl
  · rcases List.mem_cons.mp member with same | member
    · cases same; rfl
    · cases member

theorem codeId_eq (compiler : Compiler) (old : Word) (slot : Fin 2) :
    codeId compiler old slot = slot.val := by
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · exact (Image.resources_codes compiler old).1
  · exact (Image.resources_codes compiler old).2

theorem callerId_eq (compiler : Compiler) (old : Word) (slot : Fin 2) :
    callerId compiler old slot = slot.val + 2 := by
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · exact (Image.resources_callers compiler old).1
  · exact (Image.resources_callers compiler old).2

theorem atomicId_eq (compiler : Compiler) (old : Word) (slot : Fin 2) :
    atomicId compiler old slot = ⟨slot.val⟩ := by
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · exact (Image.resources_atomics compiler old).1
  · exact (Image.resources_atomics compiler old).2

theorem worker_context (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker compiler old count upper flags slot).context = context compiler old count upper flags slot := by
  rw [worker_view]
  rfl

theorem worker_count (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    ((worker compiler old count upper flags slot).context.registers .rsi).setWidth 32 = count slot := by
  rw [worker_context]
  exact argument_low32 _ _

theorem worker_upper (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    ((worker compiler old count upper flags slot).context.registers .rsi).extractLsb' 32 32 = upper slot := by
  rw [worker_context]
  exact argument_upper32 _ _

theorem worker_flags (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker compiler old count upper flags slot).context.flags = flags slot := by
  rw [worker_context]
  rfl

theorem worker_nextStore (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker compiler old count upper flags slot).nextStore = 0 := by
  rw [worker_view]
  rfl

theorem worker_actor (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker compiler old count upper flags slot).resources.actor = actor slot := by
  rw [worker_view]
  rfl

/-- The actual output projection carries current code and original caller
authority, not merely matching record fields. -/
theorem worker_resources (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    ResourcesValid (initial compiler old count upper flags).world
      (worker compiler old count upper flags slot).resources :=
  ((wellFormed compiler old count upper flags).2 _
    (List.mem_of_getElem? (worker_live compiler old count upper flags slot))).1

theorem selection (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    atomicFor (initial compiler old count upper flags).world
      (worker compiler old count upper flags slot).resources (Image.resources compiler old).cell.address =
      some (atomicId compiler old slot, ⟨actor slot, (Image.resources compiler old).target⟩,
        (Image.resources compiler old).cell) := by
  rw [initial_world, worker_view]
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl <;> cases compiler <;> buffer_resource_kernel_rfl

theorem caller_read (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    Borrowing.loadWord64 (initial compiler old count upper flags).world.legacy.shared
      (worker compiler old count upper flags slot).resources.actor
      (worker compiler old count upper flags slot).resources.caller.identifier
      (worker compiler old count upper flags slot).resources.callerAddress = .ok (continuation slot) := by
  rw [initial_world, worker_view]
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · exact Image.caller_readA compiler old
  · exact Image.caller_readB compiler old

theorem continuation_canonical (slot : Fin 2) : canonical (continuation slot) = true := by
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · change canonical (0x654320 : Word) = true
    decide +kernel
  · change canonical (0x654330 : Word) = true
    decide +kernel

def site (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) : CounterCommon.Site compiler where
  profile := .ownedOnly
  tid := slot.val
  original := worker compiler old count upper flags slot
  codeLoan := by
    rw [worker_view]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

def call (compiler : Compiler) (old : Word) (count : Fin 2 → BitVec 32) (slot : Fin 2) : CounterCommon.Call where
  address := (Image.resources compiler old).cell.address
  iterations := count slot
  target := (Image.resources compiler old).target
  returnAddress := continuation slot

theorem site_profile (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    (site compiler old count upper flags slot).profile = .ownedOnly := rfl

theorem site_slot (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    (site compiler old count upper flags slot).tid = slot.val := rfl

/-- Independent present-state admission, with the real current ordered atomic
selector and the original protected caller read. -/
theorem pre (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    CounterCommon.Pre (site compiler old count upper flags slot) (call compiler old count slot)
      (initial compiler old count upper flags) := by
  have running : (worker compiler old count upper flags slot).phase = .running := by
    rw [worker_view]
    rfl
  have code : CodeAt (published (initial compiler old count upper flags).world)
      (CounterCommon.base compiler) (CounterMixedGraphs.bytes compiler) := by
    rw [initial_world]
    exact Image.code compiler old
  have pc : (worker compiler old count upper flags slot).context.rip = CounterCommon.base compiler := by
    rw [worker_context]
    rfl
  have pointer : (worker compiler old count upper flags slot).context.registers .rdi =
      (Image.resources compiler old).cell.address := by
    rw [worker_context]
    rfl
  have rsp : (worker compiler old count upper flags slot).context.registers .rsp =
      (worker compiler old count upper flags slot).resources.callerAddress := by
    rw [worker_view]
    rfl
  constructor
  · constructor
    · simpa only [CounterCommon.descriptor, site] using wellFormed compiler old count upper flags
    · simpa only [CounterCommon.descriptor, site] using worker_live compiler old count upper flags slot
    · simpa only [CounterCommon.descriptor, site] using running
    · simpa only [CounterCommon.descriptor] using code
    · simpa only [CounterCommon.descriptor, site, call] using caller_read compiler old count upper flags slot
  · simpa only [CounterCommon.descriptor, site] using pc
  · simpa only [site, call] using pointer
  · simpa only [site, call] using worker_count compiler old count upper flags slot
  · simpa only [site] using rsp
  · exact continuation_canonical slot
  · unfold CounterCommon.Selected
    refine ⟨atomicId compiler old slot, ⟨actor slot, (Image.resources compiler old).target⟩,
      (Image.resources compiler old).cell, ?_, rfl⟩
    simpa only [site, call] using selection compiler old count upper flags slot

theorem registered (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    (initial compiler old count upper flags).world.cells (Image.resources compiler old).target =
      some (Image.resources compiler old).cell := by
  rw [initial_world]
  exact Image.resources_live compiler old

theorem initial_read (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    loadQWord (published (initial compiler old count upper flags).world)
      (Image.resources compiler old).cell.address = .ok old := by
  rw [initial_world, Image.target_address]
  exact Image.initial_read compiler old

/-- Exact loaded cells retain their permission records as well as byte values. -/
theorem full_image (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    {address : Word} {original : AddressSpace.Cell}
    (live : (Image.installed compiler).space.cells address = some original) :
    (initial compiler old count upper flags).world.legacy.shared.resources.space.cells address = some original := by
  rw [initial_world]
  exact Image.full_image compiler old live

theorem code_cell (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (index : Nat)
    (bound : index < (Image.image compiler).bytes.length) :
    (initial compiler old count upper flags).world.legacy.shared.resources.space.cells
      ((Image.image compiler).base + BitVec.ofNat 64 index) =
      some ⟨(Image.image compiler).bytes[index], readExecute⟩ :=
  full_image compiler old count upper flags (Image.installed_cell compiler index bound)

theorem fresh_target (compiler : Compiler) (old : Word) :
    allUnmapped (Image.installed compiler).space ⟨(Image.resources compiler old).cell.address, 8⟩ = true := by
  rw [Image.target_address]
  exact Image.fresh_target compiler old

theorem target_outside_loaded (compiler : Compiler) (old : Word)
    {address : Word} {original : AddressSpace.Cell}
    (live : (Image.installed compiler).space.cells address = some original) :
    ¬(⟨(Image.resources compiler old).cell.address, 8⟩ : Region).Contains address := by
  intro inside
  have absent := allUnmapped_inside _ _ (fresh_target compiler old) address inside
  rw [live] at absent
  cases absent

theorem caller_protected (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    PlainResources.allReadOnly (initial compiler old count upper flags).world.legacy.shared.resources.space
      (worker compiler old count upper flags slot).resources.caller.loan.region = true := by
  rw [initial_world, worker_view]
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · exact (Image.caller_protected compiler old).1
  · exact (Image.caller_protected compiler old).2

theorem private_callers (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    Ownership.Disjoint
      (worker compiler old count upper flags 0).resources.caller.loan.region
      (worker compiler old count upper flags 1).resources.caller.loan.region := by
  rw [worker_view, worker_view]
  change Ownership.Disjoint (⟨0x700008, 8⟩ : Region) ⟨0x710008, 8⟩
  decide +kernel

theorem code_caller_disjoint (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (codeSlot callerSlot : Fin 2) :
    Ownership.Disjoint
      (worker compiler old count upper flags codeSlot).resources.code.loan.region
      (worker compiler old count upper flags callerSlot).resources.caller.loan.region := by
  rw [worker_view, worker_view]
  change Ownership.Disjoint
    ⟨(Image.image compiler).base, (Image.image compiler).bytes.length⟩ ⟨stack callerSlot, 8⟩
  rw [Image.image_length]
  rcases callerSlot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · cases compiler with
    | defaultGCC =>
      change Ownership.Disjoint (⟨4207440, 49⟩ : Region) ⟨0x700008, 8⟩
      decide +kernel
    | defaultClang =>
      change Ownership.Disjoint (⟨4201344, 86⟩ : Region) ⟨0x700008, 8⟩
      decide +kernel
  · cases compiler with
    | defaultGCC =>
      change Ownership.Disjoint (⟨4207440, 49⟩ : Region) ⟨0x710008, 8⟩
      decide +kernel
    | defaultClang =>
      change Ownership.Disjoint (⟨4201344, 86⟩ : Region) ⟨0x710008, 8⟩
      decide +kernel

theorem target_caller_disjoint (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    Ownership.Disjoint ⟨(Image.resources compiler old).cell.address, 8⟩
      (worker compiler old count upper flags slot).resources.caller.loan.region := by
  rw [worker_view, Image.target_address]
  change Ownership.Disjoint ⟨PlainResources.standard.target, 8⟩ ⟨stack slot, 8⟩
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · change Ownership.Disjoint (⟨0x10000, 8⟩ : Region) ⟨0x700008, 8⟩
    decide +kernel
  · change Ownership.Disjoint (⟨0x10000, 8⟩ : Region) ⟨0x710008, 8⟩
    decide +kernel

theorem cleanupShape (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    CounterCommon.CleanupShape (site compiler old count upper flags slot) := by
  have shape : ∃ identifier,
      (worker compiler old count upper flags slot).resources.atomics = [identifier] ∧
      (worker compiler old count upper flags slot).resources.code.identifier ≠
        (worker compiler old count upper flags slot).resources.caller.identifier := by
    rw [worker_view]
    refine ⟨atomicId compiler old slot, rfl, ?_⟩
    change codeId compiler old slot ≠ callerId compiler old slot
    rw [codeId_eq, callerId_eq]
    omega
  simpa only [CounterCommon.CleanupShape, site] using shape

/-- Every cross-loan inequality and disjoint singleton-handle manifest is
derived from actual setup IDs. Actor inequality is not a separation premise. -/
theorem separate (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    (initial compiler old count upper flags).workers.reverse.Pairwise
      (fun retiring peer => Lifecycle.Separate retiring.resources peer.resources) := by
  rw [workers_view]
  have distinct : Lifecycle.Separate
      (workerView compiler old count upper flags 1).resources
      (workerView compiler old count upper flags 0).resources := by
    simp [Lifecycle.Separate, workerView, codeId_eq, callerId_eq, atomicId_eq]
  simpa using distinct

#print axioms Compiler
#print axioms actor
#print axioms stack
#print axioms continuation
#print axioms codeId
#print axioms callerId
#print axioms atomicId
#print axioms argument
#print axioms argument_low32
#print axioms argument_upper32
#print axioms context
#print axioms emptyState
#print axioms first_total
#print axioms first
#print axioms first_attached
#print axioms second_total
#print axioms initial
#print axioms second_attached
#print axioms attach_world
#print axioms initial_world
#print axioms wellFormed
#print axioms workerView
#print axioms workers_view
#print axioms workerUniverse2
#print axioms worker
#print axioms worker_live
#print axioms worker_view
#print axioms quiescent
#print axioms codeId_eq
#print axioms callerId_eq
#print axioms atomicId_eq
#print axioms worker_context
#print axioms worker_count
#print axioms worker_upper
#print axioms worker_flags
#print axioms worker_nextStore
#print axioms worker_actor
#print axioms worker_resources
#print axioms selection
#print axioms caller_read
#print axioms continuation_canonical
#print axioms site
#print axioms call
#print axioms site_profile
#print axioms site_slot
#print axioms pre
#print axioms registered
#print axioms initial_read
#print axioms full_image
#print axioms code_cell
#print axioms fresh_target
#print axioms target_outside_loaded
#print axioms caller_protected
#print axioms private_callers
#print axioms code_caller_disjoint
#print axioms target_caller_disjoint
#print axioms cleanupShape
#print axioms separate

end EDSL.Corpus.V1.CounterResources

#audit_edsl
