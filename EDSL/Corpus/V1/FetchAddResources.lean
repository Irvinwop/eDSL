/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.FetchAddBodies
import EDSL.Corpus.ELFResources
import EDSL.OS.FetchAddABI64

set_option warningAsError true

/-!
Current resources at the two frozen ELF entries. The new modeled registry starts
with the COMPLETE installed ELF, adopts its checked function interval, and uses
the existing checked manager for allocations, initialization, protection, loans,
cell enrollment and handle issue. It authenticates no native OS principal.
The callable text contract is the existing FunctionWindow.TextUnchanged slice;
the complete file/name/extent obligation remains FetchAddWindows.checked.
-/

namespace EDSL.Corpus.V1.FetchAddResources
open X86 OS OS.AddressSpace OS.TSO64

/-- Emit only Eq.refl of the right side; the kernel checks definitional equality
against the original goal, including free symbolic words. This avoids expanding
the complete checked manager setup in the elaborator's recursive unifier. It
changes no limits, evaluates no native code and adds no trusted proof rule. -/
elab "fetch_add_kernel_rfl" : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let some (_, _, rhs) := (← Lean.Meta.whnf (← goal.getType)).eq? |
      Lean.throwError "expected an equality"
    let proof ← Lean.Meta.mkEqRefl rhs
    Lean.Elab.Tactic.closeMainGoal `fetch_add_kernel_rfl proof

abbrev Compiler := FetchAddWindows.Compiler
variable {Id : Type}

def entry (compiler : Compiler) : Word := (FetchAddWindows.function compiler).window.base

def image (compiler : Compiler) : FetchAddABI64.Image :=
  ⟨entry compiler, FetchAddWindows.bytes compiler⟩

def installed (compiler : Compiler) : ELF.Loaded :=
  ⟨(FetchAddWindows.input compiler).table.image,
    ELF.install (FetchAddWindows.file compiler) (FetchAddWindows.input compiler).table.image empty⟩

theorem admitted (compiler : Compiler) :
    (FetchAddWindows.input compiler).admit (FetchAddWindows.file compiler)
      FetchAddWindows.name empty = .ok (installed compiler) := by
  have fresh : ELF.fresh (FetchAddWindows.input compiler).table.image empty = true := by
    apply List.all_eq_true.mpr
    intro segment _
    apply List.all_eq_true.mpr
    intro address _
    rfl
  exact ELFResources.admitted (caller := ⟨empty, 0, 0, 0, 0, 0⟩)
    (FetchAddWindows.checked compiler) fresh

theorem executable_permissions (compiler : Compiler) :
    ∀ segment ∈ (FetchAddWindows.input compiler).table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute := by
  cases compiler <;> decide +kernel

private theorem segmentCell_permissions (file : List Byte) (segment : ELF.Segment)
    (address : Nat) (cell : AddressSpace.Cell)
    (found : ELF.segmentCell file segment address = some cell) :
    cell.permissions = segment.permissions := by
  dsimp only [ELF.segmentCell] at found
  split at found
  · cases byte : file[segment.offset + (address - segment.virtualAddress)]? with
    | none => simp [byte] at found
    | some value =>
      simp only [byte, Option.map_some, Option.some.injEq] at found
      subst cell
      rfl
  · cases Option.some.inj found
    rfl

theorem installed_cell (compiler : Compiler) (index : Nat)
    (bound : index < (FetchAddWindows.bytes compiler).length) :
    (installed compiler).space.cells (entry compiler + BitVec.ofNat 64 index) =
      some ⟨(FetchAddWindows.bytes compiler)[index], readExecute⟩ := by
  have code := (ELF.FunctionSymbol.admitted_sound (admitted compiler)).2.2.2.2.1
  have fetched := code.2 index (FetchAddWindows.bytes compiler)[index]
    (List.getElem?_eq_getElem bound)
  let address := entry compiler + BitVec.ofNat 64 index
  change fetchByte (toMemory (installed compiler).space) address = .ok _ at fetched
  cases found : (installed compiler).space.cells address with
  | none => simp [fetchByte, toMemory, found] at fetched
  | some current =>
    have facts : canonical address = true ∧ current.permissions.readable = true ∧
        current.permissions.executable = true ∧ current.byte = (FetchAddWindows.bytes compiler)[index] := by
      cases canonical : X86.canonical address <;>
        cases readable : current.permissions.readable <;>
        cases executable : current.permissions.executable <;>
        simp_all [fetchByte, toMemory]
    have permissions : current.permissions = readExecute := by
      cases selected : ELF.segmentAt (FetchAddWindows.input compiler).table.image address.toNat with
      | none => simp [installed, ELF.install, selected, empty] at found
      | some segment =>
        have raw : ELF.segmentCell (FetchAddWindows.file compiler) segment address.toNat = some current := by
          simpa only [installed, ELF.install, selected] using found
        have projected := segmentCell_permissions _ _ _ _ raw
        exact projected.trans (executable_permissions compiler segment
          (List.mem_of_find?_eq_some selected) (projected ▸ facts.2.2.1))
    have equal : current = ⟨(FetchAddWindows.bytes compiler)[index], readExecute⟩ := by
      cases current
      simp_all
    exact congrArg some equal

/-- An extensionally identical representation of the COMPLETE loaded space.
Only the already checked function slice is indexed directly, avoiding repeated
linear traversal of the large literal file during checked resource setup. -/
def programSpace (compiler : Compiler) : Space where
  cells address :=
    if (⟨entry compiler, (FetchAddWindows.bytes compiler).length⟩ : Region).Contains address then
      some ⟨((FetchAddWindows.bytes compiler)[address.toNat - (entry compiler).toNat]?).getD 0, readExecute⟩
    else (installed compiler).space.cells address

theorem programSpace_eq (compiler : Compiler) : programSpace compiler = (installed compiler).space := by
  apply congrArg Space.mk
  funext address
  change (programSpace compiler).cells address = (installed compiler).space.cells address
  by_cases inside : (⟨entry compiler, (FetchAddWindows.bytes compiler).length⟩ : Region).Contains address
  · let offset := address.toNat - (entry compiler).toNat
    change (entry compiler).toNat ≤ address.toNat ∧
      address.toNat < (entry compiler).toNat + (FetchAddWindows.bytes compiler).length at inside
    have bound : offset < (FetchAddWindows.bytes compiler).length := by
      dsimp [offset]; rcases inside with ⟨lower, upper⟩; omega
    have small : offset < 2^64 := by dsimp [offset]; have := address.isLt; omega
    have sum : (entry compiler).toNat + offset = address.toNat := by
      dsimp [offset]; have := inside.1; omega
    have same : entry compiler + BitVec.ofNat 64 offset = address := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, sum,
        Nat.mod_eq_of_lt address.isLt]
    have original := installed_cell compiler offset bound
    rw [same] at original
    change (if _ then some (⟨_, readExecute⟩ : AddressSpace.Cell) else _) = _
    change (if ((entry compiler).toNat ≤ address.toNat ∧
      address.toNat < (entry compiler).toNat + (FetchAddWindows.bytes compiler).length)
      then some (⟨_, readExecute⟩ : AddressSpace.Cell) else _) = _
    rw [ite_eq_left inside, original]
    change some (⟨((FetchAddWindows.bytes compiler)[offset]?).getD 0, readExecute⟩ : AddressSpace.Cell) = _
    rw [List.getElem?_eq_getElem bound, Option.getD_some]
  · change (if _ then some (⟨_, readExecute⟩ : AddressSpace.Cell) else _) = _
    rw [ite_eq_right inside]

structure Managed where
  world : Atomics64.State
  valid : Atomics64.WellFormed world

def seed (compiler : Compiler) : Managed :=
  ⟨Atomics64.empty (Atomics.empty (Borrowing.empty (Ownership.empty (programSpace compiler)))),
    Atomics64.empty_wellFormed _ (Atomics.empty_wellFormed _
      (Borrowing.empty_wellFormed _ (Ownership.empty_wellFormed _)))⟩

def mutate (before : Managed) (operation : Ownership.Mutation) :
    Except Atomics64.Fault (Managed × Option Ownership.Ticket) :=
  match success : Atomics64.mutate before.world operation with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, Atomics64.mutate_wellFormed _ _ _ before.valid success⟩, result.2)

def borrow (before : Managed) (owner : Nat) (ticket : Ownership.Ticket)
    (actor : Nat) (region : Region) : Except Atomics64.Fault (Managed × Nat) :=
  match success : Atomics64.readBorrow before.world owner ticket actor region with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1,
      Atomics64.readBorrow_wellFormed _ _ _ _ _ _ before.valid success⟩, result.2)

def enroll (before : Managed) (ticket : Ownership.Ticket) :
    Except Atomics64.Fault (Managed × Atomics64.CellId64) :=
  match success : Atomics64.enroll before.world 7 ticket 0x10000 with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1,
      (Atomics64.enroll_wellFormed _ _ _ _ _ before.valid success).1⟩, result.2)

def handle (before : Managed) (cell : Atomics64.CellId64) (actor : Nat) :
    Except Atomics64.Fault (Managed × Atomics64.HandleId64) :=
  match success : Atomics64.issue before.world 7 cell actor with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1,
      (Atomics64.issue_wellFormed _ _ _ _ _ before.valid success).1⟩, result.2)

def ticket : Option Ownership.Ticket → Except Atomics64.Fault Ownership.Ticket
  | none => .error .missingCell
  | some result => .ok result

def caller (before : Managed) (owner actor : Nat) (address returnAddress : Word) :
    Except Atomics64.Fault (Managed × Nat) := do
  let (allocated, output) ← mutate before (.allocate owner ⟨address, 8⟩ readWrite)
  let allocation ← ticket output
  let (written, _) ← mutate allocated (.store64 owner allocation address returnAddress)
  let (readable, _) ← mutate written (.protect owner allocation readOnly)
  borrow readable owner allocation actor ⟨address, 8⟩

structure Ready where
  managed : Managed
  codeA : Nat
  codeB : Nat
  callerA : Nat
  callerB : Nat
  atomicA : Atomics64.HandleId64
  atomicB : Atomics64.HandleId64

/-- Real checked setup, with an arbitrary original full64 counter word. Code is
adopted from the complete installed file, never rewritten or recompiled. -/
def setup (compiler : Compiler) (old : Word) : Except Atomics64.Fault Ready := do
  let (code, output) ← mutate (seed compiler)
    (.adopt 23 ⟨entry compiler, (FetchAddWindows.bytes compiler).length⟩)
  let codeTicket ← ticket output
  let (oneCode, codeA) ← borrow code 23 codeTicket 11
    ⟨entry compiler, (FetchAddWindows.bytes compiler).length⟩
  let (twoCodes, codeB) ← borrow oneCode 23 codeTicket 12
    ⟨entry compiler, (FetchAddWindows.bytes compiler).length⟩
  let (allocated, output) ← mutate twoCodes (.allocate 7 ⟨0x10000, 8⟩ readWrite)
  let counterTicket ← ticket output
  let (initialized, _) ← mutate allocated (.store64 7 counterTicket 0x10000 old)
  let (oneCaller, callerA) ← caller initialized 21 11 0x700008 0x654320
  let (twoCallers, callerB) ← caller oneCaller 22 12 0x710008 0x654330
  let (registered, cell) ← enroll twoCallers counterTicket
  let (oneHandle, atomicA) ← handle registered cell 11
  let (twoHandles, atomicB) ← handle oneHandle cell 12
  return ⟨twoHandles, codeA, codeB, callerA, callerB, atomicA, atomicB⟩

theorem setup_total (compiler : Compiler) (old : Word) :
    (setup compiler old).toOption.isSome = true := by
  cases compiler <;> fetch_add_kernel_rfl

def ready (compiler : Compiler) (old : Word) : Ready :=
  (setup compiler old).toOption.get (setup_total compiler old)

def target : Atomics64.CellId64 := ⟨0⟩
def cell : Atomics64.Cell := ⟨7, ⟨1, 0⟩, 0x10000⟩

def context (compiler : Compiler) (stack delta : Word) : Context where
  registers register := match register with
    | .rsp => stack
    | .rdi => cell.address
    | .rsi => delta
    | _ => 0x8877665544332211
  rip := entry compiler
  flags := 0x202

structure Checked where
  state : OS.TSO64.State
  valid : WellFormed state

def attach (before : Checked) (actor : Nat) (context : Context)
    (code caller : Nat) (atomic : Atomics64.HandleId64) : Except OS.TSO64.Fault Checked :=
  match success : OS.TSO64.attach before.state actor context code caller [] [atomic] with
  | .error fault => .error fault
  | .ok state => .ok ⟨state, attach_valid before.valid success⟩

def start (compiler : Compiler) (old deltaA deltaB : Word) : Except OS.TSO64.Fault Checked := do
  let resources := ready compiler old
  let before : Checked := ⟨⟨resources.managed.world, []⟩, resources.managed.valid, by simp⟩
  let one ← attach before 11 (context compiler 0x700008 deltaA)
    resources.codeA resources.callerA resources.atomicA
  attach one 12 (context compiler 0x710008 deltaB)
    resources.codeB resources.callerB resources.atomicB

theorem start_total (compiler : Compiler) (old deltaA deltaB : Word) :
    (start compiler old deltaA deltaB).toOption.isSome = true := by
  cases compiler <;> fetch_add_kernel_rfl

def started (compiler : Compiler) (old deltaA deltaB : Word) : Checked :=
  (start compiler old deltaA deltaB).toOption.get (start_total compiler old deltaA deltaB)

theorem live (compiler : Compiler) (old deltaA deltaB : Word) :
    (started compiler old deltaA deltaB).state.world.cells target = some cell := by
  cases compiler <;> fetch_add_kernel_rfl

def current (compiler : Compiler) (old deltaA deltaB : Word) :
    FetchAddCalls64.CheckedState target cell :=
  ⟨(started compiler old deltaA deltaB).state, (started compiler old deltaA deltaB).valid,
    live compiler old deltaA deltaB⟩

/-- A projection used only to normalize setup's memory frame. Equality to the
actual checked setup is proved below; this supplies no separate authority/WF. -/
def counterData (compiler : Compiler) (old : Word) : Space :=
  writeQWordCells (mapUnchecked (programSpace compiler) ⟨0x10000, 8⟩ readWrite) 0x10000 old

def freshCaller (before : Space) (address value : Word) : Space :=
  protectUnchecked (writeQWordCells (mapUnchecked before ⟨address, 8⟩ readWrite) address value)
    ⟨address, 8⟩ readOnly

def spaceView (compiler : Compiler) (old : Word) : Space :=
  freshCaller (freshCaller (counterData compiler old) 0x700008 0x654320) 0x710008 0x654330

theorem freshCaller_read (before : Space) (address value query : Word) :
    (toMemory (freshCaller before address value)).read query =
      (toMemory (writeQWordCells (mapUnchecked before ⟨address, 8⟩ readWrite) address value)).read query := by
  by_cases inside : (⟨address, 8⟩ : Region).Contains query
  · simp only [freshCaller, toMemory, protectUnchecked, writeQWordCells, mapUnchecked,
      qwordRegion, ite_eq_left inside, Option.map_some]
    rfl
  · simp only [freshCaller, toMemory, protectUnchecked, writeQWordCells, mapUnchecked,
      qwordRegion, ite_eq_right inside]

theorem freshCaller_frame (before : Space) (address value query : Word)
    (outside : ¬ (⟨address, 8⟩ : Region).Contains query) :
    (toMemory (freshCaller before address value)).read query = (toMemory before).read query := by
  simp only [freshCaller, toMemory, protectUnchecked, writeQWordCells, mapUnchecked,
    qwordRegion, ite_eq_right outside]

theorem installed_free (compiler : Compiler) (address : Word)
    (selected : address = 0x10000 ∨ address = 0x700008 ∨ address = 0x710008) :
    allUnmapped (installed compiler).space ⟨address, 8⟩ = true := by
  rcases selected with rfl | rfl | rfl <;> cases compiler <;> decide +kernel

/-- The complete installed image survives setup, not just the selected code.
The additional mappings were initially absent; all stores/protection affect
only those fresh regions. Thus this adapter needs no weaker loaded-image gate. -/
theorem installed_frame (compiler : Compiler) (old : Word) {address : Word}
    {original : AddressSpace.Cell} (existing : (installed compiler).space.cells address = some original) :
    (spaceView compiler old).cells address = some original := by
  have outside (base : Word) (selected : base = 0x10000 ∨ base = 0x700008 ∨ base = 0x710008) :
      ¬ (⟨base, 8⟩ : Region).Contains address := by
    intro inside
    have absent := allUnmapped_inside _ _ (installed_free compiler base selected) address inside
    rw [existing] at absent
    cases absent
  have counter := outside 0x10000 (Or.inl rfl)
  have callerA := outside 0x700008 (Or.inr (Or.inl rfl))
  have callerB := outside 0x710008 (Or.inr (Or.inr rfl))
  have present : (programSpace compiler).cells address = some original := by
    rw [programSpace_eq]; exact existing
  simpa only [spaceView, freshCaller, counterData, mapUnchecked, writeQWordCells, protectUnchecked,
    qwordRegion, ite_eq_right counter, ite_eq_right callerA, ite_eq_right callerB] using present

theorem space (compiler : Compiler) (old deltaA deltaB : Word) :
    (current compiler old deltaA deltaB).state.world.legacy.shared.resources.space =
      spaceView compiler old := by
  cases compiler <;> fetch_add_kernel_rfl

theorem memory (compiler : Compiler) (old deltaA deltaB : Word) :
    published (current compiler old deltaA deltaB).state.world = toMemory (spaceView compiler old) :=
  congrArg toMemory (space compiler old deltaA deltaB)

theorem full_image (compiler : Compiler) (old deltaA deltaB : Word) {address : Word}
    {original : AddressSpace.Cell} (existing : (installed compiler).space.cells address = some original) :
    (current compiler old deltaA deltaB).state.world.legacy.shared.resources.space.cells address =
      some original := by
  rw [space]
  exact installed_frame compiler old existing

/-- Actual setup retains the checked installation's entire selected function
interval, including execute permission and GCC's leading ENDBR64. -/
theorem text (compiler : Compiler) (old deltaA deltaB : Word) :
    ELF.FunctionWindow.TextUnchanged (toMemory (installed compiler).space)
      (published (current compiler old deltaA deltaB).state.world)
      (FetchAddWindows.function compiler).window (FetchAddWindows.bytes compiler).length := by
  intro index bound
  rw [memory]
  rw [← programSpace_eq compiler]
  cases compiler with
  | defaultGCC =>
    have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
        index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨
        index = 11 ∨ index = 12 := by change index < 13 at bound; omega
    rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals constructor <;> fetch_add_kernel_rfl
  | defaultClang =>
    have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
        index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by change index < 9 at bound; omega
    rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals constructor <;> fetch_add_kernel_rfl

theorem code (compiler : Compiler) (old deltaA deltaB : Word) :
    CodeAt (published (current compiler old deltaA deltaB).state.world)
      (entry compiler) (FetchAddWindows.bytes compiler) :=
  ELF.FunctionSymbol.admitted_current_code (admitted compiler) (text compiler old deltaA deltaB)

/-- The arbitrary initial counter word is read back from real store64 bytes.
The existing whole-qword store theorem supplies serialization correctness. -/
theorem initial_read (compiler : Compiler) (old deltaA deltaB : Word) :
    FetchAddCalls64.read (current compiler old deltaA deltaB).state cell = .ok old := by
  let data := mapUnchecked (programSpace compiler) ⟨0x10000, 8⟩ readWrite
  have stored : AddressSpace.storeQWord data 0x10000 old =
      .ok (writeQWordCells data 0x10000 old) := by
    cases compiler <;> fetch_add_kernel_rfl
  have observed := (AddressSpace.storeQWord_sound _ _ _ _ stored).2.1
  have agrees : MemoryAgreesOn (toMemory (spaceView compiler old))
      (toMemory (writeQWordCells data 0x10000 old)) 0x10000 8 := by
    intro index bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
    rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases compiler <;> fetch_add_kernel_rfl
  change loadQWord (published (current compiler old deltaA deltaB).state.world) 0x10000 = .ok old
  rw [memory, loadQWord_congr _ _ _ agrees]
  exact observed

theorem workers_length (compiler : Compiler) (old deltaA deltaB : Word) :
    (current compiler old deltaA deltaB).state.workers.length = 2 := by
  cases compiler <;> fetch_add_kernel_rfl

def worker (compiler : Compiler) (old deltaA deltaB : Word) (tid : Fin 2) : Worker :=
  (current compiler old deltaA deltaB).state.workers[tid.val]'(by
    rw [workers_length]; exact tid.isLt)

theorem worker_live (compiler : Compiler) (old deltaA deltaB : Word) (tid : Fin 2) :
    (current compiler old deltaA deltaB).state.workers[tid.val]? =
      some (worker compiler old deltaA deltaB tid) :=
  List.getElem?_eq_getElem (by rw [workers_length]; exact tid.isLt)

def stack (tid : Fin 2) : Word := if tid.val = 0 then 0x700008 else 0x710008
def returnAddress (tid : Fin 2) : Word := if tid.val = 0 then 0x654320 else 0x654330
def actor (tid : Fin 2) : Nat := if tid.val = 0 then 11 else 12
def delta (deltaA deltaB : Word) (tid : Fin 2) : Word := if tid.val = 0 then deltaA else deltaB

/-- Present descriptor view, authenticated by equality to the actual attached
worker. The setup, rather than this record expression, supplies authority. -/
def workerView (compiler : Compiler) (deltaA deltaB : Word) (tid : Fin 2) : Worker where
  context := context compiler (stack tid) (delta deltaA deltaB tid)
  resources := {
    actor := actor tid
    code := ⟨tid.val, ⟨⟨0, 0⟩, 23, actor tid,
      ⟨entry compiler, (FetchAddWindows.bytes compiler).length⟩⟩⟩
    caller := ⟨tid.val + 2, ⟨⟨tid.val + 2, 0⟩, tid.val + 21, actor tid, ⟨stack tid, 8⟩⟩⟩
    callerAddress := stack tid
    grants := []
    atomics := [⟨tid.val⟩] }
  phase := .running
  pending := []

theorem worker_view (compiler : Compiler) (old deltaA deltaB : Word) (tid : Fin 2) :
    worker compiler old deltaA deltaB tid = workerView compiler deltaA deltaB tid := by
  rcases tid with ⟨tid, bound⟩
  have choices : tid = 0 ∨ tid = 1 := by omega
  rcases choices with rfl | rfl <;> cases compiler <;> fetch_add_kernel_rfl

theorem worker_present (compiler : Compiler) (old deltaA deltaB : Word) (tid : Fin 2) :
    FetchAddABI64.Present (image compiler) cell (worker compiler old deltaA deltaB tid)
      (delta deltaA deltaB tid) := by
  rw [worker_view]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ⟨Nat.le_refl _, Nat.le_refl _⟩, ?_, ?_⟩
  · change 0 < (FetchAddWindows.bytes compiler).length
    cases compiler <;> decide +kernel
  · change canonical (entry compiler) = true
    cases compiler <;> decide +kernel
  · change (stack tid).toNat + 8 < 2^64
    rcases tid with ⟨tid, bound⟩
    have choices : tid = 0 ∨ tid = 1 := by omega
    rcases choices with rfl | rfl
    · change (0x700008 : Word).toNat + 8 < 2^64; decide +kernel
    · change (0x710008 : Word).toNat + 8 < 2^64; decide +kernel
  · change canonical (stack tid + 8) = true
    rcases tid with ⟨tid, bound⟩
    have choices : tid = 0 ∨ tid = 1 := by omega
    rcases choices with rfl | rfl
    · change canonical ((0x700008 : Word) + 8) = true; decide +kernel
    · change canonical ((0x710008 : Word) + 8) = true; decide +kernel

theorem worker_abi (compiler : Compiler) (old deltaA deltaB : Word) (tid : Fin 2) :
    FetchAddABI64.ScalarEntry (worker compiler old deltaA deltaB tid) := by
  rw [worker_view]
  constructor
  · change ((stack tid).toNat + 8) % 16 = 0
    rcases tid with ⟨tid, bound⟩
    have choices : tid = 0 ∨ tid = 1 := by omega
    rcases choices with rfl | rfl
    · change ((0x700008 : Word).toNat + 8) % 16 = 0; decide +kernel
    · change ((0x710008 : Word).toNat + 8) % 16 = 0; decide +kernel
  · change (0x202 : Word).getLsbD 10 = false
    decide +kernel

theorem worker_selection (compiler : Compiler) (old deltaA deltaB : Word) (tid : Fin 2) :
    atomicFor (current compiler old deltaA deltaB).state.world
      (worker compiler old deltaA deltaB tid).resources cell.address =
      some (⟨tid.val⟩, ⟨actor tid, target⟩, cell) := by
  rcases tid with ⟨tid, bound⟩
  have choices : tid = 0 ∨ tid = 1 := by omega
  rcases choices with rfl | rfl <;> cases compiler <;> fetch_add_kernel_rfl

def callerData (compiler : Compiler) (old : Word) (tid : Fin 2) : Space :=
  if tid.val = 0 then mapUnchecked (counterData compiler old) ⟨0x700008, 8⟩ readWrite else
    mapUnchecked (freshCaller (counterData compiler old) 0x700008 0x654320) ⟨0x710008, 8⟩ readWrite

theorem caller_store (compiler : Compiler) (old : Word) (tid : Fin 2) :
    AddressSpace.storeQWord (callerData compiler old tid) (stack tid) (returnAddress tid) =
      .ok (writeQWordCells (callerData compiler old tid) (stack tid) (returnAddress tid)) := by
  apply AddressSpace.storeQWord_success
  rcases tid with ⟨tid, bound⟩
  have choices : tid = 0 ∨ tid = 1 := by omega
  rcases choices with rfl | rfl <;> cases compiler <;> fetch_add_kernel_rfl

theorem caller_bytes (compiler : Compiler) (old : Word) (tid : Fin 2) :
    MemoryAgreesOn (toMemory (spaceView compiler old))
      (toMemory (writeQWordCells (callerData compiler old tid) (stack tid) (returnAddress tid))) (stack tid) 8 := by
  intro index bound
  rcases tid with ⟨tid, extent⟩
  have choices : tid = 0 ∨ tid = 1 := by omega
  rcases choices with rfl | rfl
  · have small : index < 2^64 := by omega
    have total : (0x700008 : Word).toNat + index < 2^64 := by change 7340040 + index < 2^64; omega
    have outside : ¬ (⟨0x710008, 8⟩ : Region).Contains (0x700008 + BitVec.ofNat 64 index) := by
      simp only [Region.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
      change ¬ (7405576 ≤ 7340040 + index ∧ 7340040 + index < 7405576 + 8)
      omega
    change (toMemory (spaceView compiler old)).read (0x700008 + BitVec.ofNat 64 index) = _
    unfold spaceView
    rw [freshCaller_frame _ _ _ _ outside]
    exact freshCaller_read _ _ _ _
  · exact freshCaller_read _ _ _ _

theorem caller_read (compiler : Compiler) (old : Word) (tid : Fin 2) :
    loadQWord (toMemory (spaceView compiler old)) (stack tid) = .ok (returnAddress tid) := by
  rw [loadQWord_congr _ _ _ (caller_bytes compiler old tid)]
  exact (AddressSpace.storeQWord_sound _ _ _ _ (caller_store compiler old tid)).2.1

theorem worker_caller (compiler : Compiler) (old deltaA deltaB : Word) (tid : Fin 2) :
    Borrowing.loadWord64 (current compiler old deltaA deltaB).state.world.legacy.shared
      (worker compiler old deltaA deltaB tid).resources.actor
      (worker compiler old deltaA deltaB tid).resources.caller.identifier
      (worker compiler old deltaA deltaB tid).resources.callerAddress = .ok (returnAddress tid) := by
  have valid := (current compiler old deltaA deltaB).valid.2
    (worker compiler old deltaA deltaB tid) (List.mem_of_getElem? (worker_live compiler old deltaA deltaB tid))
  have lease := valid.1.2.1
  have authorized : Borrowing.authorize
      (current compiler old deltaA deltaB).state.world.legacy.shared
      (worker compiler old deltaA deltaB tid).resources.actor
      (worker compiler old deltaA deltaB tid).resources.caller.identifier =
      .ok (worker compiler old deltaA deltaB tid).resources.caller.loan := by
    simp only [Borrowing.authorize, lease.1, lease.2.1, ite_true]
  have fits : Borrowing.Subregion
      (qwordRegion (worker compiler old deltaA deltaB tid).resources.callerAddress)
      (worker compiler old deltaA deltaB tid).resources.caller.loan.region := by
    rw [valid.1.2.2.1]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  apply Borrowing.loadWord64_success _ _ _ _ _ _ authorized fits
  change loadQWord (published (current compiler old deltaA deltaB).state.world)
    (worker compiler old deltaA deltaB tid).resources.callerAddress = .ok (returnAddress tid)
  rw [memory, worker_view]
  exact caller_read compiler old tid

/-- Symbolic two-context nonvacuity: arbitrary old and both full64 inputs,
shared one live counter, distinct current handles and private original callers.
This checks current resources/ABI, not a desired execution result. -/
theorem gate (compiler : Compiler) (old deltaA deltaB : Word) (tid : Fin 2) (id : Id) :
    FetchAddABI64.gate (image compiler) (current compiler old deltaA deltaB)
      id tid.val (delta deltaA deltaB tid) = true := by
  have currentCode : X86.checkCode (published (current compiler old deltaA deltaB).state.world)
      (image compiler).base (image compiler).bytes = true :=
    X86.checkCode_complete _ _ _ (code compiler old deltaA deltaB)
  simp only [FetchAddABI64.gate, worker_live, FetchAddABI64.workerGate,
    decide_eq_true (worker_present compiler old deltaA deltaB tid),
    decide_eq_true (worker_abi compiler old deltaA deltaB tid),
    currentCode, worker_selection, worker_caller]
  rcases tid with ⟨tid, bound⟩
  have choices : tid = 0 ∨ tid = 1 := by omega
  rcases choices with rfl | rfl <;> fetch_add_kernel_rfl

theorem private_callers (compiler : Compiler) (old deltaA deltaB : Word) :
    Ownership.Disjoint
      (worker compiler old deltaA deltaB 0).resources.caller.loan.region
      (worker compiler old deltaA deltaB 1).resources.caller.loan.region ∧
    (worker compiler old deltaA deltaB 0).resources.actor ≠
      (worker compiler old deltaA deltaB 1).resources.actor ∧
    (worker compiler old deltaA deltaB 0).resources.atomics = [⟨0⟩] ∧
    (worker compiler old deltaA deltaB 1).resources.atomics = [⟨1⟩] := by
  rw [worker_view, worker_view]
  change Ownership.Disjoint ⟨0x700008, 8⟩ ⟨0x710008, 8⟩ ∧
    11 ≠ 12 ∧ ([⟨0⟩] : List Atomics64.HandleId64) = [⟨0⟩] ∧
    ([⟨1⟩] : List Atomics64.HandleId64) = [⟨1⟩]
  decide +kernel

end EDSL.Corpus.V1.FetchAddResources
