/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO.Effects
import EDSL.OS.TSO.Trace

namespace EDSL.OS.TSO
open X86

/-- Pending writes satisfy the same aligned ordinary-RAM and fixed-code
profile as retiring stores, against the current full shared memory. -/
def StoreValid (memory : Memory) (store : StoreBuffer.Store) : Prop :=
  atomicAddressable store.address = true ∧
    canStoreDWord memory store.address = true ∧ dataOnly memory store.address = true

def BuffersValid (state : State) : Prop :=
  ∀ worker ∈ state.workers, ∀ store ∈ worker.buffer, StoreValid state.memory store

theorem StoreValid.write {memory : Memory} {store : StoreBuffer.Store}
    (valid : StoreValid memory store) (address : Word) (value : BitVec 32) :
    StoreValid (writeDWordUnchecked memory address value) store :=
  ⟨valid.1, StoreBuffer.write_canStore _ _ _ _ valid.2.1, valid.2.2⟩

private theorem BuffersValid.install {state : State} (valid : BuffersValid state)
    (identifier : Nat) (memory : Memory) (context : Threads.Context) (returned : Bool)
    (buffer : StoreBuffer.Buffer)
    (preserved : ∀ store, StoreValid state.memory store → StoreValid memory store)
    (pending : ∀ store ∈ buffer, StoreValid memory store) :
    BuffersValid (install state identifier memory context returned buffer) := by
  intro worker member store queued
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact preserved store (valid worker old store queued)
  · exact pending store queued

theorem BuffersValid.initial (state : MachineThreads.State) : BuffersValid (initial state) := by
  intro worker member store queued
  obtain ⟨before, _, rfl⟩ := List.mem_map.mp member
  simp at queued

theorem BuffersValid.execute {state : State} {identifier : Nat} {worker : Worker}
    {instruction : Instruction} {result : State × Observation}
    (valid : BuffersValid state) (live : state.workers[identifier]? = some worker)
    (success : execute state identifier worker instruction = .ok result) :
    BuffersValid result.1 := by
  have pending := valid worker (List.mem_of_getElem? live)
  cases execute_effect _ _ _ _ _ success with
  | queued found aligned data executed writable exactOutput =>
    apply valid.install identifier state.memory _ false _ (fun _ valid => valid)
    intro store member
    rcases List.mem_append.mp member with old | newest
    · exact pending store old
    · have same := List.mem_singleton.mp newest
      subst store
      exact ⟨aligned, writable, data⟩
  | ordinary found unlocked loads executed memory =>
    exact valid.install identifier state.memory _ false _ (fun _ valid => valid) pending
  | returned found unlocked instructionEq executed memory =>
    exact valid.install identifier state.memory _ true _ (fun _ valid => valid) pending
  | atomic found classified empty data executed transition address accumulator =>
    apply valid.install identifier _ _ false []
    · intro store validStore
      rw [transition.2.2.2]
      exact validStore.write _ _
    · intro store member
      simp at member
  | blocked found classified nonempty => exact valid

theorem BuffersValid.issue {state : State} {identifier : Nat} {result : State × Observation}
    (valid : BuffersValid state) (success : issue state identifier = .ok result) :
    BuffersValid result.1 := by
  obtain ⟨worker, instruction, live, _, _, executed, _⟩ := issue_effect _ _ _ success
  exact valid.execute live executed

theorem BuffersValid.drain {state : State} {identifier : Nat} {result : State × Observation}
    (valid : BuffersValid state) (success : drain state identifier = .ok result) :
    BuffersValid result.1 := by
  obtain ⟨worker, head, tail, memory, live, buffer, committed, same⟩ := drain_ok _ _ _ success
  have written : memory = writeDWordUnchecked state.memory head.address head.value := by
    unfold storeDWord at committed
    split at committed
    · exact (Except.ok.inj committed).symm
    · cases committed
  rw [same, written]
  apply valid.install identifier _ _ _ tail
  · intro store validStore
    exact validStore.write _ _
  · intro store member
    have queued : store ∈ worker.buffer := by
      rw [buffer]
      exact List.mem_cons_of_mem head member
    exact (valid worker (List.mem_of_getElem? live) store queued).write _ _

theorem BuffersValid.step {state : State} {action : Action} {result : State × Observation}
    (valid : BuffersValid state) (success : step state action = .ok result) :
    BuffersValid result.1 := by
  cases action with
  | issue identifier => exact valid.issue success
  | drain identifier => exact valid.drain success

theorem BuffersValid.schedule {state : State} {actions : List Action}
    {result : State × List Observation} (valid : BuffersValid state)
    (success : schedule state actions = .ok result) : BuffersValid result.1 := by
  induction actions generalizing state result with
  | nil => simp only [TSO.schedule, Except.ok.injEq] at success; cases success; exact valid
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact ih (result := tail) (valid.step first) following

theorem BuffersValid.trace {before after : State} {actions : List Action}
    {observations : List Observation} (valid : BuffersValid before)
    (trace : Trace before actions observations after) : BuffersValid after :=
  valid.schedule trace.schedule

theorem initial_schedule_buffers {state : MachineThreads.State} {actions : List Action}
    {result : State × List Observation} (success : schedule (initial state) actions = .ok result) :
    BuffersValid result.1 :=
  (BuffersValid.initial state).schedule success

/-- Execute and write permissions are immutable for every successful step,
even when the starting queues do not satisfy the queue invariant. -/
theorem execute_permissions {state : State} {identifier : Nat} {worker : Worker}
    {instruction : Instruction} {result : State × Observation}
    (success : execute state identifier worker instruction = .ok result) :
    result.1.memory.executable = state.memory.executable ∧
      result.1.memory.writable = state.memory.writable := by
  cases execute_effect _ _ _ _ _ success with
  | queued | ordinary | returned | blocked => exact ⟨rfl, rfl⟩
  | atomic _ _ _ _ _ transition _ _ => exact transition.permissions

theorem issue_permissions {state : State} {identifier : Nat} {result : State × Observation}
    (success : issue state identifier = .ok result) :
    result.1.memory.executable = state.memory.executable ∧
      result.1.memory.writable = state.memory.writable := by
  obtain ⟨_, _, _, _, _, executed, _⟩ := issue_effect _ _ _ success
  exact execute_permissions executed

theorem drain_permissions {state : State} {identifier : Nat} {result : State × Observation}
    (success : drain state identifier = .ok result) :
    result.1.memory.executable = state.memory.executable ∧
      result.1.memory.writable = state.memory.writable := by
  obtain ⟨_, _, _, _, _, _, written, _⟩ := drain_memory _ _ _ success
  rw [written]
  exact ⟨rfl, rfl⟩

theorem step_permissions {state : State} {action : Action} {result : State × Observation}
    (success : step state action = .ok result) :
    result.1.memory.executable = state.memory.executable ∧
      result.1.memory.writable = state.memory.writable := by
  cases action with
  | issue identifier => exact issue_permissions success
  | drain identifier => exact drain_permissions success

theorem schedule_permissions {state : State} {actions : List Action}
    {result : State × List Observation} (success : schedule state actions = .ok result) :
    result.1.memory.executable = state.memory.executable ∧
      result.1.memory.writable = state.memory.writable := by
  induction actions generalizing state result with
  | nil => simp only [schedule, Except.ok.injEq] at success; cases success; exact ⟨rfl, rfl⟩
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok _ _ _ _ success
    have headFrame := step_permissions first
    have tailFrame := ih following
    rw [same]
    exact ⟨tailFrame.1.trans headFrame.1, tailFrame.2.trans headFrame.2⟩

/-- A non-executable four-byte destination is disjoint from every executable
byte, including modular footprints in the high canonical address half. -/
theorem dataOnly_outside {memory : Memory} {address query : Word}
    (data : dataOnly memory address = true) (code : memory.executable query = true) :
    4 ≤ (query - address).toNat := by
  have disabled : ((memory.executable address = false ∧
      memory.executable (address + 1) = false) ∧ memory.executable (address + 2) = false) ∧
      memory.executable (address + 3) = false := by
    simpa only [dataOnly, Bool.not_eq_true', Bool.or_eq_false_iff] using data
  simp only [BitVec.ofNat_eq_ofNat] at disabled
  by_cases outside : 4 ≤ (query - address).toNat
  · exact outside
  exfalso
  have offsets : (query - address).toNat = 0 ∨ (query - address).toNat = 1 ∨
      (query - address).toNat = 2 ∨ (query - address).toNat = 3 := by omega
  rcases offsets with offset | offset | offset | offset
  · have same := StoreBuffer.query_of_offset address query 0 (by decide) offset
    simp only [BitVec.add_zero] at same
    rw [same, disabled.1.1.1] at code
    cases code
  · have same := StoreBuffer.query_of_offset address query 1 (by decide) offset
    rw [same, disabled.1.1.2] at code
    cases code
  · have same := StoreBuffer.query_of_offset address query 2 (by decide) offset
    rw [same, disabled.1.2] at code
    cases code
  · have same := StoreBuffer.query_of_offset address query 3 (by decide) offset
    rw [same, disabled.2] at code
    cases code

/-- Shared data values may change. Permission functions, accessible-byte
domains, and all bytes marked executable in the input remain identical. -/
structure MemoryFrame (before after : Memory) : Prop where
  executable : after.executable = before.executable
  writable : after.writable = before.writable
  readable : ∀ query, (after.read query).isSome = (before.read query).isSome
  code : ∀ query, before.executable query = true → after.read query = before.read query

theorem MemoryFrame.refl (memory : Memory) : MemoryFrame memory memory :=
  ⟨rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem MemoryFrame.trans {before middle after : Memory}
    (first : MemoryFrame before middle) (second : MemoryFrame middle after) :
    MemoryFrame before after := by
  refine ⟨second.executable.trans first.executable, second.writable.trans first.writable,
    fun query => (second.readable query).trans (first.readable query), ?_⟩
  intro query code
  exact (second.code query (by rw [first.executable]; exact code)).trans (first.code query code)

theorem MemoryFrame.write (memory : Memory) (address : Word) (value : BitVec 32)
    (allowed : canStoreDWord memory address = true) (data : dataOnly memory address = true) :
    MemoryFrame memory (writeDWordUnchecked memory address value) :=
  ⟨rfl, rfl, fun query => StoreBuffer.write_read_isSome memory address query value allowed,
    fun query code => writeDWord_frame memory address query value (dataOnly_outside data code)⟩

theorem MemoryFrame.view (memory : Memory) (buffer : StoreBuffer.Buffer)
    (pending : ∀ store ∈ buffer, StoreValid memory store) :
    MemoryFrame memory (StoreBuffer.view memory buffer) := by
  refine ⟨StoreBuffer.view_executable _ _, StoreBuffer.view_writable _ _,
    fun query => StoreBuffer.view_read_isSome memory buffer query
      (fun store member => (pending store member).2.1), ?_⟩
  intro query code
  exact StoreBuffer.view_frame _ _ _
    (fun store member => dataOnly_outside (pending store member).2.2 code)

theorem MemoryFrame.canStore {before after : Memory} (frame : MemoryFrame before after)
    (address : Word) : canStoreDWord after address = canStoreDWord before address := by
  simp only [canStoreDWord, dwordWritable, frame.writable, frame.readable]

theorem MemoryFrame.fetch {before after : Memory} (frame : MemoryFrame before after)
    (address : Word) : fetchByte after address = fetchByte before address := by
  cases permission : before.executable address with
  | false => simp [fetchByte, frame.executable, permission]
  | true => simp [fetchByte, frame.executable, permission, frame.code address permission]

theorem MemoryFrame.codeAt {before after : Memory} (frame : MemoryFrame before after)
    {base : Word} {bytes : List Byte} (code : CodeAt before base bytes) : CodeAt after base bytes :=
  ⟨code.1, fun offset byte found => (frame.fetch _).trans (code.2 offset byte found)⟩

theorem BuffersValid.local_frame {state : State} (valid : BuffersValid state)
    {worker : Worker} (live : worker ∈ state.workers) :
    MemoryFrame state.memory (localState state worker).memory :=
  MemoryFrame.view _ _ (valid worker live)

theorem execute_memory_frame {state : State} {identifier : Nat} {worker : Worker}
    {instruction : Instruction} {result : State × Observation}
    (success : execute state identifier worker instruction = .ok result) :
    MemoryFrame state.memory result.1.memory := by
  cases execute_effect _ _ _ _ _ success with
  | queued | ordinary | returned | blocked => exact .refl _
  | atomic _ _ _ data _ transition address _ =>
    change MemoryFrame state.memory _
    rw [transition.2.2.2]
    exact .write _ _ _ transition.2.1 (by rw [address]; exact data)

theorem issue_memory_frame {state : State} {identifier : Nat} {result : State × Observation}
    (success : issue state identifier = .ok result) : MemoryFrame state.memory result.1.memory := by
  obtain ⟨_, _, _, _, _, executed, _⟩ := issue_effect _ _ _ success
  exact execute_memory_frame executed

theorem drain_memory_frame {state : State} {identifier : Nat} {result : State × Observation}
    (valid : BuffersValid state) (success : drain state identifier = .ok result) :
    MemoryFrame state.memory result.1.memory := by
  obtain ⟨worker, head, tail, live, buffer, allowed, written, _⟩ := drain_memory _ _ _ success
  have headValid := valid worker (List.mem_of_getElem? live) head
    (by rw [buffer]; exact List.mem_cons_self)
  rw [written]
  exact .write _ _ _ allowed headValid.2.2

theorem step_memory_frame {state : State} {action : Action} {result : State × Observation}
    (valid : BuffersValid state) (success : step state action = .ok result) :
    MemoryFrame state.memory result.1.memory := by
  cases action with
  | issue identifier => exact issue_memory_frame success
  | drain identifier => exact drain_memory_frame valid success

theorem schedule_memory_frame {state : State} {actions : List Action}
    {result : State × List Observation} (valid : BuffersValid state)
    (success : schedule state actions = .ok result) : MemoryFrame state.memory result.1.memory := by
  induction actions generalizing state result with
  | nil => simp only [schedule, Except.ok.injEq] at success; cases success; exact .refl _
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact (step_memory_frame valid first).trans (ih (result := tail) (valid.step first) following)

theorem Trace.memory_frame {before after : State} {actions : List Action}
    {observations : List Observation} (trace : Trace before actions observations after)
    (valid : BuffersValid before) : MemoryFrame before.memory after.memory :=
  schedule_memory_frame valid trace.schedule

/-- Code preservation follows from the initial empty queues and actual
successful scheduling; it needs no expected instruction or final-state gate. -/
theorem initial_schedule_code {state : MachineThreads.State} {actions : List Action}
    {result : State × List Observation} {base : Word} {bytes : List Byte}
    (code : CodeAt state.memory base bytes)
    (success : schedule (initial state) actions = .ok result) : CodeAt result.1.memory base bytes :=
  (schedule_memory_frame (BuffersValid.initial state) success).codeAt code

end EDSL.OS.TSO

#audit_edsl
