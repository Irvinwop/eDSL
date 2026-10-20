/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Invariant

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

/-- Inversion of checked cohort creation, retaining both real loan operations
and the machine code, operand, and return-stack gates. -/
theorem spawn_ok (state : State) (start : Start) (after : State)
    (success : spawn state start = .ok after) :
    started state = false ∧ ∃ record target code stack,
      Mutex.registered state.shared = .ok record ∧ record.config.owner = 0 ∧
      record.holder = none ∧
      start.entry.registers .rdi = record.config.lockAddress ∧
      start.entry.registers .rsi = record.config.dataAddress ∧
      checkCode (toMemory state.shared.shared.resources.space) start.entry.rip bytes = true ∧
      readWord (toMemory state.shared.shared.resources.space) (start.entry.registers .rsp) = .ok target ∧
      canonical target = true ∧
      Mutex.readBorrow state.shared 0 start.codeTicket
        (principal state.workers.length) (codeRegion start.entry) = .ok code ∧
      Mutex.readBorrow code.1 0 start.stackTicket
        (principal state.workers.length) (Threads.stackRegion start.entry) = .ok stack ∧
      after = ⟨stack.1, state.workers ++ [⟨start.entry, target, code.2, stack.2,
        start.entry, .entry, none⟩]⟩ := by
  by_cases running : started state = true
  · simp [spawn, running] at success
  · have stopped : started state = false := by cases h : started state <;> simp_all
    refine ⟨stopped, ?_⟩
    cases registered : Mutex.registered state.shared with
    | error fault => simp [spawn, running, registered, Except.mapError] at success
    | ok record =>
      by_cases owner : record.config.owner = 0
      · by_cases held : record.holder.isSome = true
        · simp [spawn, running, registered, owner, held, Except.mapError] at success
        · have free : record.holder = none := by cases h : record.holder <;> simp_all
          by_cases operands : start.entry.registers .rdi ≠ record.config.lockAddress ∨
              start.entry.registers .rsi ≠ record.config.dataAddress
          · simp [spawn, running, registered, owner, held, operands, Except.mapError] at success
          · have addresses : start.entry.registers .rdi = record.config.lockAddress ∧
                start.entry.registers .rsi = record.config.dataAddress := by simpa using operands
            by_cases executable : checkCode (toMemory state.shared.shared.resources.space) start.entry.rip bytes = true
            · cases target : readWord (toMemory state.shared.shared.resources.space) (start.entry.registers .rsp) with
              | error fault => simp [spawn, running, registered, owner, held, operands, executable, target, Except.mapError] at success
              | ok address =>
                by_cases canonical : X86.canonical address = true
                · cases code : Mutex.readBorrow state.shared 0 start.codeTicket
                      (principal state.workers.length) (codeRegion start.entry) with
                  | error fault => simp [spawn, running, registered, owner, held, operands, executable, target, canonical, code, Except.mapError] at success
                  | ok first =>
                    cases stack : Mutex.readBorrow first.1 0 start.stackTicket
                        (principal state.workers.length) (Threads.stackRegion start.entry) with
                    | error fault => simp [spawn, running, registered, owner, held, operands, executable, target, canonical, code, stack, Except.mapError] at success
                    | ok second =>
                      simp [spawn, running, registered, owner, held, operands, executable, target, canonical, code, stack, Except.mapError] at success
                      exact ⟨record, address, first, second, rfl, owner, free,
                        addresses.1, addresses.2, executable, rfl, canonical, rfl, stack, success.symm⟩
                · simp [spawn, running, registered, owner, held, operands, executable, target, canonical, Except.mapError] at success
            · simp [spawn, running, registered, owner, held, operands, executable, Except.mapError] at success
      · simp [spawn, running, registered, owner, Except.mapError] at success

theorem started_entry (state : State) (stopped : started state = false) :
    ∀ worker ∈ state.workers, worker.phase = .entry := by
  simpa [started] using stopped

private theorem readBorrow_frame {before : Mutex.State} {lender borrower : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Mutex.State × Nat}
    (success : Mutex.readBorrow before lender ticket borrower region = .ok result) :
    result.1.shared.resources = before.shared.resources ∧ result.1.mutex = before.mutex := by
  obtain ⟨_, shared, borrowed, same⟩ := Mutex.readBorrow_ok _ _ _ _ _ _ success
  rw [same]
  exact ⟨Threads.readBorrow_resources borrowed, rfl⟩

/-- Borrowing issues authority without changing the resource world or the
registered record, including its current holder and invariant function. -/
theorem spawn_resources (state : State) (start : Start) (after : State)
    (success : spawn state start = .ok after) :
    after.shared.shared.resources = state.shared.shared.resources ∧
      after.shared.mutex = state.shared.mutex := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, code, stack, same⟩ := spawn_ok _ _ _ success
  have first := readBorrow_frame code
  have second := readBorrow_frame stack
  rw [same]
  exact ⟨second.1.trans first.1, second.2.trans first.2⟩

theorem spawn_space (state : State) (start : Start) (after : State)
    (success : spawn state start = .ok after) :
    after.shared.shared.resources.space = state.shared.shared.resources.space :=
  congrArg Ownership.World.space (spawn_resources _ _ _ success).1

theorem spawn_registered (state : State) (start : Start) (after : State) (config : Mutex.Config)
    (registered : Registered state.shared config) (success : spawn state start = .ok after) :
    Registered after.shared config := by
  obtain ⟨record, present, same⟩ := registered
  exact ⟨record, (spawn_resources _ _ _ success).2.trans present, same⟩

theorem spawn_entry (state : State) (start : Start) (after : State)
    (success : spawn state start = .ok after) :
    ∀ worker ∈ after.workers, worker.phase = .entry := by
  obtain ⟨stopped, _, _, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := spawn_ok _ _ _ success
  rw [same]
  intro worker member
  rcases List.mem_append.mp member with old | new
  · exact started_entry state stopped worker old
  · have equal := List.mem_singleton.mp new
    subst worker
    rfl

theorem spawn_length (state : State) (start : Start) (after : State)
    (success : spawn state start = .ok after) : after.workers.length = state.workers.length + 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := spawn_ok _ _ _ success
  simp [same]

/-- Worker identities remain their original list indices when a new entry
worker is appended. -/
theorem spawn_keeps (state : State) (start : Start) (after : State)
    (success : spawn state start = .ok after) (identifier : Nat) (worker : Worker)
    (live : state.workers[identifier]? = some worker) : after.workers[identifier]? = some worker := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := spawn_ok _ _ _ success
  have below : identifier < state.workers.length := (List.getElem?_eq_some_iff.mp live).1
  simpa only [same, List.getElem?_append_left below] using live

theorem spawn_free (state : State) (start : Start) (after : State)
    (success : spawn state start = .ok after) :
    ∀ record, after.shared.mutex = some record → record.holder = none := by
  obtain ⟨_, original, _, _, _, registered, _, free, _⟩ := spawn_ok _ _ _ success
  have present := Mutex.registered_ok _ _ registered
  intro record live
  have equal := Option.some.inj (live.symm.trans ((spawn_resources _ _ _ success).2.trans present))
  exact (congrArg Mutex.Registered.holder equal).trans free

theorem spawn_tracked (state : State) (start : Start) (after : State)
    (success : spawn state start = .ok after) : Tracked after := by
  intro record lease present held
  rw [spawn_free _ _ _ success record present] at held
  cases held

/-- The empty cohort may start from a registered, free mutex. Registration
and mutex well-formedness are environmental premises, not created by empty. -/
theorem empty_invariant (shared : Mutex.State) (config : Mutex.Config)
    (valid : Mutex.WellFormed shared) (registered : Registered shared config)
    (free : ∀ record, shared.mutex = some record → record.holder = none) :
    Invariant config (empty shared) := by
  refine ⟨valid, registered, ?_, ?_⟩
  · intro identifier worker live
    simp [empty] at live
  · intro record lease present held
    rw [free record present] at held
    cases held

/-- Successful checked spawn establishes the new worker's entry invariant
and preserves every old entry worker; no resulting-invariant check is used. -/
theorem spawn_invariant (state : State) (start : Start) (after : State) (config : Mutex.Config)
    (valid : Invariant config state) (success : spawn state start = .ok after) :
    Invariant config after := by
  refine ⟨spawn_wellFormed _ _ _ valid.shared success,
    spawn_registered _ _ _ _ valid.registered success, ?_, spawn_tracked _ _ _ success⟩
  obtain ⟨stopped, record, target, code, stack, registered, _, _, rdi, rsi, _, _, _, _, _, same⟩ :=
    spawn_ok _ _ _ success
  obtain ⟨original, present, configEq⟩ := valid.registered
  have recordEq := Option.some.inj ((Mutex.registered_ok _ _ registered).symm.trans present)
  have registeredConfig : record.config = config := (congrArg Mutex.Registered.config recordEq).trans configEq
  rw [same]
  intro identifier worker live
  by_cases old : identifier < state.workers.length
  · have oldLive : state.workers[identifier]? = some worker := by
      simpa only [List.getElem?_append_left old] using live
    have invariant := valid.workers identifier worker oldLive
    have phase := started_entry state stopped worker (List.mem_of_getElem? oldLive)
    have guard : worker.guard = none := by simpa [Control, phase] using invariant.control
    refine ⟨invariant.context, invariant.operands, invariant.control, ?_, ?_⟩
    · intro lease held; rw [guard] at held; cases held
    · intro lease held; rw [guard] at held; cases held
  · have tail := List.getElem?_append_right (Nat.le_of_not_gt old) (l₂ := [
        ⟨start.entry, target, code.2, stack.2, start.entry, .entry, none⟩])
    simp only [tail] at live
    cases index : identifier - state.workers.length with
    | zero =>
      simp [index] at live
      subst worker
      refine ⟨?_, ?_, rfl, ?_, ?_⟩
      · simp [contextValid, Phase.offset]
      · exact ⟨rdi.trans (congrArg Mutex.Config.lockAddress registeredConfig),
          rsi.trans (congrArg Mutex.Config.dataAddress registeredConfig)⟩
      · intro lease held; cases held
      · intro lease held; cases held
    | succ index => simp [index] at live

theorem spawn_credits (state : State) (start : Start) (after : State)
    (success : spawn state start = .ok after) : credits after = credits state := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := spawn_ok _ _ _ success
  simp [same, credits, credit, List.map_append, List.sum_append]

theorem spawn_accounted (state : State) (start : Start) (after : State)
    (config : Mutex.Config) (initial : BitVec 32) (accounted : Accounted config initial state)
    (success : spawn state start = .ok after) : Accounted config initial after := by
  simpa only [Accounted, spawn_space _ _ _ success, spawn_credits _ _ _ success] using accounted

/-- A successful spawn from empty yields one actual entry worker and a
globally valid cohort, without assuming any invariant of the result. -/
theorem spawn_empty_positive (shared : Mutex.State) (start : Start) (after : State) (config : Mutex.Config)
    (valid : Mutex.WellFormed shared) (registered : Registered shared config)
    (success : spawn (empty shared) start = .ok after) :
    Invariant config after ∧ after.workers.length = 1 ∧ credits after = 0 := by
  have free : ∀ record, shared.mutex = some record → record.holder = none := by
    intro record present
    apply spawn_free (empty shared) start after success record
    exact (spawn_resources _ _ _ success).2.trans present
  refine ⟨spawn_invariant _ _ _ _ (empty_invariant _ _ valid registered free) success, ?_, ?_⟩
  · simpa [empty] using spawn_length _ _ _ success
  · simpa [credits, empty] using spawn_credits _ _ _ success

end EDSL.OS.MutexReplay
