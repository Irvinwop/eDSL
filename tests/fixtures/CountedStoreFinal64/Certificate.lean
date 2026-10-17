/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CountedStoreFinal64.Invariant
import tests.fixtures.CountedStoreFinal64.Support

set_option warningAsError true

namespace EDSL.CountedStoreFinal64
open EDSL X86 X86.Sequential OS Grading.Trace CountedStore64

/-- The loop retains the old target. Only the positive exit goes through STORE;
the zero entry path goes directly to RET. -/
inductive Interior (input : Input) (initial : State) : Node → Nat → Node → State → Prop where
  | entry : Interior input initial .entry (input.count.toNat + 1) .entry initial
  | test : Interior input initial .entry (input.count.toNat + 1) .test (move initial)
  | guard (af : Bool) :
      Interior input initial .entry (input.count.toNat + 1) .guard (CountedStoreFinal64.test (move initial) af)
  | increment {state} (header : Header input initial state) :
      Interior input initial .increment (state.registers .rdx).toNat .increment state
  | decrement {state} (header : Header input initial state) :
      Interior input initial .increment (state.registers .rdx).toNat .decrement (incState state)
  | back {state} (header : Header input initial state) :
      Interior input initial .increment (state.registers .rdx).toNat .back (decState state)
  | store {source budget state} (ready : Ready input initial state) :
      Interior input initial source budget .store state
  | ret {source budget state} (exit : Exit input initial state) :
      Interior input initial source budget .ret state

def rank (node : Node) (state : State) : Nat :=
  (state.registers .rdx).toNat + if node = .entry then 1 else 0

def Inv {Ghost : Type} (rules : Rules Ghost) (input : Input) (initial : State)
    (node : Node) (shared : Ghost) (state : State) : Prop :=
  rules.Current shared state ∧ match node with
    | .entry => state = initial
    | .increment => Nonempty (Header input initial state)
    | _ => False

theorem interior_frame {input initial source budget node state}
    (pre : Pre bytes input initial) (inside : Interior input initial source budget node state) :
    Frame input initial state := by
  cases inside with
  | entry => exact Frame.initial pre
  | test => exact (Frame.initial pre).move
  | guard af => exact ((Frame.initial pre).move).test af
  | increment h => exact h.frame
  | decrement h => exact incState_frame h
  | back h => exact decState_frame h
  | store ready => exact ready.frame
  | ret exit => exact exit.frame

theorem interior_pc {input initial source budget node state}
    (inside : Interior input initial source budget node state) :
    state.rip = initial.rip + BitVec.ofNat 64 (offset node) := by
  cases inside with
  | entry => simp [offset]
  | test => rfl
  | guard af => simp only [GCC.test, GCC.move, BitVec.add_assoc]; rfl
  | increment h => exact h.pc
  | decrement h => simp only [incState, GCC.increment, h.pc, BitVec.add_assoc]; rfl
  | back h => simp only [decState, incState, GCC.decrement, GCC.increment, h.pc,
      BitVec.add_assoc]; rfl
  | store ready => exact ready.pc
  | ret exit => exact exit.pc

/-- The complete local resource obligation, shared by the small checked steps. -/
def VC {Ghost : Type} (rules : Rules Ghost) (input : Input) (initial : State)
    (source : Node) (budget : Nat) (node : Node) (shared : Ghost) (state : State) : Prop :=
  rules.Current shared state ∧
    ∃ instruction, Sequential.decodeAt state = .ok instruction ∧
      ∀ af, ∃ observation evolved,
        step af state = .ok observation ∧
        (∀ read ∈ observation.reads,
          rules.ReadAllowed shared state read ∧ OperandReadSucceeds state read) ∧
        rules.Effect shared state instruction observation evolved ∧
        match observation.result with
        | .returned final => rules.Current evolved final ∧ Post input initial final
        | .next middle => ∃ dest, flow.Edge node dest ∧
            ((flow.cutpoint dest = true ∧ Inv rules input initial dest evolved middle ∧
                rank dest middle < budget) ∨
             (flow.cutpoint dest = false ∧ rules.Current evolved middle ∧
                Interior input initial source budget dest middle))
        | .atomic _ _ | .syscall _ => False

theorem vc_entry {Ghost : Type} {rules : Rules Ghost} {input initial}
    (pre : Pre bytes input initial) (support : Support input initial rules)
    {shared} (current : rules.Current shared initial) :
    VC rules input initial .entry (input.count.toNat + 1) .entry shared initial := by
  have inside : Interior input initial .entry (input.count.toNat + 1) .entry initial := Interior.entry
  have frame := interior_frame pre inside
  have pc := interior_pc inside
  have decoded := decode frame.code .entry pc
  have fetch := fetch_at frame.code .entry pc
  refine ⟨current, instruction .entry, decoded, ?_⟩
  intro af
  have actual := (step_eq_execute af decoded).trans (execute_move initial af)
  exact ⟨⟨.next (move initial), []⟩, shared, actual, by simp,
    support.readOnly shared _ _ _ rfl fetch, .test, Edge.entry,
    Or.inr ⟨rfl, support.sameMemory current rfl, Interior.test⟩⟩

theorem vc_test {Ghost : Type} {rules : Rules Ghost} {input initial}
    (pre : Pre bytes input initial) (support : Support input initial rules)
    {shared} (current : rules.Current shared (move initial)) :
    VC rules input initial .entry (input.count.toNat + 1) .test shared (move initial) := by
  have inside : Interior input initial .entry (input.count.toNat + 1) .test (move initial) := Interior.test
  have frame := interior_frame pre inside
  have pc := interior_pc inside
  have decoded := decode frame.code .test pc
  have fetch := fetch_at frame.code .test pc
  refine ⟨current, instruction .test, decoded, ?_⟩
  intro af
  have actual := (step_eq_execute af decoded).trans (execute_test _ af)
  exact ⟨⟨.next (test (move initial) af), []⟩, shared, actual, by simp,
    support.readOnly shared _ _ _ rfl fetch, .guard, Edge.test,
    Or.inr ⟨rfl, support.sameMemory current rfl, Interior.guard af⟩⟩

theorem vc_guard {Ghost : Type} {rules : Rules Ghost} {input initial}
    (pre : Pre bytes input initial) (support : Support input initial rules)
    (prior : Bool) {shared} (current : rules.Current shared (test (move initial) prior)) :
    VC rules input initial .entry (input.count.toNat + 1) .guard shared (test (move initial) prior) := by
  have inside : Interior input initial .entry (input.count.toNat + 1) .guard (test (move initial) prior) := Interior.guard prior
  have frame := interior_frame pre inside
  have pc := interior_pc inside
  have decoded := decode frame.code .guard pc
  have fetch := fetch_at frame.code .guard pc
  refine ⟨current, instruction .guard, decoded, ?_⟩
  intro af
  by_cases zero : initial.registers .rdx = 0
  · have zf : (test (move initial) prior).flags.getLsbD 6 = true := by
      rw [tested_zero]
      simp only [GCC.move, State.writeRegister, reduceCtorEq, ite_false]
      rw [zero]; decide
    have actual := (step_eq_execute af decoded).trans (guard_exit frame.code pc zf af)
    exact ⟨⟨.next (exitState initial.rip (move initial) prior), []⟩, shared, actual, by simp,
      support.readOnly shared _ _ _ rfl fetch, .ret, Edge.exit,
      Or.inr ⟨rfl, support.sameMemory current rfl, Interior.ret (initialExit pre zero prior)⟩⟩
  · have zf : (test (move initial) prior).flags.getLsbD 6 = false := by
      rw [tested_zero]
      simp only [GCC.move, State.writeRegister, reduceCtorEq, ite_false,
        Bool.beq_eq_decide_eq, zero, decide_false]
    have actual := (step_eq_execute af decoded).trans (guard_body pc zf af)
    refine ⟨⟨.next (body initial.rip (move initial) prior), []⟩, shared, actual, by simp,
      support.readOnly shared _ _ _ rfl fetch, .increment, Edge.body,
      Or.inl ⟨rfl, ⟨support.sameMemory current rfl, ⟨initialHeader pre zero prior⟩⟩, ?_⟩⟩
    simp [rank, body, GCC.atPC, GCC.test, GCC.move, State.writeRegister, pre.count]

theorem vc_increment {Ghost : Type} {rules : Rules Ghost} {input initial}
    (pre : Pre bytes input initial) (support : Support input initial rules)
    {state} (h : Header input initial state) {shared} (current : rules.Current shared state) :
    VC rules input initial .increment (state.registers .rdx).toNat .increment shared state := by
  have inside : Interior input initial .increment (state.registers .rdx).toNat .increment state := Interior.increment h
  have frame := interior_frame pre inside
  have pc := interior_pc inside
  have decoded := decode frame.code .increment pc
  have fetch := fetch_at frame.code .increment pc
  refine ⟨current, instruction .increment, decoded, ?_⟩
  intro af
  have actual := (step_eq_execute af decoded).trans (execute_increment _ af)
  exact ⟨⟨.next (incState state), []⟩, shared, actual, by simp,
    support.readOnly shared _ _ _ rfl fetch, .decrement, Edge.increment,
    Or.inr ⟨rfl, support.sameMemory current rfl, Interior.decrement h⟩⟩

theorem vc_decrement {Ghost : Type} {rules : Rules Ghost} {input initial}
    (pre : Pre bytes input initial) (support : Support input initial rules)
    {before} (h : Header input initial before) {shared} (current : rules.Current shared (incState before)) :
    VC rules input initial .increment (before.registers .rdx).toNat .decrement shared (incState before) := by
  have inside : Interior input initial .increment (before.registers .rdx).toNat .decrement (incState before) := Interior.decrement h
  have frame := interior_frame pre inside
  have pc := interior_pc inside
  have decoded := decode frame.code .decrement pc
  have fetch := fetch_at frame.code .decrement pc
  refine ⟨current, instruction .decrement, decoded, ?_⟩
  intro af
  have actual := (step_eq_execute af decoded).trans (execute_decrement _ af)
  exact ⟨⟨.next (decState before), []⟩, shared, actual, by simp,
    support.readOnly shared _ _ _ rfl fetch, .back, Edge.decrement,
    Or.inr ⟨rfl, support.sameMemory current rfl, Interior.back h⟩⟩

theorem vc_back {Ghost : Type} {rules : Rules Ghost} {input initial}
    (pre : Pre bytes input initial) (support : Support input initial rules)
    {before} (h : Header input initial before) {shared} (current : rules.Current shared (decState before)) :
    VC rules input initial .increment (before.registers .rdx).toNat .back shared (decState before) := by
  have inside : Interior input initial .increment (before.registers .rdx).toNat .back (decState before) := Interior.back h
  have frame := interior_frame pre inside
  have pc := interior_pc inside
  have decoded := decode frame.code .back pc
  have fetch := fetch_at frame.code .back pc
  refine ⟨current, instruction .back, decoded, ?_⟩
  intro af
  by_cases zero : (decState before).registers .rdx = 0
  · have zf : (decState before).flags.getLsbD 6 = true := by
      rw [decState, decremented_zero]
      change ((decState before).registers .rdx == 0) = true
      rw [zero]; decide
    have actual := (step_eq_execute af decoded).trans (back_exit pc zf af)
    exact ⟨⟨.next (toStore initial.rip before), []⟩, shared, actual, by simp,
      support.readOnly shared _ _ _ rfl fetch, .store, Edge.finish,
      Or.inr ⟨rfl, support.sameMemory current rfl, Interior.store (nextReady pre h zero)⟩⟩
  · have zf : (decState before).flags.getLsbD 6 = false := by
      rw [decState, decremented_zero]
      change ((decState before).registers .rdx == 0) = false
      simp only [Bool.beq_eq_decide_eq, zero, decide_false]
    have actual := (step_eq_execute af decoded).trans (back_taken frame.code pc zf af)
    refine ⟨⟨.next (continued initial.rip before), []⟩, shared, actual, by simp,
      support.readOnly shared _ _ _ rfl fetch, .increment, Edge.back,
      Or.inl ⟨rfl, ⟨support.sameMemory current rfl, ⟨nextHeader pre h zero⟩⟩, ?_⟩⟩
    simpa only [rank, reduceCtorEq, ite_false, Nat.add_zero, continued, GCC.atPC] using rank_decreases h

theorem vc_store {Ghost : Type} {rules : Rules Ghost} {input initial}
    (pre : Pre bytes input initial) (support : Support input initial rules)
    {source budget state} (ready : Ready input initial state) {shared} (current : rules.Current shared state) :
    VC rules input initial source budget .store shared state := by
  have inside : Interior input initial source budget .store state := Interior.store ready
  have frame := interior_frame pre inside
  have pc := interior_pc inside
  have decoded := decode frame.code .store pc
  have fetch := fetch_at frame.code .store pc
  refine ⟨current, instruction .store, decoded, ?_⟩
  intro af
  have pointer := frame.pointer pre
  have writable : canStoreQWord state.memory (state.registers .rdi) = true := by
    rw [pointer]; exact frame.writable
  have actual := (step_eq_execute af decoded).trans (execute_store _ af writable)
  obtain ⟨evolved, evolvedCurrent, effect⟩ :=
    support.store shared _ current decoded pointer frame.writable fetch
  exact ⟨⟨.next (store state), []⟩, evolved, actual, by simp,
    effect, .ret, Edge.store, Or.inr ⟨rfl, evolvedCurrent, Interior.ret (storedExit pre ready)⟩⟩

theorem vc_ret {Ghost : Type} {rules : Rules Ghost} {input initial}
    (pre : Pre bytes input initial) (support : Support input initial rules)
    {source budget state} (exit : Exit input initial state) {shared} (current : rules.Current shared state) :
    VC rules input initial source budget .ret shared state := by
  have inside : Interior input initial source budget .ret state := Interior.ret exit
  have frame := interior_frame pre inside
  have pc := interior_pc inside
  have decoded := decode frame.code .ret pc
  have fetch := fetch_at frame.code .ret pc
  refine ⟨current, instruction .ret, decoded, ?_⟩
  intro af
  have stack : state.registers .rsp = initial.registers .rsp :=
    frame.registers .rsp (by decide) (by decide)
  have loaded : readWord state.memory (state.registers .rsp) = .ok input.returnAddress := by
    rw [stack]; exact frame.stackRead
  have actual := (step_eq_execute af decoded).trans (execute_ret loaded pre.memory.returnCanonical af)
  have reads := support.stack shared _ current stack frame.stackRead
  refine ⟨⟨.returned (finish state input.returnAddress), [⟨.stack, initial.registers .rsp, 8⟩]⟩,
    shared, ?_, ?_, support.readOnly shared _ _ _ rfl fetch,
    support.sameMemory current rfl, exit_post pre exit⟩
  · simpa only [stack] using actual
  · intro read member
    have same : read = ⟨.stack, initial.registers .rsp, 8⟩ := List.mem_singleton.mp member
    subst read
    exact reads

/-- Current authority is unchanged through the counting loop, then the actual
checked STORE produces the evolved world used by RET and the return contract. -/
def certificate {Ghost : Type} {rules : Rules Ghost} {input initial}
    (pre : Pre bytes input initial) (support : Support input initial rules) :
    ResourceCutpoints.Certificate flow rules (Post input initial) where
  Inv := Inv rules input initial
  rank := rank
  Interior source budget node shared state :=
    rules.Current shared state ∧ Interior input initial source budget node state
  start node shared state cut valid := by
    obtain ⟨current, valid⟩ := valid
    cases node <;> simp only [flow, isCut, Bool.false_eq_true] at cut
    · change state = initial at valid
      subst state
      refine ⟨current, ?_⟩
      simpa only [rank, ite_true, pre.count] using (Interior.entry (input := input) (initial := initial))
    · obtain ⟨header⟩ := valid
      exact ⟨current, by simpa only [rank, reduceCtorEq, ite_false, Nat.add_zero] using Interior.increment header⟩
  localVC source budget node shared state valid := by
    obtain ⟨current, inside⟩ := valid
    cases inside with
    | entry => exact vc_entry pre support current
    | test => exact vc_test pre support current
    | guard prior => exact vc_guard pre support prior current
    | increment h => exact vc_increment pre support h current
    | decrement h => exact vc_decrement pre support h current
    | back h => exact vc_back pre support h current
    | store ready => exact vc_store pre support ready current
    | ret exit => exact vc_ret pre support exit current

end EDSL.CountedStoreFinal64
