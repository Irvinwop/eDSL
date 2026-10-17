/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Clang.Invariant
import EDSL.CountedStore64.Clang.Support

set_option warningAsError true

namespace EDSL.CountedStore64.Clang
open EDSL X86 X86.Sequential OS Grading.Trace

/-- Exact intermediate states keep the completed STORE separate from the
still pending counter decrement. RET can follow either the entry guard or
the post-DEC branch, carrying the same settled value and resource world. -/
inductive Interior (input : Input) (initial : State) : Node → Nat → Node → State → Prop where
  | entry : Interior input initial .entry (input.count.toNat + 1) .entry initial
  | test : Interior input initial .entry (input.count.toNat + 1) .test (move initial)
  | guard (af : Bool) :
      Interior input initial .entry (input.count.toNat + 1) .guard (Clang.test (move initial) af)
  | increment {state} (header : Header input initial state) :
      Interior input initial .increment (state.registers .rdx).toNat .increment state
  | store {state} (header : Header input initial state) :
      Interior input initial .increment (state.registers .rdx).toNat .store (incState state)
  | decrement {state} (header : Header input initial state) :
      Interior input initial .increment (state.registers .rdx).toNat .decrement (storedState state)
  | back {state} (header : Header input initial state) :
      Interior input initial .increment (state.registers .rdx).toNat .back (decState state)
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
  | store h => exact incState_frame h
  | decrement h => exact storedState_frame pre h
  | back h => exact decState_frame pre h
  | ret exit => exact exit.frame

theorem interior_pc {input initial source budget node state}
    (inside : Interior input initial source budget node state) :
    state.rip = initial.rip + BitVec.ofNat 64 (offset node) := by
  cases inside with
  | entry => simp [offset]
  | test => rfl
  | guard af => simp only [GCC.test, GCC.move, BitVec.add_assoc]; rfl
  | increment h => exact h.pc
  | store h => simp only [incState, GCC.increment, h.pc, BitVec.add_assoc]; rfl
  | decrement h => simp only [storedState, incState, GCC.store, GCC.increment, h.pc,
      BitVec.add_assoc]; rfl
  | back h => simp only [decState, storedState, incState, GCC.decrement, GCC.store,
      GCC.increment, h.pc, BitVec.add_assoc]; rfl
  | ret exit => exact exit.pc

/-- Actual local machine steps compose under both ordinary RAM and current
ownership rules. Every STORE threads its evolved world into DEC and JNZ. -/
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
    have frame := interior_frame pre inside
    have pc := interior_pc inside
    have decoded := decode frame.code node pc
    have fetch := fetch_at frame.code node pc
    refine ⟨current, instruction node, decoded, ?_⟩
    cases inside with
    | entry =>
      intro af
      have actual := (step_eq_execute af decoded).trans (execute_move initial af)
      exact ⟨⟨.next (move initial), []⟩, shared, actual, by simp,
        support.readOnly shared _ _ _ rfl fetch, .test, Edge.entry,
        Or.inr ⟨rfl, support.sameMemory current rfl, Interior.test⟩⟩
    | test =>
      intro af
      have actual := (step_eq_execute af decoded).trans (execute_test _ af)
      exact ⟨⟨.next (test (move initial) af), []⟩, shared, actual, by simp,
        support.readOnly shared _ _ _ rfl fetch, .guard, Edge.test,
        Or.inr ⟨rfl, support.sameMemory current rfl, Interior.guard af⟩⟩
    | guard prior =>
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
    | increment h =>
      intro af
      have actual := (step_eq_execute af decoded).trans (execute_increment _ af)
      exact ⟨⟨.next (incState state), []⟩, shared, actual, by simp,
        support.readOnly shared _ _ _ rfl fetch, .store, Edge.increment,
        Or.inr ⟨rfl, support.sameMemory current rfl, Interior.store h⟩⟩
    | @store before h =>
      intro af
      have pointer := frame.pointer pre
      have writable : canStoreQWord (incState before).memory
          ((incState before).registers .rdi) = true := by
        rw [pointer]; exact frame.writable
      have actual := (step_eq_execute af decoded).trans (execute_store _ af writable)
      obtain ⟨evolved, evolvedCurrent, effect⟩ :=
        support.store shared _ current decoded pointer frame.writable fetch
      exact ⟨⟨.next (storedState before), []⟩, evolved, actual, by simp,
        effect, .decrement, Edge.store, Or.inr ⟨rfl, evolvedCurrent, Interior.decrement h⟩⟩
    | @decrement before h =>
      intro af
      have actual := (step_eq_execute af decoded).trans (execute_decrement _ af)
      exact ⟨⟨.next (decState before), []⟩, shared, actual, by simp,
        support.readOnly shared _ _ _ rfl fetch, .back, Edge.decrement,
        Or.inr ⟨rfl, support.sameMemory current rfl, Interior.back h⟩⟩
    | @back before h =>
      intro af
      by_cases zero : (decState before).registers .rdx = 0
      · have zf : (decState before).flags.getLsbD 6 = true := by
          rw [decState, decremented_zero]
          change ((decState before).registers .rdx == 0) = true
          rw [zero]; decide
        have actual := (step_eq_execute af decoded).trans (back_exit pc zf af)
        exact ⟨⟨.next (exited initial.rip before), []⟩, shared, actual, by simp,
          support.readOnly shared _ _ _ rfl fetch, .ret, Edge.finish,
          Or.inr ⟨rfl, support.sameMemory current rfl, Interior.ret (nextExit pre h zero)⟩⟩
      · have zf : (decState before).flags.getLsbD 6 = false := by
          rw [decState, decremented_zero]
          change ((decState before).registers .rdx == 0) = false
          simp only [Bool.beq_eq_decide_eq, zero, decide_false]
        have actual := (step_eq_execute af decoded).trans (back_taken frame.code pc zf af)
        refine ⟨⟨.next (continued initial.rip before), []⟩, shared, actual, by simp,
          support.readOnly shared _ _ _ rfl fetch, .increment, Edge.back,
          Or.inl ⟨rfl, ⟨support.sameMemory current rfl, ⟨nextHeader pre h zero⟩⟩, ?_⟩⟩
        simpa only [rank, reduceCtorEq, ite_false, Nat.add_zero, continued, GCC.atPC] using rank_decreases h
    | ret exit =>
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

end EDSL.CountedStore64.Clang
