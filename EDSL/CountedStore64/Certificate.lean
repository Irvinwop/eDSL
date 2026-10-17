/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Invariant
import EDSL.CountedStore64.Support

set_option warningAsError true

namespace EDSL.CountedStore64.GCC
open EDSL X86 X86.Sequential OS Grading.Trace

/-- Each interior names the precise intermediate machine state. In
particular DEC's pending store is distinct from a completed iteration. -/
inductive Interior (input : Input) (initial : State) : Node → Nat → Node → State → Prop where
  | entry : Interior input initial .entry (input.count.toNat + 1) .entry initial
  | header {state} (header : Header input initial state) :
      Interior input initial .header (state.registers .rdx).toNat .header state
  | guard {state} (header : Header input initial state) (af : Bool) :
      Interior input initial .header (state.registers .rdx).toNat .guard (test state af)
  | increment {state} (header : Header input initial state)
      (nonzero : state.registers .rdx ≠ 0) (af : Bool) :
      Interior input initial .header (state.registers .rdx).toNat .increment (body initial.rip state af)
  | decrement {state} (header : Header input initial state)
      (nonzero : state.registers .rdx ≠ 0) (af : Bool) :
      Interior input initial .header (state.registers .rdx).toNat .decrement
        (GCC.increment (body initial.rip state af))
  | store {state} (header : Header input initial state)
      (nonzero : state.registers .rdx ≠ 0) (af : Bool) :
      Interior input initial .header (state.registers .rdx).toNat .store (pending initial.rip state af)
  | back {state} (header : Header input initial state)
      (nonzero : state.registers .rdx ≠ 0) (af : Bool) :
      Interior input initial .header (state.registers .rdx).toNat .back (GCC.store (pending initial.rip state af))
  | ret {state} (header : Header input initial state)
      (zero : state.registers .rdx = 0) (af : Bool) :
      Interior input initial .header (state.registers .rdx).toNat .ret (exitState initial.rip state af)

def rank (node : Node) (state : State) : Nat :=
  (state.registers .rdx).toNat + if node = .entry then 1 else 0

def Inv {Ghost : Type} (rules : Rules Ghost) (input : Input) (initial : State)
    (node : Node) (shared : Ghost) (state : State) : Prop :=
  rules.Current shared state ∧ match node with
    | .entry => state = initial
    | .header => Nonempty (Header input initial state)
    | _ => False

theorem interior_frame {input initial source budget node state}
    (pre : Pre bytes input initial) (inside : Interior input initial source budget node state) :
    Frame input initial state := by
  cases inside with
  | entry => exact Frame.initial pre
  | header h => exact h.frame
  | guard h af => exact h.frame.test af
  | increment h _ af => exact (h.frame.test af).atPC _
  | decrement h _ af => exact ((h.frame.test af).atPC _).increment
  | store h _ af => exact pending_frame h af
  | back h _ af => exact (pending_frame h af).store pre
  | ret h _ af => exact (h.frame.test af).atPC _

theorem interior_pc {input initial source budget node state}
    (inside : Interior input initial source budget node state) :
    state.rip = initial.rip + BitVec.ofNat 64 (offset node) := by
  cases inside with
  | entry => simp [offset]
  | header h => exact h.pc
  | guard h af => simp only [test, h.pc, BitVec.add_assoc]; rfl
  | increment h _ af => rfl
  | decrement h _ af => simp only [increment, body, atPC, BitVec.add_assoc]; rfl
  | store h _ af => simp only [pending, decrement, increment, body, atPC, BitVec.add_assoc]; rfl
  | back h _ af => simp only [store, pending, decrement, increment, body, atPC, BitVec.add_assoc]; rfl
  | ret h _ af => rfl

/-- A single local proof is instantiated by raw RAM and current OS rules.
Its rank reads RDX from the machine, independently of the ghost world. -/
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
      exact ⟨current, by simpa only [rank, reduceCtorEq, ite_false, Nat.add_zero] using Interior.header header⟩
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
      have nextCurrent := support.sameMemory current (show (move initial).memory = initial.memory from rfl)
      refine ⟨⟨.next (move initial), []⟩, shared, actual, by simp,
        support.readOnly shared _ _ _ rfl fetch, .header, Edge.entry, Or.inl ⟨rfl, ?_, ?_⟩⟩
      · exact ⟨nextCurrent, ⟨initialized pre⟩⟩
      · simp [rank, move, State.writeRegister, pre.count]
    | header h =>
      intro af
      have actual := (step_eq_execute af decoded).trans (execute_test _ af)
      refine ⟨⟨.next (test _ af), []⟩, shared, actual, by simp,
        support.readOnly shared _ _ _ rfl fetch, .guard, Edge.header,
        Or.inr ⟨rfl, support.sameMemory current rfl, Interior.guard h af⟩⟩
    | @guard before h prior =>
      intro af
      by_cases zero : before.registers .rdx = 0
      · have zf : (test before prior).flags.getLsbD 6 = true := by rw [tested_zero, zero]; decide
        have actual := (step_eq_execute af decoded).trans (guard_exit frame.code pc zf af)
        exact ⟨⟨.next (exitState initial.rip before prior), []⟩, shared, actual, by simp,
          support.readOnly shared _ _ _ rfl fetch, .ret, Edge.exit,
          Or.inr ⟨rfl, support.sameMemory current rfl, Interior.ret h zero prior⟩⟩
      · have zf : (test before prior).flags.getLsbD 6 = false := by
          rw [tested_zero]
          simp only [Bool.beq_eq_decide_eq, zero, decide_false]
        have actual := (step_eq_execute af decoded).trans (guard_body pc zf af)
        exact ⟨⟨.next (body initial.rip before prior), []⟩, shared, actual, by simp,
          support.readOnly shared _ _ _ rfl fetch, .increment, Edge.body,
          Or.inr ⟨rfl, support.sameMemory current rfl, Interior.increment h zero prior⟩⟩
    | @increment before h nonzero prior =>
      intro af
      have actual := (step_eq_execute af decoded).trans (execute_increment _ af)
      exact ⟨⟨.next (GCC.increment (body initial.rip before prior)), []⟩, shared, actual, by simp,
        support.readOnly shared _ _ _ rfl fetch, .decrement, Edge.increment,
        Or.inr ⟨rfl, support.sameMemory current rfl, Interior.decrement h nonzero prior⟩⟩
    | @decrement before h nonzero prior =>
      intro af
      have actual := (step_eq_execute af decoded).trans (execute_decrement _ af)
      exact ⟨⟨.next (pending initial.rip before prior), []⟩, shared, actual, by simp,
        support.readOnly shared _ _ _ rfl fetch, .store, Edge.decrement,
        Or.inr ⟨rfl, support.sameMemory current rfl, Interior.store h nonzero prior⟩⟩
    | @store before h nonzero prior =>
      intro af
      have pointer := frame.pointer pre
      have writable : canStoreQWord (pending initial.rip before prior).memory
          ((pending initial.rip before prior).registers .rdi) = true := by
        rw [pointer]; exact frame.writable
      have actual := (step_eq_execute af decoded).trans (execute_store _ af writable)
      obtain ⟨evolved, evolvedCurrent, effect⟩ :=
        support.store shared _ current decoded pointer frame.writable fetch
      exact ⟨⟨.next (GCC.store (pending initial.rip before prior)), []⟩, evolved, actual, by simp,
        effect, .back, Edge.store, Or.inr ⟨rfl, evolvedCurrent, Interior.back h nonzero prior⟩⟩
    | @back before h nonzero prior =>
      intro af
      have actual := (step_eq_execute af decoded).trans (back_edge frame.code pc af)
      have nextCurrent := support.sameMemory current
        (show (cycle initial.rip before prior).memory = (GCC.store (pending initial.rip before prior)).memory from rfl)
      refine ⟨⟨.next (cycle initial.rip before prior), []⟩, shared, actual, by simp,
        support.readOnly shared _ _ _ rfl fetch, .header, Edge.back, Or.inl ⟨rfl, ?_, ?_⟩⟩
      · exact ⟨nextCurrent, ⟨nextHeader pre h nonzero prior⟩⟩
      · simpa only [rank, reduceCtorEq, ite_false, Nat.add_zero] using rank_decreases h nonzero prior
    | @ret before h zero prior =>
      intro af
      have stack : (exitState initial.rip before prior).registers .rsp = initial.registers .rsp :=
        frame.registers .rsp (by decide) (by decide)
      have loaded : readWord (exitState initial.rip before prior).memory
          ((exitState initial.rip before prior).registers .rsp) = .ok input.returnAddress := by
        rw [stack]; exact frame.stackRead
      have actual := (step_eq_execute af decoded).trans (execute_ret loaded pre.memory.returnCanonical af)
      have reads := support.stack shared _ current stack frame.stackRead
      refine ⟨⟨.returned (finish (exitState initial.rip before prior) input.returnAddress),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩, shared, ?_, ?_,
        support.readOnly shared _ _ _ rfl fetch,
        support.sameMemory current rfl, exit_post pre h zero prior⟩
      · simpa only [stack] using actual
      · intro read member
        have same : read = ⟨.stack, initial.registers .rsp, 8⟩ := List.mem_singleton.mp member
        subst read
        exact reads

end EDSL.CountedStore64.GCC
