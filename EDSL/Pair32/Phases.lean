/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Pair32.Model

namespace EDSL.Pair32
open X86

def headerIndex : Loop → Index
  | .first => ⟨1, by decide⟩
  | .second => ⟨7, by decide⟩
def testedIndex : Loop → Index
  | .first => ⟨2, by decide⟩
  | .second => ⟨8, by decide⟩
def bodyIndex : Loop → Index
  | .first => ⟨3, by decide⟩
  | .second => ⟨9, by decide⟩
def loadedIndex : Loop → Index
  | .first => ⟨4, by decide⟩
  | .second => ⟨10, by decide⟩
def decrementedIndex : Loop → Index
  | .first => ⟨5, by decide⟩
  | .second => ⟨11, by decide⟩
def advancedIndex : Loop → Index
  | .first => ⟨6, by decide⟩
  | .second => ⟨12, by decide⟩

/-- The first phase reserves a strictly positive budget for the transition to
the second. Both loops use ordinary natural counts within that phase budget. -/
def budget (loop : Loop) (count secondLength : Nat) : Nat :=
  match loop with
  | .first => count + secondLength + 1
  | .second => count

inductive Invariant (initial : State) (valuesA valuesB : List (BitVec 32)) (target : Word) :
    Index → State → Prop where
  | entry (pre : Pre bytes initial valuesA valuesB target) :
      Invariant initial valuesA valuesB target ⟨0, by decide⟩ initial
  | loop {loop : Loop} {state : State} (header : Header initial valuesA valuesB loop state) :
      Invariant initial valuesA valuesB target (headerIndex loop) state

/-- Interior annotations retain a local current state and the original segment
budget. They contain no future execution or assumed terminating result. -/
inductive Phase (initial : State) (valuesA valuesB : List (BitVec 32)) (target : Word) :
    Index → Nat → Index → State → Prop where
  | entry (pre : Pre bytes initial valuesA valuesB target) :
      Phase initial valuesA valuesB target ⟨0, by decide⟩ (valuesA.length + valuesB.length + 2)
        ⟨0, by decide⟩ initial
  | header {loop : Loop} {state : State} (header : Header initial valuesA valuesB loop state) :
      Phase initial valuesA valuesB target (headerIndex loop) (budget loop header.count valuesB.length)
        (headerIndex loop) state
  | tested {loop : Loop} {state : State} (header : Header initial valuesA valuesB loop state) (af : Bool) :
      Phase initial valuesA valuesB target (headerIndex loop) (budget loop header.count valuesB.length)
        (testedIndex loop) (test loop state af)
  | body {loop : Loop} {state : State} (header : Header initial valuesA valuesB loop state)
      (element : Element header) (af : Bool) :
      Phase initial valuesA valuesB target (headerIndex loop) (budget loop header.count valuesB.length)
        (bodyIndex loop) (body loop initial.rip state af)
  | loaded {loop : Loop} {state : State} (header : Header initial valuesA valuesB loop state)
      (element : Element header) (af : Bool) :
      Phase initial valuesA valuesB target (headerIndex loop) (budget loop header.count valuesB.length)
        (loadedIndex loop) (load (body loop initial.rip state af) element.first)
  | decremented {loop : Loop} {state : State} (header : Header initial valuesA valuesB loop state)
      (element : Element header) (af : Bool) :
      Phase initial valuesA valuesB target (headerIndex loop) (budget loop header.count valuesB.length)
        (decrementedIndex loop) (decrement loop (load (body loop initial.rip state af) element.first))
  | advanced {loop : Loop} {state : State} (header : Header initial valuesA valuesB loop state)
      (element : Element header) (af : Bool) :
      Phase initial valuesA valuesB target (headerIndex loop) (budget loop header.count valuesB.length)
        (advancedIndex loop) (advance loop (decrement loop (load (body loop initial.rip state af) element.first)))
  | returning {state : State} (header : Header initial valuesA valuesB .second state)
      (zero : header.count = 0) (af : Bool) :
      Phase initial valuesA valuesB target (headerIndex .second) header.count
        ⟨13, by decide⟩ (exitState .second initial.rip state af)

def rank (lengthA lengthB : Nat) (node : Index) (state : State) : Nat :=
  if node.val = 0 then lengthA + lengthB + 2
  else if node.val = 1 then (state.registers .rsi).toNat + lengthB + 1
  else (state.registers .rcx).toNat

theorem rank_header {initial state : State} {valuesA valuesB : List (BitVec 32)} {loop : Loop}
    (header : Header initial valuesA valuesB loop state) :
    rank valuesA.length valuesB.length (headerIndex loop) state = budget loop header.count valuesB.length := by
  cases loop with
  | first =>
    change (state.registers Loop.first.counter).toNat + valuesB.length + 1 = _
    rw [header.rank]
    rfl
  | second => exact header.rank

theorem Phase.memory {initial state : State} {valuesA valuesB : List (BitVec 32)}
    {target : Word} {source node : Index} {amount : Nat}
    (inside : Phase initial valuesA valuesB target source amount node state) :
    state.memory = initial.memory := by
  cases inside with
  | entry => rfl
  | header header | tested header af | body header element af | loaded header element af
  | decremented header element af | advanced header element af | returning header zero af =>
    exact header.frame.memory

theorem Phase.pc {initial state : State} {valuesA valuesB : List (BitVec 32)}
    {target : Word} {source node : Index} {amount : Nat}
    (inside : Phase initial valuesA valuesB target source amount node state) :
    state.rip = initial.rip + BitVec.ofNat 64 (graph.node node).offset := by
  cases inside with
  | entry => change initial.rip = initial.rip + 0; exact (BitVec.add_zero _).symm
  | @header loop state header => cases loop <;> exact header.pc
  | @tested loop state header af =>
    cases loop <;> simp only [test, header.pc, BitVec.add_assoc] <;> rfl
  | @body loop state header element af => cases loop <;> rfl
  | @loaded loop state header element af =>
    cases loop <;> simp only [load, Pair32.body, atPC, edit, BitVec.add_assoc] <;> rfl
  | @decremented loop state header element af =>
    cases loop <;> simp only [decrement, load, Pair32.body, atPC, edit, BitVec.add_assoc] <;> rfl
  | @advanced loop state header element af =>
    cases loop <;> simp only [advance, decrement, load, Pair32.body, atPC, edit, BitVec.add_assoc] <;> rfl
  | returning header zero af => rfl

def Allowed (initial : State) (Access : Sequential.Read → Prop) (state : State)
    (read : Sequential.Read) : Prop := Access read ∧ state.memory = initial.memory

end EDSL.Pair32
