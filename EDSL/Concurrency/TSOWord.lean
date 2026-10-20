/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.State

/-!
An independent memory fragment of Owens, Sarkar and Sewell, §3.1, Figure 2:
https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.tphols.pdf

Buffers are newest first: writes prepend, forwarding selects the first matching
location, and publication removes the last entry. The paper presents 32-bit
values; this fragment uses uniform 64-bit `X86.Word` values at symbolic locations.
Registers, fences and instruction cores are erased. There is no address decoding,
OS/resource model, scheduler executor, or mixed-width overlap semantics here.
A client must justify its projection of managed persistent cells and actual
effects. Framing or erasing ordinary mixed-width accesses in that projection
does not establish their support in the paper's model.

`Step` and finite `Path` describe only the reference transitions below. They do
not impose the paper's progress condition or assert liveness, fairness, a full
x86/source semantics, or equivalence with the complete HOL4 formalization.
-/

set_option autoImplicit false

namespace EDSL.Concurrency.TSOWord

structure State (Location : Type) where
  memory : Location → Option X86.Word
  buffers : Nat → List (Location × X86.Word)
  lock : Option Nat

inductive Label (Location : Type) where
  | read (tid : Nat) (address : Location) (value : X86.Word)
  | write (tid : Nat) (address : Location) (value : X86.Word)
  | lock (tid : Nat)
  | unlock (tid : Nat)
  | tau
  deriving DecidableEq, Repr

variable {Location : Type}

def NotBlocked (s : State Location) (tid : Nat) : Prop :=
  s.lock = none ∨ s.lock = some tid

def NoPending (buffer : List (Location × X86.Word)) (address : Location) : Prop :=
  ∀ pair ∈ buffer, pair.1 ≠ address

/-- Update one processor's buffer, retaining every peer's buffer. -/
def setBuffer (buffers : Nat → List (Location × X86.Word)) (tid : Nat)
    (buffer : List (Location × X86.Word)) : Nat → List (Location × X86.Word) :=
  fun peer => if peer = tid then buffer else buffers peer

/-- Publish one whole symbolic word, retaining all other memory locations. -/
def setMemory [DecidableEq Location] (memory : Location → Option X86.Word)
    (address : Location) (value : X86.Word) : Location → Option X86.Word :=
  fun target => if target = address then some value else memory target

def writeBuffered (s : State Location) (tid : Nat) (address : Location)
    (value : X86.Word) : State Location :=
  { s with buffers := setBuffer s.buffers tid ((address, value) :: s.buffers tid) }

def publish [DecidableEq Location] (s : State Location) (tid : Nat)
    (remaining : List (Location × X86.Word)) (address : Location)
    (value : X86.Word) : State Location :=
  { s with
    memory := setMemory s.memory address value
    buffers := setBuffer s.buffers tid remaining }

def acquire (s : State Location) (tid : Nat) : State Location :=
  { s with lock := some tid }

def release (s : State Location) : State Location :=
  { s with lock := none }

/-- Exactly the memory, buffer and lock rules retained from Figure 2.
In particular, `writeBuffer` is unconditional even when a peer holds the lock. -/
inductive Step [DecidableEq Location] : State Location → Label Location →
    State Location → Prop where
  | readMemory {s : State Location} {tid : Nat} {address : Location} {value : X86.Word}
      (notBlocked : NotBlocked s tid)
      (memoryValue : s.memory address = some value)
      (noPending : NoPending (s.buffers tid) address) :
      Step s (.read tid address value) s
  | readBuffer {s : State Location} {tid : Nat} {address : Location} {value : X86.Word}
      {newer older : List (Location × X86.Word)}
      (notBlocked : NotBlocked s tid)
      (bufferValue : s.buffers tid = newer ++ [(address, value)] ++ older)
      (noNewer : NoPending newer address) :
      Step s (.read tid address value) s
  | writeBuffer {s : State Location} {tid : Nat} {address : Location} {value : X86.Word} :
      Step s (.write tid address value) (writeBuffered s tid address value)
  | publishOldest {s : State Location} {tid : Nat} {address : Location} {value : X86.Word}
      {remaining : List (Location × X86.Word)}
      (notBlocked : NotBlocked s tid)
      (oldest : s.buffers tid = remaining ++ [(address, value)]) :
      Step s .tau (publish s tid remaining address value)
  | lock {s : State Location} {tid : Nat}
      (lockNone : s.lock = none) (bufferEmpty : s.buffers tid = []) :
      Step s (.lock tid) (acquire s tid)
  | unlock {s : State Location} {tid : Nat}
      (lockHeld : s.lock = some tid) (bufferEmpty : s.buffers tid = []) :
      Step s (.unlock tid) (release s)

/-- Finite labelled paths; erasing an action can use `nil` directly. -/
inductive Path [DecidableEq Location] : State Location → List (Label Location) →
    State Location → Prop where
  | nil (s : State Location) : Path s [] s
  | cons {s middle t : State Location} {label : Label Location}
      {labels : List (Label Location)}
      (head : Step s label middle) (tail : Path middle labels t) :
      Path s (label :: labels) t

/-- Algebra for the exact endpoint of one locked buffered write and drain.
The original buffer function, including every peer's pending stores, is restored. -/
theorem lockedWrite_endpoint [DecidableEq Location]
    (s : State Location) (tid : Nat) (address : Location) (value : X86.Word)
    (lockNone : s.lock = none) (bufferEmpty : s.buffers tid = []) :
    release (publish (writeBuffered (acquire s tid) tid address value)
      tid [] address value) =
      { s with memory := setMemory s.memory address value } := by
  have restored :
      setBuffer (setBuffer s.buffers tid ((address, value) :: s.buffers tid)) tid [] =
        s.buffers := by
    funext peer
    change
      (if peer = tid then [] else
        if peer = tid then (address, value) :: s.buffers tid else s.buffers peer) =
          s.buffers peer
    by_cases same : peer = tid
    · subst peer
      exact (ite_eq_left (rfl : tid = tid)).trans bufferEmpty.symm
    · exact (ite_eq_right same).trans (ite_eq_right same)
  change
    ({ memory := setMemory s.memory address value
       buffers := setBuffer (setBuffer s.buffers tid ((address, value) :: s.buffers tid)) tid []
       lock := none } : State Location) =
      { s with memory := setMemory s.memory address value }
  rw [restored, lockNone]

/-- An explicit LOCK/read/write/Tau/unlock witness, including unchanged-value
writes. Only the selected memory word changes at the exact endpoint: the lock
is free again and the entire original buffer function is retained. -/
theorem lockedWrite_path [DecidableEq Location]
    (s : State Location) (tid : Nat) (address : Location) (old new : X86.Word)
    (lockNone : s.lock = none) (bufferEmpty : s.buffers tid = [])
    (memoryOld : s.memory address = some old) :
    Path s [.lock tid, .read tid address old, .write tid address new, .tau, .unlock tid]
      { s with memory := setMemory s.memory address new } := by
  have readStep :
      Step (acquire s tid) (.read tid address old) (acquire s tid) := by
    apply Step.readMemory
    · exact Or.inr rfl
    · exact memoryOld
    · change NoPending (s.buffers tid) address
      rw [bufferEmpty]
      intro pair member
      cases member
  have publishStep :
      Step (writeBuffered (acquire s tid) tid address new) .tau
        (publish (writeBuffered (acquire s tid) tid address new) tid [] address new) := by
    apply Step.publishOldest (tid := tid) (remaining := []) (address := address) (value := new)
    · exact Or.inr rfl
    · change (if tid = tid then (address, new) :: s.buffers tid else s.buffers tid) =
        [] ++ [(address, new)]
      rw [ite_eq_left (rfl : tid = tid), bufferEmpty]
      rfl
  have unlockStep :
      Step (publish (writeBuffered (acquire s tid) tid address new) tid [] address new)
        (.unlock tid)
        (release (publish (writeBuffered (acquire s tid) tid address new) tid [] address new)) := by
    apply Step.unlock
    · rfl
    · change (if tid = tid then [] else
        (writeBuffered (acquire s tid) tid address new).buffers tid) = []
      exact ite_eq_left (rfl : tid = tid)
  rw [← lockedWrite_endpoint s tid address new lockNone bufferEmpty]
  exact Path.cons (Step.lock lockNone bufferEmpty)
    (Path.cons readStep
      (Path.cons Step.writeBuffer
        (Path.cons publishStep (Path.cons unlockStep (Path.nil _)))))

end EDSL.Concurrency.TSOWord
