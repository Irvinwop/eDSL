/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO.CounterCalls
import EDSL.Audit

namespace EDSL.Tests.TSOCounterCalls
open X86 OS OS.TSO OS.TSO.CounterCalls Concurrency

/- Synthetic executable bytes: MOV EAX,1; MOV [RSI],EAX; MOV EAX,1;
   LOCK XADD [RDI],EAX; RET. Each thread has its own publication and stack. -/
def bytes : List Byte :=
  [0xb8, 1, 0, 0, 0, 0x89, 0x06, 0xb8, 1, 0, 0, 0, 0xf0, 0x0f, 0xc1, 0x07, 0xc3]

def memory (old : BitVec 32) (code : List Byte) : X86.Memory where
  read address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length then code[address.toNat - 4096]?
    else if address.toNat = 32769 ∨ address.toNat = 36865 then some 0x20
    else if (32768 ≤ address.toNat ∧ address.toNat < 32776) ∨
        (36864 ≤ address.toNat ∧ address.toNat < 36872) then some 0
    else if address.toNat = 65536 then some (old.extractLsb' 0 8)
    else if address.toNat = 65537 then some (old.extractLsb' 8 8)
    else if address.toNat = 65538 then some (old.extractLsb' 16 8)
    else if address.toNat = 65539 then some (old.extractLsb' 24 8)
    else if 65540 ≤ address.toNat ∧ address.toNat < 65552 then some 0xa5
    else none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length)
  writable address := decide (65536 ≤ address.toNat ∧ address.toNat < 65548)

def context (publication stack : Word) : Threads.Context where
  registers register := if register = .rdi then 65536
    else if register = .rsi then publication else if register = .rsp then stack else 0xfeedface89abcdef
  rip := 4096
  flags := 0x8d7

def initial (old : BitVec 32 := 0) (code : List Byte := bytes) : OS.TSO.State :=
  ⟨memory old code, [⟨context 65540 32768, false, []⟩, ⟨context 65544 36864, false, []⟩]⟩

private def checked {α : Type} (attempt : Option α) (accepted : attempt.isSome = true) : α :=
  attempt.get accepted

private theorem checked_some {α : Type} (attempt : Option α) (accepted : attempt.isSome = true) :
    attempt = some (checked attempt accepted) := by
  cases attempt with
  | none => cases accepted
  | some result => rfl

def quiet (action : Action) : Entry := .execute action .quiet

/-- Both calls start before either RMW. Both threads really buffer an ordinary
store, and both locked attempts are blocked before the local drains. -/
def prelude : List Entry :=
  [.invoke 10 0 1, .invoke 20 1 1,
   quiet (.issue 0), quiet (.issue 1), quiet (.issue 0), quiet (.issue 1),
   quiet (.issue 0), quiet (.issue 1), quiet (.issue 0), quiet (.issue 1)]

def paused : Result := checked (replay 65536 initial prelude) (by rfl)

-- RAM still holds the publication sentinel while the FIFOs hold real stores.
example : loadDWord paused.state.memory 65536 = .ok 0 ∧
    loadDWord paused.state.memory 65540 = .ok 0xa5a5a5a5 ∧
    paused.state.workers.map (fun worker => worker.buffer.length) = [1, 1] ∧
    paused.observations.filterMap (fun observation => match observation with
      | .blocked thread => some thread | _ => none) = [0, 1] := ⟨rfl, rfl, rfl, rfl⟩

def overlap : List Entry := prelude ++
  [quiet (.drain 1), .execute (.issue 1) (.rmw 20), quiet (.drain 0), .execute (.issue 0) (.rmw 10),
   .execute (.issue 0) (.response 10 0 1), .execute (.issue 1) (.response 20 1 0)]

-- The first successful RMW runs while the peer's publication is still queued.
def firstRmw : Result := checked
  (replay 65536 initial (prelude ++ [quiet (.drain 1), .execute (.issue 1) (.rmw 20)])) (by rfl)

example : loadDWord firstRmw.state.memory 65536 = .ok 1 ∧
    loadDWord firstRmw.state.memory 65540 = .ok 0xa5a5a5a5 ∧
    loadDWord firstRmw.state.memory 65544 = .ok 1 ∧
    firstRmw.state.workers.map (fun worker => worker.buffer.length) = [1, 0] := ⟨rfl, rfl, rfl, rfl⟩

def overlapResult : Result := checked (replay 65536 initial overlap) (by rfl)

theorem overlap_replay : replay 65536 initial overlap = some overlapResult := checked_some _ _
theorem overlap_checked : checkComplete 65536 initial overlap = true := by rfl

-- Invocation order, RMW order and response order differ. This checks actual
-- returned old words and identity correspondence, not merely a final sum.
theorem overlap_calls : Linearizability.calls overlapResult.events =
    [⟨20, 1, 1, 0⟩, ⟨10, 0, 1, 1⟩] := by rfl

example : overlapResult.events =
    [.invoke 10 0 1, .invoke 20 1 1, .point ⟨20, 1, 1, 0⟩, .point ⟨10, 0, 1, 1⟩,
     .respond 10 0 1, .respond 20 1 0] ∧
    atomicEvents overlapResult.observations = [(1, ⟨65536, 0, 1⟩), (0, ⟨65536, 1, 2⟩)] ∧
    overlapResult.state.workers.map (fun worker =>
      (worker.context.registers .rax, worker.context.rip, worker.context.registers .rsp,
       worker.returned, worker.buffer.length)) =
      [(1, 8192, 32776, true, 0), (0, 8192, 36872, true, 0)] ∧
    loadDWord overlapResult.state.memory 65540 = .ok 1 ∧
    loadDWord overlapResult.state.memory 65544 = .ok 1 ∧
    loadDWord overlapResult.state.memory 65548 = .ok 0xa5a5a5a5 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem certificate {before : OS.TSO.State} {entries : List Entry} {result : Result}
    {old final : BitVec 32} (read : loadDWord before.memory 65536 = .ok old)
    (accepted : checkComplete 65536 before entries = true)
    (replayed : replay 65536 before entries = some result)
    (finalRead : loadDWord result.state.memory 65536 = .ok final) :
    Linearizability.Linearization result.events (fun calls => Counter.Sequential old (calls.map operation) final) := by
  obtain ⟨actual, value, actualReplay, _, _, ram, _, linearization, _⟩ :=
    checked_linearization read accepted
  have same : actual = result := Option.some.inj (actualReplay.symm.trans replayed)
  subst actual
  have valueEq : value = final := Except.ok.inj (ram.symm.trans finalRead)
  simpa only [valueEq] using linearization

theorem overlap_linearization : Linearizability.Linearization overlapResult.events
    (fun calls => Counter.Sequential 0 (calls.map operation) 2) :=
  certificate (by rfl) overlap_checked overlap_replay (by rfl)

-- Kernel-checked independent sequential fetch-add relation for those calls.
example : Counter.Sequential 0 [⟨1, 1, 0⟩, ⟨0, 1, 1⟩] 2 := by
  simpa only [overlap_calls, List.map_cons, List.map_nil, operation] using overlap_linearization.sequential

-- Expose a decoded origin at an actual prefix, including the input register,
-- installed architectural output, and scheduler observation.
example : Occurs initial (actions overlap) (fun state action result =>
    Counter.Origin 65536 state action result ⟨1, 1, 0⟩) := by
  exact (replay_sound overlap_replay).backed
    (show Linearizability.Event.point ⟨20, 1, 1, 0⟩ ∈ overlapResult.events from by decide) (by decide)

example : Occurs initial (actions overlap) (fun state action result =>
    ReturnOrigin state action result 0 1) := by
  exact (replay_sound overlap_replay).backed
    (show Linearizability.Event.respond 10 0 1 ∈ overlapResult.events from by decide) (by decide)

-- A second overlapping schedule has the opposite RMW order and responds
-- from thread one first. The adapter must follow actual events in both cases.
def otherOverlap : List Entry := prelude ++
  [quiet (.drain 0), .execute (.issue 0) (.rmw 10), quiet (.drain 1), .execute (.issue 1) (.rmw 20),
   .execute (.issue 1) (.response 20 1 1), .execute (.issue 0) (.response 10 0 0)]

def otherResult : Result := checked (replay 65536 initial otherOverlap) (by rfl)

example : checkComplete 65536 initial otherOverlap = true ∧
    Linearizability.calls otherResult.events = [⟨10, 0, 1, 0⟩, ⟨20, 1, 1, 1⟩] := ⟨rfl, rfl⟩

example : Linearizability.Linearization otherResult.events
    (fun calls => Counter.Sequential 0 (calls.map operation) 2) :=
  certificate (by rfl) (by rfl) (checked_some _ _) (by rfl)

/-- One actual call, with a blocked locked issue before the local drain. -/
def body (thread id : Nat) (ticket : BitVec 32) : List Entry :=
  [quiet (.issue thread), quiet (.issue thread), quiet (.issue thread), quiet (.issue thread),
   quiet (.drain thread), .execute (.issue thread) (.rmw id),
   .execute (.issue thread) (.response id thread ticket)]

def nonoverlap : List Entry := [.invoke 10 0 1] ++ body 0 10 0 ++ [.invoke 20 1 1] ++ body 1 20 1

def nonoverlapResult : Result := checked (replay 65536 initial nonoverlap) (by rfl)

theorem nonoverlap_replay : replay 65536 initial nonoverlap = some nonoverlapResult := checked_some _ _
theorem nonoverlap_checked : checkComplete 65536 initial nonoverlap = true := by rfl

theorem nonoverlap_linearization : Linearizability.Linearization nonoverlapResult.events
    (fun calls => Counter.Sequential 0 (calls.map operation) 2) :=
  certificate (by rfl) nonoverlap_checked nonoverlap_replay (by rfl)

-- The completed first call precedes the second invocation. Its ticket must be
-- zero and the second ticket one; a reversed proposed serial order is impossible.
example : nonoverlapResult.events =
    [.invoke 10 0 1, .point ⟨10, 0, 1, 0⟩, .respond 10 0 0,
     .invoke 20 1 1, .point ⟨20, 1, 1, 1⟩, .respond 20 1 1] ∧
    Counter.Sequential 0 [⟨0, 1, 0⟩, ⟨1, 1, 1⟩] 2 := by
  refine ⟨rfl, ?_⟩
  exact nonoverlap_linearization.sequential

-- Wraparound retains ticket semantics and full zero-extension at actual RET.
example : checkComplete 65536 (initial 0xffffffff)
    ([.invoke 10 0 1] ++ body 0 10 0xffffffff ++ [.invoke 20 1 1] ++ body 1 20 0) = true := by rfl

-- Duplicate invocation and wrong invocation input are rejected by the finite
-- protocol, despite successful underlying execution.
example : checkComplete 65536 initial (.invoke 10 0 1 :: overlap) = false := by rfl
example : checkComplete 65536 initial (.invoke 10 0 2 :: body 0 10 0) = false := by rfl

-- Invocation-thread agreement is independent of real RET/thread agreement.
example : (replay 65536 initial (.invoke 10 1 1 :: body 0 10 0)).isSome = true ∧
    checkComplete 65536 initial (.invoke 10 1 1 :: body 0 10 0) = false := ⟨rfl, rfl⟩

-- The reusable protocol forbids two outstanding calls on the same thread,
-- even when every identity, payload and interval is individually well formed.
example : Linearizability.check
    ([.invoke 1 7 2, .invoke 2 7 3, .point ⟨1, 7, 2, 0⟩, .point ⟨2, 7, 3, 2⟩,
      .respond 1 7 0, .respond 2 7 2] : List (Linearizability.Event Nat Nat Nat Nat)) = false := by rfl

-- A real RET followed by a late external invocation cannot repair an interval.
example : checkComplete 65536 initial (body 0 10 0 ++ [.invoke 10 0 1]) = false := by rfl

-- This response ticket disagrees with actual returned RAX (the old word zero).
example : replay 65536 initial (.invoke 10 0 1 :: body 0 10 1) = none := by rfl

-- Here the response label agrees with an actual RET, but code destroyed the
-- XADD ticket first. Lifecycle output agreement must independently reject it.
def changedReturnBytes : List Byte :=
  [0xb8, 1, 0, 0, 0, 0x89, 0x06, 0xb8, 1, 0, 0, 0, 0xf0, 0x0f, 0xc1, 0x07,
   0xb8, 7, 0, 0, 0, 0xc3]
def changedReturn : List Entry := [.invoke 10 0 1] ++ (body 0 10 0).take 6 ++
  [quiet (.issue 0), .execute (.issue 0) (.response 10 0 7)]

example : (replay 65536 (initial 0 changedReturnBytes) changedReturn).isSome = true ∧
    checkComplete 65536 (initial 0 changedReturnBytes) changedReturn = false := ⟨rfl, rfl⟩

-- Omitting the label on an actual target RMW is fail-closed at that step.
def missingRmw : List Entry := (.invoke 10 0 1 :: body 0 10 0).map fun entry => match entry with
  | .execute action (.rmw _) => .execute action .quiet
  | other => other

example : replay 65536 initial missingRmw = none := by rfl

-- An actual complete machine execution with no target RMW cannot stand in
-- for a fetch-add call, even when its returned value and RET are real.
def noRmwBytes : List Byte := [0xb8, 1, 0, 0, 0, 0xc3]
def noRmw : List Entry :=
  [.invoke 10 0 1, quiet (.issue 0), .execute (.issue 0) (.response 10 0 1)]

example : (replay 65536 (initial 0 noRmwBytes) noRmw).isSome = true ∧
    checkComplete 65536 (initial 0 noRmwBytes) noRmw = false := ⟨rfl, rfl⟩

-- A response on an ordinary MOV has no actual RET execution behind it, even
-- though the claimed return register value is already present after that MOV.
example : replay 65536 initial
    [.invoke 10 0 1, .execute (.issue 0) (.response 10 0 1)] = none := by rfl

-- A valid prefix with a real RMW remains pending; there is no free future RET.
example : (replay 65536 initial (.invoke 10 0 1 :: (body 0 10 0).take 6)).isSome = true ∧
    checkComplete 65536 initial (.invoke 10 0 1 :: (body 0 10 0).take 6) = false := ⟨rfl, rfl⟩

-- Actual code performing two RMWs in a single call cannot use one call identity
-- to hide the second update. The actual final ticket is one, not a fake trace.
def twiceBytes : List Byte :=
  [0xb8, 1, 0, 0, 0, 0x89, 0x06, 0xb8, 1, 0, 0, 0, 0xf0, 0x0f, 0xc1, 0x07,
   0xb8, 1, 0, 0, 0, 0xf0, 0x0f, 0xc1, 0x07, 0xc3]

def twice : List Entry :=
  [.invoke 10 0 1, quiet (.issue 0), quiet (.issue 0), quiet (.issue 0), quiet (.drain 0),
   .execute (.issue 0) (.rmw 10), quiet (.issue 0), .execute (.issue 0) (.rmw 10),
   .execute (.issue 0) (.response 10 0 1)]

example : (replay 65536 (initial 0 twiceBytes) twice).isSome = true ∧
    checkComplete 65536 (initial 0 twiceBytes) twice = false := ⟨rfl, rfl⟩

-- Duplicate-point rejection must not rely on differing tickets or final sums.
-- Change both RMW-input MOV immediates to zero; real observations coincide.
def zeroTwiceBytes : List Byte := (twiceBytes.set 8 0).set 17 0

def zeroTwice : List Entry :=
  [.invoke 10 0 0, quiet (.issue 0), quiet (.issue 0), quiet (.issue 0), quiet (.drain 0),
   .execute (.issue 0) (.rmw 10), quiet (.issue 0), .execute (.issue 0) (.rmw 10),
   .execute (.issue 0) (.response 10 0 0)]

def zeroTwiceResult : Result := checked (replay 65536 (initial 0 zeroTwiceBytes) zeroTwice) (by rfl)

example : atomicEvents zeroTwiceResult.observations =
    [(0, ⟨65536, 0, 0⟩), (0, ⟨65536, 0, 0⟩)] ∧
    checkComplete 65536 (initial 0 zeroTwiceBytes) zeroTwice = false := ⟨rfl, rfl⟩

end EDSL.Tests.TSOCounterCalls

#audit_edsl
