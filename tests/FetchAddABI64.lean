/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.FetchAddABI64
import tests.FetchAddCalls64

namespace EDSL.Tests.FetchAddABI64
open X86 OS.FetchAddABI64

/-- Synthetic complete MOV RAX,RSI / LOCK XADD [RDI],RAX / RET image,
including its padding. Fixture addresses do not establish frozen ELF identity. -/
def image : Image := ⟨393216,
  [0x48,0x89,0xf0,0xf0,0x48,0x0f,0xc1,0x07,0xc3,0x90,0x90,0x90,0x90,0x90,0x90,0x90]⟩

/-- Fresh current caller authority, installed through actual checked allocation,
initialization, protection and borrowing. No old fixture caller slot is reused. -/
def caller (before : TSO64.Checked) (owner actor : Nat) (address returnAddress : Word) :
    Except OS.Atomics64.Fault (TSO64.Checked × Nat) := do
  let (allocated, out) ← TSO64.change before (.allocate owner ⟨address,8⟩ OS.AddressSpace.readWrite)
  let ticket ← TSO64.ticket out
  let (written, _) ← TSO64.change allocated (.store64 owner ticket address returnAddress)
  let (readOnly, _) ← TSO64.change written (.protect owner ticket OS.AddressSpace.readOnly)
  TSO64.borrow readOnly owner ticket actor ⟨address,8⟩

def setupAt (stackA : Word) (first second old deltaA deltaB : Word) :
    Except OS.TSO64.Fault (Sigma (OS.FetchAddCalls64.CheckedState ⟨0⟩)) := do
  let ready ← (TSO64.fixture first second old).mapError OS.TSO64.Fault.os
  let (oneCaller, callerA) ← (caller ready.checked 31 11 stackA 0x7000).mapError OS.TSO64.Fault.os
  let (twoCallers, callerB) ← (caller oneCaller 32 12 589832 0x8000).mapError OS.TSO64.Fault.os
  let initial : FetchAddCalls64.Current := ⟨⟨twoCallers.world, []⟩, twoCallers.valid, by simp⟩
  let one ← FetchAddCalls64.attach initial 11
    { TSO64.context stackA 131072 deltaA 0 with flags := 0x202 }
    ready.codeA callerA [ready.dataA] [ready.atomicA]
  let two ← FetchAddCalls64.attach one 12
    { TSO64.context 589832 196608 deltaB 0 with flags := 0x202 }
    ready.codeB callerB [ready.dataB] [ready.atomicB]
  FetchAddCalls64.selectTarget two

/-- Both original caller slots are 8 mod16, as scalar SysV entry requires. -/
def setup := setupAt 524296

def observe (old deltaA deltaB : Word) (entries : List (OS.FetchAddCalls64.Entry Nat)) := do
  let ⟨cell, before⟩ ← setup 0x07c10f48f0f08948 0x90909090909090c3 old deltaA deltaB
  return (checkComplete image before entries,
    (replay image ⟨0⟩ cell before entries).map fun (result : OS.FetchAddCalls64.Result Nat ⟨0⟩ cell) =>
      (TSO64.events result.observations, OS.FetchAddCalls64.read result.state.state cell,
        OS.TSO64.collect result.state.state 0, OS.TSO64.collect result.state.state 1))

-- Literal mathematical results distinguish 32-bit truncation, lost carry,
-- wrong issue order, and returning the new word instead of the entire old word.
example : observe 0x11223344ffffffff 1 0x100000001
    (FetchAddCalls64.forward 0x11223344ffffffff 0x1122334500000000 1 0x100000001) = .ok
    (true, some ([(0,1,0x11223344ffffffff,0x1122334500000000),
      (1,0x100000001,0x1122334500000000,0x1122334600000001)],
      .ok 0x1122334600000001, .ok 0x11223344ffffffff, .ok 0x1122334500000000)) := by rfl

example : observe 0xfffffffffffffffe 1 2
    (FetchAddCalls64.reverse 0xfffffffffffffffe 0 1 2) = .ok
    (true, some ([(1,2,0xfffffffffffffffe,0), (0,1,0,1)],
      .ok 1, .ok 0, .ok 0xfffffffffffffffe)) := by rfl

/-- Retain checked resource authority while choosing a different present CPU
context. The real gate still reads the actual selected worker and RAM. -/
def recontext {target cell} (before : OS.FetchAddCalls64.CheckedState target cell)
    (change : OS.TSO64.Context → OS.TSO64.Context) : OS.FetchAddCalls64.CheckedState target cell :=
  ⟨{ before.state with workers := before.state.workers.map fun worker =>
      { worker with context := change worker.context } },
    ⟨before.valid.1, by
      intro worker member
      obtain ⟨original, listed, rfl⟩ := List.mem_map.mp member
      exact before.valid.2 original listed⟩, before.live⟩

def register (context : OS.TSO64.Context) (selected : Register) (value : Word) : OS.TSO64.Context :=
  { context with registers := fun query => if query = selected then value else context.registers query }

-- Useful present rejection controls. The wrong target is an actually mapped
-- neighboring word; the wrong delta differs only above bit31. A readable
-- peer's readable caller slot cannot replace the original caller slot.
def presentControls := do
  let ⟨cell, before⟩ ← setup 0x07c10f48f0f08948 0x90909090909090c3 17 1 2
  let admits := fun state => ((replay image ⟨0⟩ cell state
    ([.invoke 10 0 1] : List (OS.FetchAddCalls64.Entry Nat))).isSome)
  return [admits before,
    admits (recontext before fun context => { context with rip := context.rip + 3 }),
    admits (recontext before fun context => register context .rdi 65544),
    admits (recontext before fun context => register context .rsi 0x100000001),
    admits (recontext before fun context => register context .rsp 589832),
    admits (recontext before fun context => { context with flags := context.flags ||| 0x400 })]

example : presentControls = .ok [true,false,false,false,false,false] := by rfl

-- This separately allocated, readable ORIGINAL caller slot is qword aligned,
-- but is 0 mod16; its resources are valid while its scalar ABI entry is not.
def misaligned := do
  let ⟨cell, before⟩ ← setupAt 524288 0x07c10f48f0f08948 0x90909090909090c3 17 1 2
  return (replay image ⟨0⟩ cell before ([.invoke 10 0 1] : List (OS.FetchAddCalls64.Entry Nat))).isNone

example : misaligned = .ok true := by rfl

-- A changed LAST padding byte rejects even though every instruction and its
-- entry still match. This catches a checker that binds only a decoded prefix.
def changedTail := do
  let ⟨cell, before⟩ ← setup 0x07c10f48f0f08948 0x91909090909090c3 17 1 2
  return (replay image ⟨0⟩ cell before ([.invoke 10 0 1] : List (OS.FetchAddCalls64.Entry Nat))).isNone

example : changedTail = .ok true := by rfl

/-- This different synthetic image begins with a real ordinary queued store.
After that store, its suffix is the declared entry image for the pending test. -/
def pendingImage : Image := ⟨393219,
  [0x48,0x89,0xf0,0xf0,0x48,0x0f,0xc1,0x07,0xc3,0x90,0x90,0x90,0x90]⟩

def pendingEntry := do
  let ⟨cell, before⟩ ← setup 0x48f0f08948328948 0x90909090c307c10f 17 1 2
  let queued ← OS.FetchAddCalls64.step before (.issue 0 false)
  let blocked := (replay pendingImage ⟨0⟩ cell queued.1
    ([.invoke 10 0 1] : List (OS.FetchAddCalls64.Entry Nat))).isNone
  let published ← OS.FetchAddCalls64.step queued.1 (.drain 0)
  let admitted := (replay pendingImage ⟨0⟩ cell published.1
    ([.invoke 10 0 1] : List (OS.FetchAddCalls64.Entry Nat))).isSome
  return (blocked, admitted)

-- The real FIFO drain changes admission at the same RIP, image and arguments.
example : pendingEntry = .ok (true,true) := by rfl

end EDSL.Tests.FetchAddABI64

#print axioms EDSL.OS.FetchAddABI64.gate_sound
#print axioms EDSL.OS.FetchAddABI64.checkComplete_sound
#print axioms EDSL.OS.FetchAddABI64.invocation_at
#print axioms EDSL.OS.FetchAddABI64.checked_complete
#audit_edsl
