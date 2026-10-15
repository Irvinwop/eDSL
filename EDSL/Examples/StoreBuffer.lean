/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO.Trace

namespace EDSL.Examples.StoreBuffer
open X86 OS

/-- Owned two-location store-buffer litmus. Both workers run the same exact
MOV-store/MOV-load/RET bytes, with their two data pointers exchanged. -/
def code : List Byte := [0x89, 0x06, 0x8b, 0x07, 0xc3]

def memory : X86.Memory where
  read address :=
    if 4194304 ≤ address.toNat ∧ address.toNat < 4194309 then code[address.toNat - 4194304]?
    else if address.toNat = 32769 then some 0x20
    else if (32768 ≤ address.toNat ∧ address.toNat < 32776) ∨
        (65536 ≤ address.toNat ∧ address.toNat < 65544) then some 0
    else none
  executable address := decide (4194304 ≤ address.toNat ∧ address.toNat < 4194309)
  writable address := decide (65536 ≤ address.toNat ∧ address.toNat < 65544)

def context (destination source : Word) : Threads.Context where
  registers register := if register = .rax then 1 else if register = .rsi then destination
    else if register = .rdi then source else if register = .rsp then 32768 else 0xfeedface89abcdef
  rip := 4194304
  flags := 0x8d7

def sequential : MachineThreads.State :=
  ⟨memory, [⟨context 65536 65540, false⟩, ⟨context 65540 65536, false⟩]⟩

def initial : TSO.State := TSO.initial sequential

def delayed : List TSO.Action := [.issue 0, .issue 1, .issue 0, .issue 1]

def complete : List TSO.Action := delayed ++ [.issue 0, .issue 1, .drain 0, .drain 1]

def observe (state : TSO.State) : List Word × Option (BitVec 32) × Option (BitVec 32) ×
    List (Bool × Nat) :=
  (state.workers.map (fun worker => worker.context.registers .rax),
    (loadDWord state.memory 65536).toOption, (loadDWord state.memory 65540).toOption,
    state.workers.map (fun worker => (worker.returned, worker.buffer.length)))

end EDSL.Examples.StoreBuffer
