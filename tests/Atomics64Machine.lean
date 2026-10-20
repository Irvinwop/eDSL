/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64
import EDSL.Audit

namespace EDSL.Tests.Atomics64Machine
open X86 OS.AddressSpace
open OS.Atomics64

/-- Owned loader bytes: a complete caller slot, strict code, and a qword with
distinct high/low halves. The oracle below uses literal results and bytes. -/
def space : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0xf0, readExecute⟩
    | 4097 => some ⟨0x48, readExecute⟩
    | 4098 => some ⟨0x09, readExecute⟩
    | 4099 => some ⟨0x37, readExecute⟩
    | 4100 => some ⟨0xc3, readExecute⟩
    | 32769 => some ⟨0x20, readOnly⟩
    | 32768 | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some ⟨0, readOnly⟩
    | 65536 => some ⟨1, readWrite⟩
    | 65537 => some ⟨0x23, readWrite⟩
    | 65538 => some ⟨0x45, readWrite⟩
    | 65539 => some ⟨0x67, readWrite⟩
    | 65540 => some ⟨0x89, readWrite⟩
    | 65541 => some ⟨0xab, readWrite⟩
    | 65542 => some ⟨0xcd, readWrite⟩
    | 65543 => some ⟨1, readWrite⟩
    | _ => none

def setup : Except OS.Atomics64.Fault (OS.Atomics64.State × HandleId64) := do
  let initial := empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty space)))
  let (owned, ticket) ← mutate initial (.adopt 7 ⟨65536, 8⟩)
  let ticket ← match ticket with
    | some ticket => pure ticket
    | none => throw .missingCell
  let (registered, cell) ← enroll owned 7 ticket 65536
  issue registered 7 cell 11

def entry (shared : OS.Atomics64.State) : X86.State where
  registers register := match register with
    | .rdi => 65536 | .rsi => 0x8020044080201010 | .rsp => 32768
    | _ => 0xdeadbeef76543210
  rip := 4096
  flags := 0xed7
  memory := toMemory shared.legacy.shared.resources.space

structure View where
  osEvent : Event
  cpuEvent : LogicalEvent64
  cpuWord : Option Word
  osWord : Option Word
  bytes : List (Option Byte)
  rax : Word
  rsp : Word
  rip : Word
  flagsWithoutAF : Word
  af : Bool
  deriving DecidableEq, Repr

/-- Both real paths start from the same CURRENT resources. RET must consume
the updated CPU memory without losing the event or changing RAX. -/
def observe (af : Bool) : Except OS.Atomics64.Fault View := do
  let (shared, handle) ← setup
  let (after, osEvent) ← logicalDiscard shared 11 handle 0x8020044080201010
  let first ← (LockedLogical64.step af (entry shared)).mapError OS.Atomics64.Fault.machine
  match first.result with
  | .returned _ => throw .missingCell
  | .atomic64 cpuEvent middle =>
    let second ← (LockedLogical64.step (!af) middle).mapError OS.Atomics64.Fault.machine
    match second.result with
    | .atomic64 _ _ => throw .missingCell
    | .returned final =>
      return ⟨osEvent, cpuEvent, (loadQWord final.memory 65536).toOption,
        (loadQWord (toMemory after.legacy.shared.resources.space) 65536).toOption,
        [65536,65537,65538,65539,65540,65541,65542,65543].map final.memory.read,
        final.registers .rax, final.registers .rsp, final.rip,
        final.flags &&& ~~~(0x10 : Word), final.flags.getLsbD 4⟩

example (af : Bool) : observe af = .ok {
    osEvent := ⟨11, ⟨0⟩, ⟨0⟩, ⟨.bor, 0x8020044080201010,
      ⟨65536, 0x01cdab8967452301, 0x81edafc9e7653311⟩⟩⟩
    cpuEvent := ⟨.bor, 0x8020044080201010,
      ⟨65536, 0x01cdab8967452301, 0x81edafc9e7653311⟩⟩
    cpuWord := some 0x81edafc9e7653311
    osWord := some 0x81edafc9e7653311
    bytes := [some 0x11, some 0x33, some 0x65, some 0xe7,
      some 0xc9, some 0xaf, some 0xed, some 0x81]
    rax := 0xdeadbeef76543210
    rsp := 32776
    rip := 8192
    flagsWithoutAF := 0x686
    af := af } := by cases af <;> rfl

end EDSL.Tests.Atomics64Machine

#audit_edsl
