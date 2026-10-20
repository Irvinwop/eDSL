/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedAdd64.Model

namespace EDSL.X86.LockedAdd64

structure Window where
  lock : Byte
  rex : Byte
  escape : Byte
  opcode : Byte
  modrm : Byte
  deriving DecidableEq, Repr

def Window.bytes (window : Window) : List Byte :=
  [window.lock, window.rex, window.escape, window.opcode, window.modrm]

def Instruction.window (instruction : Instruction) : Window :=
  ⟨0xf0, instruction.rex, 0x0f, 0xc1, instruction.modrm⟩

/-- Eagerly fetch exactly five current executable bytes. No fetched address
wraps. As in CodeAt, a window may end exactly at 2^64; the subsequent RIP is
still a Word. No padding, expected-byte oracle or source snapshot is consulted. -/
def fetchFive (state : State) : Except Error Window := do
  if state.rip.toNat + 5 > 2^64 then throw (.inaccessibleInstruction state.rip)
  let lock ← fetchByte state.memory state.rip
  let rex ← fetchByte state.memory (state.rip + 1)
  let escape ← fetchByte state.memory (state.rip + 2)
  let opcode ← fetchByte state.memory (state.rip + 3)
  let modrm ← fetchByte state.memory (state.rip + 4)
  return ⟨lock, rex, escape, opcode, modrm⟩

/-- Pure recognition is not execution authority: only decodeAt fetches code.
All other prefixes/widths/opcodes and ModRM modes fail closed. -/
def decodeWindow (window : Window) : Except Error Instruction := do
  if window.lock ≠ 0xf0 ∨ window.escape ≠ 0x0f ∨ window.opcode ≠ 0xc1 then
    throw .unsupportedEncoding
  if rexW : Sequential.rexWPrefix window.rex = true then
    if indirect : indirect64 window.modrm = true then
      return ⟨window.rex, window.modrm, rexW, indirect⟩
    else throw .unsupportedEncoding
  else throw .unsupportedEncoding

def decodeAt (state : State) : Except Error Instruction := do
  decodeWindow (← fetchFive state)

theorem decodeWindow_self (instruction : Instruction) :
    decodeWindow instruction.window = .ok instruction := by
  rcases instruction with ⟨rex, modrm, rexW, indirect⟩
  simp [decodeWindow, Instruction.window, rexW, indirect]

theorem decodeWindow_sound {window : Window} {instruction : Instruction}
    (decoded : decodeWindow window = .ok instruction) : window = instruction.window := by
  by_cases header : window.lock ≠ 0xf0#8 ∨ window.escape ≠ 0x0f#8 ∨ window.opcode ≠ 0xc1#8
  · simp [decodeWindow, header] at decoded
  · by_cases rexW : Sequential.rexWPrefix window.rex = true
    · by_cases indirect : indirect64 window.modrm = true
      · simp [decodeWindow, header, rexW, indirect] at decoded
        subst instruction
        rcases window with ⟨lock, rex, escape, opcode, modrm⟩
        simp only [not_or, ne_eq, Decidable.not_not] at header
        rcases header with ⟨rfl, rfl, rfl⟩
        rfl
      · simp [decodeWindow, header, rexW, indirect] at decoded
    · simp [decodeWindow, header, rexW] at decoded

theorem fetchFive_of_code (state : State) (window : Window)
    (code : CodeAt state.memory state.rip window.bytes) :
    fetchFive state = .ok window := by
  have b0 := code.2 0 window.lock (by rfl)
  have b1 := code.2 1 window.rex (by rfl)
  have b2 := code.2 2 window.escape (by rfl)
  have b3 := code.2 3 window.opcode (by rfl)
  have b4 := code.2 4 window.modrm (by rfl)
  have bound : ¬state.rip.toNat + 5 > 2^64 := by
    have := code.1
    change state.rip.toNat + 5 ≤ 2^64 at this
    omega
  cases window
  simp_all [fetchFive]

theorem fetchFive_code {state : State} {window : Window}
    (fetched : fetchFive state = .ok window) : CodeAt state.memory state.rip window.bytes := by
  by_cases wrap : state.rip.toNat + 5 > 2^64
  · simp [fetchFive, wrap] at fetched
  · cases b0 : fetchByte state.memory state.rip with
    | error fault => simp [fetchFive, wrap, b0] at fetched
    | ok lock =>
      cases b1 : fetchByte state.memory (state.rip + 1#64) with
      | error fault => simp [fetchFive, wrap, b0, b1] at fetched
      | ok rex =>
        cases b2 : fetchByte state.memory (state.rip + 2#64) with
        | error fault => simp [fetchFive, wrap, b0, b1, b2] at fetched
        | ok escape =>
          cases b3 : fetchByte state.memory (state.rip + 3#64) with
          | error fault => simp [fetchFive, wrap, b0, b1, b2, b3] at fetched
          | ok opcode =>
            cases b4 : fetchByte state.memory (state.rip + 4#64) with
            | error fault => simp [fetchFive, wrap, b0, b1, b2, b3, b4] at fetched
            | ok modrm =>
              simp [fetchFive, wrap, b0, b1, b2, b3, b4] at fetched
              subst window
              refine ⟨by change state.rip.toNat + 5 ≤ 2^64; omega, ?_⟩
              intro offset byte atOffset
              match offset with
              | 0 | 1 | 2 | 3 | 4 =>
                simp [Window.bytes] at atOffset
                subst byte
                simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using (by assumption)
              | offset + 5 => simp [Window.bytes] at atOffset

theorem decodeAt_of_code (instruction : Instruction) {state : State}
    (code : CodeAt state.memory state.rip instruction.bytes) :
    decodeAt state = .ok instruction := by
  have fetched := fetchFive_of_code state instruction.window code
  simp only [decodeAt, fetched, ok_bind, decodeWindow_self]

/-- The converse certifies all five actual executable bytes and no wrap. -/
theorem decodeAt_code {state : State} {instruction : Instruction}
    (decoded : decodeAt state = .ok instruction) :
    CodeAt state.memory state.rip instruction.bytes := by
  cases fetched : fetchFive state with
  | error fault => simp [decodeAt, fetched] at decoded
  | ok window =>
    have recognized : decodeWindow window = .ok instruction := by
      simpa only [decodeAt, fetched, ok_bind] using decoded
    have same := decodeWindow_sound recognized
    have code := fetchFive_code fetched
    simpa only [same, Instruction.window, Window.bytes, Instruction.bytes] using code

theorem decodeAt_iff_code (instruction : Instruction) (state : State) :
    decodeAt state = .ok instruction ↔ CodeAt state.memory state.rip instruction.bytes :=
  ⟨decodeAt_code, decodeAt_of_code instruction⟩

/-- Transport only successful current fetches, at all five offsets. The RIP
identity retains CodeAt's independent no-wrap obligation. -/
def SuccessfulFetchTransport (source destination : State) : Prop :=
  ∀ offset, offset < 5 → ∀ byte,
    fetchByte source.memory (source.rip + BitVec.ofNat 64 offset) = .ok byte →
    fetchByte destination.memory (destination.rip + BitVec.ofNat 64 offset) = .ok byte

theorem decodeAt_transport {source destination : State} {instruction : Instruction}
    (sameRip : source.rip = destination.rip)
    (transport : SuccessfulFetchTransport source destination)
    (decoded : decodeAt source = .ok instruction) : decodeAt destination = .ok instruction := by
  have code := decodeAt_code decoded
  apply decodeAt_of_code instruction
  refine ⟨by simpa only [sameRip] using code.1, ?_⟩
  intro offset byte atOffset
  obtain ⟨bound, _⟩ := List.getElem_of_getElem? atOffset
  have length : instruction.bytes.length = 5 := rfl
  exact transport offset (by omega) byte (code.2 offset byte atOffset)

/-- Reuse the memory primitive's code frame when transporting a decoded
instruction across an independent, disjoint full-width RMW. -/
theorem decodeAt_preserved_by_rmw {source : State} {memory : Memory}
    {event : AtomicEvent64} {instruction : Instruction}
    (transition : RMWTransition64 source.memory event memory)
    (decoded : decodeAt source = .ok instruction)
    (disjoint : QWordDisjoint event.address source.rip instruction.length) :
    decodeAt { source with memory := memory } = .ok instruction := by
  apply decodeAt_of_code instruction
  exact transition.preserves_code _ _ (decodeAt_code decoded) disjoint

end EDSL.X86.LockedAdd64
