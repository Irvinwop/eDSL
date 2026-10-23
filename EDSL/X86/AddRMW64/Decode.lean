/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.AddRMW64.Model
import EDSL.X86.LockedAdd64.Decode

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.AddRMW64

structure Window4 where
  lock : Byte
  rex : Byte
  opcode : Byte
  modrm : Byte
  deriving DecidableEq, Repr

def Window4.bytes (window : Window4) : List Byte :=
  [window.lock, window.rex, window.opcode, window.modrm]

def IncEncoding.window (encoding : IncEncoding) : Window4 :=
  ⟨0xf0, encoding.rex, 0xff, encoding.modrm⟩

/-- Reuse the old *fetch* window, not its XADD interpretation. Its five raw
positions here are LOCK, REX, 83, ModRM, imm8 respectively. -/
def AddImm8Encoding.window (encoding : AddImm8Encoding) : LockedAdd64.Window :=
  ⟨0xf0, encoding.rex, 0x83, encoding.modrm, encoding.imm8⟩

/-- Only four executable bytes are required. Like CodeAt and fetchFive, the
window may end exactly at 2^64, but no fetched byte wraps. -/
def fetchFour (state : State) : Except Error Window4 := do
  if state.rip.toNat + 4 > 2^64 then throw (.inaccessibleInstruction state.rip)
  let lock ← fetchByte state.memory state.rip
  let rex ← fetchByte state.memory (state.rip + 1)
  let opcode ← fetchByte state.memory (state.rip + 2)
  let modrm ← fetchByte state.memory (state.rip + 3)
  return ⟨lock, rex, opcode, modrm⟩

def decodeAddWindow (window : LockedAdd64.Window) : Except Error AddImm8Encoding :=
  if admitted : window.lock = 0xf0 ∧ window.escape = 0x83 ∧
      rexBasePrefix window.rex = true ∧ LockedAdd64.indirect64 window.opcode = true ∧
      window.opcode.toNat / 8 % 8 = 0 then
    .ok ⟨window.rex, window.opcode, window.modrm,
      admitted.2.2.1, admitted.2.2.2.1, admitted.2.2.2.2⟩
  else .error .unsupportedEncoding

def decodeIncWindow (window : Window4) : Except Error IncEncoding :=
  if admitted : window.lock = 0xf0 ∧ window.opcode = 0xff ∧
      rexBasePrefix window.rex = true ∧ LockedAdd64.indirect64 window.modrm = true ∧
      window.modrm.toNat / 8 % 8 = 0 then
    .ok ⟨window.rex, window.modrm,
      admitted.2.2.1, admitted.2.2.2.1, admitted.2.2.2.2⟩
  else .error .unsupportedEncoding

theorem decodeAddWindow_self (encoding : AddImm8Encoding) :
    decodeAddWindow encoding.window = .ok encoding := by
  rcases encoding with ⟨rex, modrm, imm8, rexSupported, indirect, groupZero⟩
  simp [decodeAddWindow, AddImm8Encoding.window, rexSupported, indirect, groupZero]

theorem decodeIncWindow_self (encoding : IncEncoding) :
    decodeIncWindow encoding.window = .ok encoding := by
  rcases encoding with ⟨rex, modrm, rexSupported, indirect, groupZero⟩
  simp [decodeIncWindow, IncEncoding.window, rexSupported, indirect, groupZero]

theorem decodeAddWindow_sound {window : LockedAdd64.Window} {encoding : AddImm8Encoding}
    (decoded : decodeAddWindow window = .ok encoding) : window = encoding.window := by
  unfold decodeAddWindow at decoded
  split at decoded
  next admitted =>
    simp only [Except.ok.injEq] at decoded
    subst encoding
    rcases window with ⟨lock, rex, opcode, modrm, imm8⟩
    have lockEq : lock = 0xf0 := admitted.1
    have opcodeEq : opcode = 0x83 := admitted.2.1
    subst lock
    subst opcode
    rfl
  next => cases decoded

theorem decodeIncWindow_sound {window : Window4} {encoding : IncEncoding}
    (decoded : decodeIncWindow window = .ok encoding) : window = encoding.window := by
  unfold decodeIncWindow at decoded
  split at decoded
  next admitted =>
    simp only [Except.ok.injEq] at decoded
    subst encoding
    rcases window with ⟨lock, rex, opcode, modrm⟩
    have lockEq : lock = 0xf0 := admitted.1
    have opcodeEq : opcode = 0xff := admitted.2.1
    subst lock
    subst opcode
    rfl
  next => cases decoded

theorem fetchFour_of_code (state : State) (window : Window4)
    (code : CodeAt state.memory state.rip window.bytes) : fetchFour state = .ok window := by
  have b0 := code.2 0 window.lock (by rfl)
  have b1 := code.2 1 window.rex (by rfl)
  have b2 := code.2 2 window.opcode (by rfl)
  have b3 := code.2 3 window.modrm (by rfl)
  have bound : ¬state.rip.toNat + 4 > 2^64 := by
    have := code.1
    change state.rip.toNat + 4 ≤ 2^64 at this
    omega
  cases window
  simp_all [fetchFour]

theorem fetchFour_code {state : State} {window : Window4}
    (fetched : fetchFour state = .ok window) : CodeAt state.memory state.rip window.bytes := by
  by_cases wrap : state.rip.toNat + 4 > 2^64
  · simp [fetchFour, wrap] at fetched
  · cases b0 : fetchByte state.memory state.rip with
    | error fault => simp [fetchFour, wrap, b0] at fetched
    | ok lock =>
      cases b1 : fetchByte state.memory (state.rip + 1#64) with
      | error fault => simp [fetchFour, wrap, b0, b1] at fetched
      | ok rex =>
        cases b2 : fetchByte state.memory (state.rip + 2#64) with
        | error fault => simp [fetchFour, wrap, b0, b1, b2] at fetched
        | ok opcode =>
          cases b3 : fetchByte state.memory (state.rip + 3#64) with
          | error fault => simp [fetchFour, wrap, b0, b1, b2, b3] at fetched
          | ok modrm =>
            simp [fetchFour, wrap, b0, b1, b2, b3] at fetched
            subst window
            refine ⟨by change state.rip.toNat + 4 ≤ 2^64; omega, ?_⟩
            intro offset byte atOffset
            match offset with
            | 0 | 1 | 2 | 3 =>
              simp [Window4.bytes] at atOffset
              subst byte
              simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using (by assumption)
            | offset + 4 => simp [Window4.bytes] at atOffset

def decodeAddAt (state : State) : Except Error AddImm8Encoding := do
  decodeAddWindow (← LockedAdd64.fetchFive state)

def decodeIncAt (state : State) : Except Error IncEncoding := do
  decodeIncWindow (← fetchFour state)

theorem decodeAddAt_of_code (encoding : AddImm8Encoding) {state : State}
    (code : CodeAt state.memory state.rip (Instruction.addImm8 encoding).bytes) :
    decodeAddAt state = .ok encoding := by
  have fetched := LockedAdd64.fetchFive_of_code state encoding.window code
  simp only [decodeAddAt, fetched, ok_bind, decodeAddWindow_self]

theorem decodeIncAt_of_code (encoding : IncEncoding) {state : State}
    (code : CodeAt state.memory state.rip (Instruction.inc encoding).bytes) :
    decodeIncAt state = .ok encoding := by
  have fetched := fetchFour_of_code state encoding.window code
  simp only [decodeIncAt, fetched, ok_bind, decodeIncWindow_self]

theorem decodeAddAt_code {state : State} {encoding : AddImm8Encoding}
    (decoded : decodeAddAt state = .ok encoding) :
    CodeAt state.memory state.rip (Instruction.addImm8 encoding).bytes := by
  cases fetched : LockedAdd64.fetchFive state with
  | error fault => simp [decodeAddAt, fetched] at decoded
  | ok window =>
    have recognized : decodeAddWindow window = .ok encoding := by
      simpa only [decodeAddAt, fetched, ok_bind] using decoded
    have same := decodeAddWindow_sound recognized
    have code := LockedAdd64.fetchFive_code fetched
    simpa only [same, AddImm8Encoding.window, LockedAdd64.Window.bytes, Instruction.bytes] using code

theorem decodeIncAt_code {state : State} {encoding : IncEncoding}
    (decoded : decodeIncAt state = .ok encoding) :
    CodeAt state.memory state.rip (Instruction.inc encoding).bytes := by
  cases fetched : fetchFour state with
  | error fault => simp [decodeIncAt, fetched] at decoded
  | ok window =>
    have recognized : decodeIncWindow window = .ok encoding := by
      simpa only [decodeIncAt, fetched, ok_bind] using decoded
    have same := decodeIncWindow_sound recognized
    have code := fetchFour_code fetched
    simpa only [same, IncEncoding.window, Window4.bytes, Instruction.bytes] using code

/-- A successful third-byte probe selects the new four/five-byte form. All
other probes, including probe failure, delegate to the *unchanged eager*
legacy fetchFive/decodeAt. The probe supplies no authority: each selected
decoder fetches its entire window and checks no-wrap before recognition.
In particular INC never queries byte five. New-form errors follow that
selected decoder; there is no claim of global equality with old decoding. -/
def decodeAt (state : State) : Except Error Instruction :=
  match fetchByte state.memory (state.rip + 2) with
  | .ok opcode =>
    if opcode = 0x83 then do return .addImm8 (← decodeAddAt state)
    else if opcode = 0xff then do return .inc (← decodeIncAt state)
    else do return .xadd (← LockedAdd64.decodeAt state)
  | .error _ => do return .xadd (← LockedAdd64.decodeAt state)

theorem decodeAt_of_code (instruction : Instruction) {state : State}
    (code : CodeAt state.memory state.rip instruction.bytes) :
    decodeAt state = .ok instruction := by
  cases instruction with
  | xadd old =>
    have probe := code.2 2 0x0f (by rfl)
    have decoded := LockedAdd64.decodeAt_of_code old code
    simp [decodeAt, probe, decoded]
  | addImm8 encoding =>
    have probe := code.2 2 0x83 (by rfl)
    have decoded := decodeAddAt_of_code encoding code
    simp [decodeAt, probe, decoded]
  | inc encoding =>
    have probe := code.2 2 0xff (by rfl)
    have decoded := decodeIncAt_of_code encoding code
    simp [decodeAt, probe, decoded]

/-- Success binds the exact current bytes of the selected tag and its own
length, including all four bytes of INC and all five of XADD/ADD. -/
theorem decodeAt_code {state : State} {instruction : Instruction}
    (decoded : decodeAt state = .ok instruction) :
    CodeAt state.memory state.rip instruction.bytes := by
  cases probe : fetchByte state.memory (state.rip + 2#64) with
  | error fault =>
    cases old : LockedAdd64.decodeAt state with
    | error fault => simp [decodeAt, probe, old] at decoded
    | ok legacy =>
      simp [decodeAt, probe, old] at decoded
      subst instruction
      exact LockedAdd64.decodeAt_code old
  | ok opcode =>
    by_cases add : opcode = 0x83#8
    · cases parsed : decodeAddAt state with
      | error fault => simp [decodeAt, probe, add, parsed] at decoded
      | ok encoding =>
        simp [decodeAt, probe, add, parsed] at decoded
        subst instruction
        exact decodeAddAt_code parsed
    · by_cases inc : opcode = 0xff#8
      · cases parsed : decodeIncAt state with
        | error fault => simp [decodeAt, probe, inc, parsed] at decoded
        | ok encoding =>
          simp [decodeAt, probe, inc, parsed] at decoded
          subst instruction
          exact decodeIncAt_code parsed
      · cases old : LockedAdd64.decodeAt state with
        | error fault => simp [decodeAt, probe, add, inc, old] at decoded
        | ok legacy =>
          simp [decodeAt, probe, add, inc, old] at decoded
          subst instruction
          exact LockedAdd64.decodeAt_code old

theorem decodeAt_iff_code (instruction : Instruction) (state : State) :
    decodeAt state = .ok instruction ↔ CodeAt state.memory state.rip instruction.bytes :=
  ⟨decodeAt_code, decodeAt_of_code instruction⟩

/-- Successful current executable fetches at exactly this instruction's
offsets suffice; INC transport has no fifth-byte premise. -/
def SuccessfulFetchTransport (source destination : State) (length : Nat) : Prop :=
  ∀ offset, offset < length → ∀ byte,
    fetchByte source.memory (source.rip + BitVec.ofNat 64 offset) = .ok byte →
    fetchByte destination.memory (destination.rip + BitVec.ofNat 64 offset) = .ok byte

theorem decodeAt_transport {source destination : State} {instruction : Instruction}
    (sameRip : source.rip = destination.rip)
    (transport : SuccessfulFetchTransport source destination instruction.length)
    (decoded : decodeAt source = .ok instruction) : decodeAt destination = .ok instruction := by
  have code := decodeAt_code decoded
  apply decodeAt_of_code instruction
  refine ⟨by simpa only [sameRip] using code.1, ?_⟩
  intro offset byte atOffset
  obtain ⟨bound, _⟩ := List.getElem_of_getElem? atOffset
  exact transport offset (by simpa only [Instruction.bytes_length] using bound)
    byte (code.2 offset byte atOffset)

theorem decodeAt_preserved_by_rmw {source : State} {memory : Memory}
    {event : AtomicEvent64} {instruction : Instruction}
    (transition : RMWTransition64 source.memory event memory)
    (decoded : decodeAt source = .ok instruction)
    (disjoint : QWordDisjoint event.address source.rip instruction.length) :
    decodeAt { source with memory := memory } = .ok instruction := by
  apply decodeAt_of_code instruction
  exact transition.preserves_code _ _ (decodeAt_code decoded)
    (by simpa only [Instruction.bytes_length] using disjoint)

end EDSL.X86.AddRMW64
