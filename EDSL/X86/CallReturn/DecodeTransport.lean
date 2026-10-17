/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.CallReturn.Decode
import EDSL.X86.Sequential.Code

namespace EDSL.X86.CallReturn

abbrev SuccessfulFetchTransport := Sequential.SuccessfulFetchTransport

private abbrev SuccessRefines (source destination : Except Error α) : Prop :=
  ∀ value, source = .ok value → destination = .ok value

private theorem SuccessRefines.refl (result : Except Error α) : SuccessRefines result result := fun _ h => h

private theorem SuccessRefines.error (left right : Error) :
    SuccessRefines (.error left : Except Error α) (.error right) := by intro _ h; cases h

private theorem SuccessRefines.bind {source destination : Except Error α}
    {left right : α → Except Error β} (first : SuccessRefines source destination)
    (rest : ∀ value, SuccessRefines (left value) (right value)) :
    SuccessRefines (source >>= left) (destination >>= right) := by
  intro value success
  cases fetched : source with
  | error fault => simp only [fetched, error_bind, reduceCtorEq] at success
  | ok byte =>
    rw [first byte fetched, ok_bind]
    exact rest byte value (by simpa only [fetched, ok_bind] using success)

private theorem SuccessRefines.ite (condition : Prop) [Decidable condition]
    {a b c d : Except Error α} (yes : SuccessRefines a b) (no : SuccessRefines c d) :
    SuccessRefines (if condition then a else c) (if condition then b else d) := by split <;> assumption

private theorem decodeLeaAt_refines {source destination : State} (rex : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeLeaAt source rex) (decodeLeaAt destination rex) := by
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  unfold decodeLeaAt
  apply SuccessRefines.bind t2
  intro modrm
  apply SuccessRefines.ite
  · exact SuccessRefines.refl _
  · apply SuccessRefines.ite
    · apply SuccessRefines.bind t3
      intro sibByte
      apply SuccessRefines.bind t4
      intro displacement
      exact SuccessRefines.refl _
    · apply SuccessRefines.bind t3
      intro displacement
      exact SuccessRefines.refl _

/-- Only successfully fetched instruction bytes matter. The fallback error can
change; it cannot produce a successful extension decoding. -/
theorem decodeNewAt_transport {source destination : State} {instruction : Instruction}
    (left right : Error) (transport : SuccessfulFetchTransport source destination)
    (decoded : decodeNewAt source left = .ok instruction) :
    decodeNewAt destination right = .ok instruction := by
  have t0 := transport 0 (by decide)
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  simp only [BitVec.add_zero] at t0
  have refinement : SuccessRefines (decodeNewAt source left) (decodeNewAt destination right) := by
    unfold decodeNewAt
    apply SuccessRefines.bind t0
    intro opcode
    apply SuccessRefines.ite
    · apply SuccessRefines.bind t1
      intro b0
      apply SuccessRefines.bind t2
      intro b1
      apply SuccessRefines.bind t3
      intro b2
      apply SuccessRefines.bind t4
      intro b3
      exact SuccessRefines.refl _
    · apply SuccessRefines.ite
      · exact SuccessRefines.refl _
      · apply SuccessRefines.ite
        · apply SuccessRefines.bind t1
          intro operation
          apply SuccessRefines.ite
          · exact SuccessRefines.refl _
          · apply SuccessRefines.ite
            · exact decodeLeaAt_refines _ transport
            · exact SuccessRefines.refl _
        · exact SuccessRefines.error _ _
  exact refinement instruction decoded

private theorem byte_ne_outside {byte : Byte} {low high value : Nat}
    (lower : low ≤ byte.toNat) (upper : byte.toNat ≤ high) (bound : value < 256)
    (outside : value < low ∨ high < value) : byte ≠ BitVec.ofNat 8 value := by
  intro equal
  have same := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at same
  omega

/-- The legacy decoder has no opcode in either the REX or stack-register
range. Keep the byte symbolic: normalizing its decoder once avoids a Cartesian
product of prefix and opcode cases. -/
private theorem legacy_rejects_rex_stack {state : State} {opcode : Byte}
    (fetched : fetchByte state.memory state.rip = .ok opcode)
    (lower : 0x40 ≤ opcode.toNat) (upper : opcode.toNat ≤ 0x5f) :
    X86.decodeAt state = .error (.unsupportedOpcode opcode) := by
  have outside {value : Nat} := @byte_ne_outside opcode 0x40 0x5f value lower upper
  simp only [X86.decodeAt, fetched, ok_bind]
  simp [outside (by decide : 0xc3 < 256) (by decide),
    outside (by decide : 0x8d < 256) (by decide),
    outside (by decide : 0x8b < 256) (by decide),
    outside (by decide : 0x89 < 256) (by decide),
    outside (by decide : 0x87 < 256) (by decide),
    outside (by decide : 0xf0 < 256) (by decide),
    outside (by decide : 0xe3 < 256) (by decide),
    outside (by decide : 0xe2 < 256) (by decide),
    outside (by decide : 0x75 < 256) (by decide),
    outside (by decide : 0x83 < 256) (by decide),
    outside (by decide : 0xb8 < 256) (by decide),
    outside (by decide : 0xba < 256) (by decide),
    outside (by decide : 0xbe < 256) (by decide),
    outside (by decide : 0xbf < 256) (by decide),
    outside (by decide : 0x0f < 256) (by decide)]

/-- Outside REX.W the sequential decoder also has no opcode in 40..5F. -/
private theorem sequential_rex_stack {state : State} {opcode : Byte}
    (fetched : fetchByte state.memory state.rip = .ok opcode)
    (lower : 0x40 ≤ opcode.toNat) (upper : opcode.toNat ≤ 0x5f) :
    Sequential.decodeAt state =
      if Sequential.rexWPrefix opcode then Sequential.decodeREXWAt state opcode
      else .error (.unsupportedOpcode opcode) := by
  have outside {value : Nat} := @byte_ne_outside opcode 0x40 0x5f value lower upper
  have notJcc : ¬(0x70 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x7f ∧ opcode ≠ 0x75#8) := by omega
  rw [Sequential.decodeAt, legacy_rejects_rex_stack fetched lower upper]
  simp [Sequential.decodeNewAt, fetched, notJcc,
    outside (by decide : 0x31 < 256) (by decide),
    outside (by decide : 0x03 < 256) (by decide),
    outside (by decide : 0x89 < 256) (by decide),
    outside (by decide : 0x8b < 256) (by decide),
    outside (by decide : 0x74 < 256) (by decide),
    outside (by decide : 0xeb < 256) (by decide)]

private theorem stack_not_rexW {opcode : Byte} (stack : stackOpcode opcode = true) :
    Sequential.rexWPrefix opcode = false := by
  have range : 0x50 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x5f := of_decide_eq_true stack
  have outside {value : Nat} := @byte_ne_outside opcode 0x50 0x5f value range.1 range.2
  simp [Sequential.rexWPrefix,
    outside (by decide : 0x48 < 256) (by decide),
    outside (by decide : 0x49 < 256) (by decide),
    outside (by decide : 0x4a < 256) (by decide),
    outside (by decide : 0x4b < 256) (by decide),
    outside (by decide : 0x4c < 256) (by decide),
    outside (by decide : 0x4d < 256) (by decide),
    outside (by decide : 0x4e < 256) (by decide),
    outside (by decide : 0x4f < 256) (by decide)]

/-- Every REX.W stack opcode is rejected uniformly, independently of all
prefix register bits. The unsupported family never fetches a ModRM byte. -/
private theorem rexW_rejects_stack {state : State} (rex : Byte) {opcode : Byte}
    (fetched : fetchByte state.memory (state.rip + 1#64) = .ok opcode)
    (stack : stackOpcode opcode = true) :
    Sequential.decodeREXWAt state rex = .error .unsupportedEncoding := by
  have range : 0x50 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x5f := of_decide_eq_true stack
  have outside {value : Nat} := @byte_ne_outside opcode 0x50 0x5f value range.1 range.2
  have notXchg : ¬(0x90 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x97) := by omega
  simp [Sequential.decodeREXWAt, fetched, notXchg,
    outside (by decide : 0x0f < 256) (by decide),
    outside (by decide : 0x87 < 256) (by decide),
    outside (by decide : 0x89 < 256) (by decide),
    outside (by decide : 0x8b < 256) (by decide),
    outside (by decide : 0x8d < 256) (by decide),
    outside (by decide : 0x01 < 256) (by decide),
    outside (by decide : 0x03 < 256) (by decide),
    outside (by decide : 0x21 < 256) (by decide),
    outside (by decide : 0x23 < 256) (by decide),
    outside (by decide : 0x09 < 256) (by decide),
    outside (by decide : 0x0b < 256) (by decide),
    outside (by decide : 0x31 < 256) (by decide),
    outside (by decide : 0x33 < 256) (by decide),
    outside (by decide : 0x85 < 256) (by decide),
    outside (by decide : 0x39 < 256) (by decide),
    outside (by decide : 0x83 < 256) (by decide),
    outside (by decide : 0xff < 256) (by decide)]

private theorem rexW_rejects_lea_modOne {state : State} (rex : Byte) {modrm : Byte}
    (operation : fetchByte state.memory (state.rip + 1#64) = .ok 0x8d#8)
    (fetched : fetchByte state.memory (state.rip + 2#64) = .ok modrm)
    (modOne : modrm.toNat / 64 = 1) :
    Sequential.decodeREXWAt state rex = .error .unsupportedEncoding := by
  have lower : 64 ≤ modrm.toNat := by omega
  simp [Sequential.decodeREXWAt, Sequential.decodeQWordAddressAt, operation, fetched, lower]

/-- Successful extension encodings are structurally rejected by the untouched
sequential decoder. Prefix/mod restrictions, rather than a client callback,
establish disjointness even for the overlapping REX.W LEA opcode. -/
theorem decodeNewAt_rejects_sequential {state : State} {fallback : Error} {instruction : Instruction}
    (decoded : decodeNewAt state fallback = .ok instruction) :
    Sequential.decodeAt state = .error .unsupportedEncoding ∨
      ∃ opcode, Sequential.decodeAt state = .error (.unsupportedOpcode opcode) := by
  cases fetched : fetchByte state.memory state.rip with
  | error fault => simp [decodeNewAt, fetched] at decoded
  | ok opcode =>
    by_cases call : opcode = 0xe8#8
    · subst opcode
      simp [Sequential.decodeAt, X86.decodeAt, Sequential.decodeNewAt, fetched]
    · by_cases stack : stackOpcode opcode = true
      · have range : 0x50 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x5f := of_decide_eq_true stack
        exact Or.inr ⟨opcode, by
          rw [sequential_rex_stack fetched (by omega) range.2, stack_not_rexW stack]
          rfl⟩
      · by_cases rex : rexPrefix opcode = true
        · cases operationFetched : fetchByte state.memory (state.rip + 1#64) with
          | error fault => simp [decodeNewAt, fetched, call, stack, rex, operationFetched] at decoded
          | ok operation =>
            by_cases operationStack : stackOpcode operation = true
            · have range : 0x40 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x4f := of_decide_eq_true rex
              rw [sequential_rex_stack fetched range.1 (by omega)]
              cases rexW : Sequential.rexWPrefix opcode
              · exact Or.inr ⟨opcode, rfl⟩
              · exact Or.inl (rexW_rejects_stack opcode operationFetched operationStack)
            · by_cases lea : (Sequential.rexWPrefix opcode && operation == 0x8d#8) = true
              · have parts := Bool.and_eq_true_iff.mp lea
                have operationIs : operation = 0x8d#8 := by simpa using parts.2
                subst operation
                have leaDecoded : decodeLeaAt state opcode = .ok instruction := by
                  simpa only [decodeNewAt, BitVec.ofNat_eq_ofNat, fetched, ok_bind, ite_eq_right call,
                    ite_eq_right stack, ite_eq_left rex, operationFetched,
                    ite_eq_right operationStack, ite_eq_left lea] using decoded
                cases modrmFetched : fetchByte state.memory (state.rip + 2#64) with
                | error fault => simp [decodeLeaAt, modrmFetched] at leaDecoded
                | ok modrm =>
                  have modOne : modrm.toNat / 64 = 1 := by
                    by_cases equal : modrm.toNat / 64 = 1
                    · exact equal
                    · simp [decodeLeaAt, modrmFetched, equal] at leaDecoded
                  have range : 0x40 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x4f := of_decide_eq_true rex
                  exact Or.inl (by
                    rw [sequential_rex_stack fetched range.1 (by omega), parts.1]
                    exact rexW_rejects_lea_modOne opcode operationFetched modrmFetched modOne)
              · simp only [decodeNewAt, BitVec.ofNat_eq_ofNat, fetched, ok_bind, ite_eq_right call,
                  ite_eq_right stack, ite_eq_left rex, operationFetched,
                  ite_eq_right operationStack, ite_eq_right lea, reduceCtorEq] at decoded
        · simp [decodeNewAt, fetched, call, stack, rex] at decoded

/-- Extension successes really pass through the public old-first decoder. -/
theorem decodeNewAt_admitted {state : State} {fallback : Error} {instruction : Instruction}
    (decoded : decodeNewAt state fallback = .ok instruction) : decodeAt state = .ok instruction := by
  rcases decodeNewAt_rejects_sequential decoded with rejected | ⟨opcode, rejected⟩
  · rw [decodeAt, rejected]
    exact decodeNewAt_transport _ _ (fun _ _ _ h => h) decoded
  · rw [decodeAt, rejected]
    exact decodeNewAt_transport _ _ (fun _ _ _ h => h) decoded

/-- Any successful decode transfers on its actual successful fetches below five;
bytes after a final RET impose no premise. The old-first selection is retained. -/
theorem decodeAt_transport {source destination : State} {instruction : Instruction}
    (transport : SuccessfulFetchTransport source destination)
    (decoded : decodeAt source = .ok instruction) : decodeAt destination = .ok instruction := by
  cases old : Sequential.decodeAt source with
  | ok oldInstruction =>
    have same : Instruction.sequential oldInstruction = instruction := by simpa [decodeAt, old] using decoded
    rw [← same]
    exact decodeAt_sequential (Sequential.decodeAt_transport transport old)
  | error fault =>
    cases fault <;> simp only [decodeAt, old] at decoded
    all_goals first
      | cases decoded
      | exact decodeNewAt_admitted (decodeNewAt_transport _ .unsupportedEncoding transport decoded)

/-- Static finite-window decoding is bound to current executable RAM by CodeAt.
The entry offset may follow helper-prefix bytes; it need not be zero. -/
theorem decodeAt_code {bytes : List Byte} {memory : Memory} {base : Word} {offset : Nat}
    {instruction : Instruction} (code : CodeAt memory base bytes) (size : bytes.length ≤ 64)
    (inside : offset < bytes.length) (state : State) (currentMemory : state.memory = memory)
    (currentPC : state.rip = base + BitVec.ofNat 64 offset)
    (decoded : decodeAt (Sequential.codeState bytes offset) = .ok instruction) :
    decodeAt state = .ok instruction :=
  decodeAt_transport (Sequential.code_fetch_transport code size offset inside state currentMemory currentPC) decoded

/-- E8 consumes exactly five executable bytes and joins its immediate in little
endian order. Signed interpretation is deferred to the 64-bit call target. -/
theorem decodeAt_call_bytes {state : State} (b0 b1 b2 b3 : Byte)
    (opcode : fetchByte state.memory state.rip = .ok 0xe8#8)
    (f0 : fetchByte state.memory (state.rip + 1#64) = .ok b0)
    (f1 : fetchByte state.memory (state.rip + 2#64) = .ok b1)
    (f2 : fetchByte state.memory (state.rip + 3#64) = .ok b2)
    (f3 : fetchByte state.memory (state.rip + 4#64) = .ok b3) :
    decodeAt state = .ok (.callRelative32 (joinDWord b0 b1 b2 b3)) :=
  decodeNewAt_admitted (fallback := .unsupportedEncoding) (by simp [decodeNewAt, opcode, f0, f1, f2, f3])

end EDSL.X86.CallReturn
