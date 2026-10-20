/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory

namespace EDSL.Grading.Hex
open X86

def digit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)

/-- Canonical lower-case hexadecimal; no separators or alternate spellings. -/
def nibble (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else none

def encodeChars : List Byte → List Char
  | [] => []
  | b :: rest => digit (b.toNat / 16) :: digit (b.toNat % 16) :: encodeChars rest

def decodeChars : List Char → Option (List Byte)
  | [] => some []
  | a :: b :: rest => do
      let hi ← nibble a
      let lo ← nibble b
      let tail ← decodeChars rest
      return BitVec.ofNat 8 (hi * 16 + lo) :: tail
  | [_] => none

def encode (bytes : List Byte) : String := String.ofList (encodeChars bytes)
def decode (text : String) : Option (List Byte) := decodeChars text.toList

private theorem pair_roundtrip : ∀ b : Byte,
    (do let hi ← nibble (digit (b.toNat / 16))
        let lo ← nibble (digit (b.toNat % 16))
        pure (BitVec.ofNat 8 (hi * 16 + lo))) = some b := by decide

theorem decodeChars_encodeChars (bytes : List Byte) :
    decodeChars (encodeChars bytes) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    have pair := pair_roundtrip b
    cases hi : nibble (digit (b.toNat / 16)) <;>
      cases lo : nibble (digit (b.toNat % 16)) <;>
      simp_all [decodeChars, encodeChars]

theorem decode_encode (bytes : List Byte) : decode (encode bytes) = some bytes := by
  simpa [decode, encode] using decodeChars_encodeChars bytes

/-- Compact trusted expression representation. Artifact admission uses `decode`
and rejects failure; this total helper alone is never an admission check. -/
def literal (text : String) : List Byte := (decode text).getD []

theorem literal_encode (bytes : List Byte) : literal (encode bytes) = bytes := by
  simp [literal, decode_encode]

end EDSL.Grading.Hex
