/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory64
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.Memory64
open X86

/-- A literal byte layout independent of the store's slicing and join logic. -/
def bytes : Memory where
  read address := match address.toNat with
    | 8193 => some 0xef | 8194 => some 0xcd | 8195 => some 0xab | 8196 => some 0x89
    | 8197 => some 0x67 | 8198 => some 0x45 | 8199 => some 0x23 | 8200 => some 0xf1
    | _ => some 0x5a
  executable := fun address => decide (address.toNat < 4096)
  writable := fun address => decide (8193 ≤ address.toNat ∧ address.toNat < 8201)

-- The unaligned ordinary operand retains every high bit and little-endian order.
example : loadQWord bytes 8193 = .ok 0xf123456789abcdef := by rfl
example : readWord bytes 8193 = .ok 0xf123456789abcdef := by rfl

/-- Inspect the actual checked store, without first reading it through the
same joining routine. Both adjacent bytes and the high four bytes are visible. -/
def storeView : Except Error (List (Option Byte) × Bool × Bool × Bool × Bool) := do
  let memory ← storeQWord bytes 8193 0x80fedcba98765432
  return ([memory.read 8192, memory.read 8193, memory.read 8194, memory.read 8195,
    memory.read 8196, memory.read 8197, memory.read 8198, memory.read 8199,
    memory.read 8200, memory.read 8201], memory.executable 42, memory.executable 8193,
    memory.writable 8200, memory.writable 8201)

example : storeView = .ok
    ([some 0x5a, some 0x32, some 0x54, some 0x76, some 0x98, some 0xba,
      some 0xdc, some 0xfe, some 0x80, some 0x5a], true, false, true, false) := by rfl

-- Denying any of the upper four bytes must reject the entire store. This
-- catches accidentally reusing the four-byte preflight or truncating the word.
example : ([8197, 8198, 8199, 8200] : List Word).map (fun denied =>
    (storeQWord { bytes with writable := fun address => address != denied }
      8193 0x80fedcba98765432).map (fun _ => true)) =
    [.error (.writeDenied 8193), .error (.writeDenied 8193),
      .error (.writeDenied 8193), .error (.writeDenied 8193)] := by rfl

example : ([8197, 8198, 8199, 8200] : List Word).map (fun missing =>
    (storeQWord { bytes with read := fun address =>
      if address = missing then none else bytes.read address } 8193 42).map (fun _ => true)) =
    [.error (.writeDenied 8193), .error (.writeDenied 8193),
      .error (.writeDenied 8193), .error (.writeDenied 8193)] := by rfl

example : ([8197, 8198, 8199, 8200] : List Word).map (fun missing =>
    loadQWord { bytes with read := fun address =>
      if address = missing then none else bytes.read address } 8193) =
    [.error (.inaccessibleData 8197), .error (.inaccessibleData 8198),
      .error (.inaccessibleData 8199), .error (.inaccessibleData 8200)] := by rfl

def mapped : Memory where
  read := fun _ => some 0
  executable := fun _ => true
  writable := fun _ => true

-- Nonwrap and every-byte canonicality are independent of permission maps.
example : loadQWord mapped 0xfffffffffffffffa =
    .error (.inaccessibleData 0xfffffffffffffffa) := by rfl
example : (storeQWord mapped 0xfffffffffffffffa 42).map (fun _ => true) =
    .error (.writeDenied 0xfffffffffffffffa) := by rfl
example : loadQWord mapped 0x7ffffffffffc =
    .error (.inaccessibleData 0x800000000000) := by rfl
example : (storeQWord mapped 0x7ffffffffffc 42).map (fun _ => true) =
    .error (.writeDenied 0x7ffffffffffc) := by rfl
example : loadQWord mapped 0x800000000000 =
    .error (.inaccessibleData 0x800000000000) := by rfl
example : loadQWord mapped 0xfffffffffffffff8 = .ok 0 := by rfl

-- An eight-byte read at an unmapped address has DATA provenance; RET keeps
-- its existing STACK provenance for the same memory and operand.
example : loadQWord { mapped with read := fun _ => none } 8193 =
    .error (.inaccessibleData 8193) := by rfl
example : readWord { mapped with read := fun _ => none } 8193 =
    .error (.inaccessibleStack 8193) := by rfl

end EDSL.Tests.Memory64

#audit_edsl
