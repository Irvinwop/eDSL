/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.DecodeTransport

namespace EDSL.X86.Sequential

/-- Finite candidate bytes for static decoding. Actual execution always uses
the current machine memory, related by `CodeAt` below. -/
def codeMemory (bytes : List Byte) : Memory where
  read address := bytes[address.toNat]?
  executable address := decide (address.toNat < bytes.length)

def codeState (bytes : List Byte) (offset : Nat) : State :=
  ⟨fun _ => 0, BitVec.ofNat 64 offset, 0, codeMemory bytes⟩

/-- A successful finite-code fetch transfers to current executable RAM. Failed
source fetches impose no premise, including bytes following a final RET. -/
theorem code_fetch_transport_of_bound {bytes : List Byte} {memory : Memory} {base : Word}
    (code : CodeAt memory base bytes) (size : bytes.length + 15 ≤ 2^64) (offset : Nat)
    (inside : offset < bytes.length) (state : State)
    (currentMemory : state.memory = memory) (currentPC : state.rip = base + BitVec.ofNat 64 offset) :
    SuccessfulFetchTransport (codeState bytes offset) state := by
  intro relative short byte fetched
  have offsetSmall : offset < 2^64 := by omega
  have relativeSmall : relative < 2^64 := by omega
  have totalSmall : offset + relative < 2^64 := by omega
  have natural : (BitVec.ofNat 64 offset + BitVec.ofNat 64 relative).toNat = offset + relative := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt offsetSmall, Nat.mod_eq_of_lt relativeSmall, Nat.mod_eq_of_lt totalSmall]
  change fetchByte (codeMemory bytes) (BitVec.ofNat 64 offset + BitVec.ofNat 64 relative) = .ok byte at fetched
  unfold fetchByte at fetched
  split at fetched
  next allowed =>
    cases read : (codeMemory bytes).read (BitVec.ofNat 64 offset + BitVec.ofNat 64 relative) with
    | none => simp [read] at fetched
    | some observed =>
      have same : observed = byte := Except.ok.inj (by simpa only [read] using fetched)
      subst observed
      have present : bytes[offset + relative]? = some byte := by
        simpa only [codeMemory, natural] using read
      have actual := code.2 (offset + relative) byte present
      rw [currentMemory, currentPC]
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using actual
  next => cases fetched

/-- Compatibility rule for the original 64-byte admission profile. -/
theorem code_fetch_transport {bytes : List Byte} {memory : Memory} {base : Word}
    (code : CodeAt memory base bytes) (size : bytes.length ≤ 64) (offset : Nat)
    (inside : offset < bytes.length) (state : State)
    (currentMemory : state.memory = memory) (currentPC : state.rip = base + BitVec.ofNat 64 offset) :
    SuccessfulFetchTransport (codeState bytes offset) state :=
  code_fetch_transport_of_bound code (by omega) offset inside state currentMemory currentPC

theorem code_canonical_offset {bytes : List Byte} {memory : Memory} {base : Word}
    (code : CodeAt memory base bytes) (offset : Nat) (inside : offset < bytes.length) :
    canonical (base + BitVec.ofNat 64 offset) = true := by
  let byte := bytes[offset]'inside
  have present : bytes[offset]? = some byte := List.getElem?_eq_getElem inside
  have fetched := code.2 offset byte present
  unfold fetchByte at fetched
  split at fetched
  next allowed => exact (Bool.and_eq_true_iff.mp allowed).1
  next => cases fetched

end EDSL.X86.Sequential
