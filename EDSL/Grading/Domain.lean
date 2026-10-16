/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Pair32.Resources
import EDSL.Stride32.Resources

set_option warningAsError true

namespace EDSL.Grading.Domain
open X86 OS OS.AddressSpace OS.ArrayResources

/-- Current resource evidence is independent of candidate execution. -/
structure PairWitness (bytes : List Byte) where
  shared : Borrowing.State
  callA : Call
  callB : Call
  initial : X86.State
  code : callA.bytes = bytes
  admitted : Pair32.PairAdmission shared callA callB initial
  entry : initial.rip = callA.code
  stack : initial.registers .rsp = callA.stack
  baseA : initial.registers .rdi = callA.base
  countA : initial.registers .rsi = BitVec.ofNat 64 callA.values.length
  baseB : initial.registers .rdx = callB.base
  countB : initial.registers .rcx = BitVec.ofNat 64 callB.values.length
  usefulA : callA.values ≠ []
  usefulB : callB.values ≠ []

/-- The complete contiguous array includes the ignored odd-index words. -/
structure StrideWitness (bytes : List Byte) where
  shared : Borrowing.State
  call : Call
  initial : X86.State
  count : Nat
  code : call.bytes = bytes
  admitted : Admission shared call initial
  entry : initial.rip = call.code
  stack : initial.registers .rsp = call.stack
  base : initial.registers .rdi = call.base
  length : call.values.length = 2 * count
  counter : initial.registers .rsi = BitVec.ofNat 64 count
  useful : 0 < count

def valuesA : List (BitVec 32) := [0xffffffff, 0xdeadbeef, 2, 11]
def valuesB : List (BitVec 32) := [3, 5]

def codeRegion (bytes : List Byte) : Region := ⟨4096, bytes.length⟩
def stackRegion : Region := ⟨65544, 8⟩
def regionA : Region := ⟨131072, 16⟩
def regionB : Region := ⟨196608, 8⟩

/-- Loader-installed, finite ordinary RAM. Data bytes are fixed independently
of code, decoding, graph import, and the mathematical output contracts. -/
def payload : Space where
  cells address :=
    if stackRegion.Contains address then
      some ⟨if address.toNat = 65545 then 0x20 else 0, readOnly⟩
    else if regionA.Contains address then
      some ⟨([0xff, 0xff, 0xff, 0xff, 0xef, 0xbe, 0xad, 0xde,
        2, 0, 0, 0, 11, 0, 0, 0] : List Byte)[address.toNat - 131072]?.getD 0, readOnly⟩
    else if regionB.Contains address then
      some ⟨([3, 0, 0, 0, 5, 0, 0, 0] : List Byte)[address.toNat - 196608]?.getD 0,
        readOnly⟩
    else none

/-- Numeric byte lookup installs the entire selected span, without interpreting
any byte as an instruction or searching for a return instruction. -/
def space (bytes : List Byte) : Space where
  cells address :=
    if (codeRegion bytes).Contains address then
      (bytes[address.toNat - 4096]?).map fun byte => ⟨byte, readExecute⟩
    else payload.cells address

theorem code_cell (bytes : List Byte) (address : Word)
    (inside : (codeRegion bytes).Contains address) :
    ∃ byte, (space bytes).cells address = some ⟨byte, readExecute⟩ := by
  have index : address.toNat - 4096 < bytes.length := by
    change 4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length at inside
    omega
  have present : (bytes[address.toNat - 4096]?).isSome = true := by simpa using index
  obtain ⟨byte, found⟩ := Option.isSome_iff_exists.mp present
  exact ⟨byte, by simp [space, inside, found]⟩

private theorem payload_no_execute (address : Word) :
    (toMemory payload).executable address = false := by
  dsimp only [toMemory, payload]
  by_cases stack : stackRegion.Contains address
  · rw [ite_eq_left stack]; rfl
  · rw [ite_eq_right stack]
    by_cases first : regionA.Contains address
    · rw [ite_eq_left first]; rfl
    · rw [ite_eq_right first]
      by_cases second : regionB.Contains address
      · rw [ite_eq_left second]; rfl
      · rw [ite_eq_right second]

/-- The current executable map is exactly the finite selected code interval;
the stack and inputs do not acquire execution permission. -/
theorem executable_iff (bytes : List Byte) (address : Word) :
    (toMemory (space bytes)).executable address = true ↔
      (codeRegion bytes).Contains address := by
  by_cases inside : (codeRegion bytes).Contains address
  · obtain ⟨byte, found⟩ := code_cell bytes address inside
    constructor
    · intro _; exact inside
    · intro _; dsimp only [toMemory]; rw [found]; rfl
  · have unchanged : (space bytes).cells address = payload.cells address := by
      simp [space, inside]
    have inactive : (toMemory (space bytes)).executable address = false := by
      dsimp only [toMemory]
      rw [unchanged]
      exact payload_no_execute address
    simp only [inactive, Bool.false_eq_true, inside]

/-- Every selected byte is a current readable/executable cell. The 4096-byte
bound is an artifact bound, independent of the smaller CFG importer bound. -/
theorem code_current (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    CodeAt (toMemory (space bytes)) 4096 bytes := by
  refine ⟨by change 4096 + bytes.length ≤ 2^64; omega, ?_⟩
  intro offset byte present
  have inside : offset < bytes.length := by
    have someAt : bytes[offset]?.isSome = true := by simp [present]
    simpa using someAt
  have small : offset < 2^64 := by omega
  have total : 4096 + offset < 2^64 := by omega
  have natural : ((4096 : Word) + BitVec.ofNat 64 offset).toNat = 4096 + offset := by
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
      Nat.mod_eq_of_lt total]
  have inCode : (codeRegion bytes).Contains (4096 + BitVec.ofNat 64 offset) := by
    change 4096 ≤ _ ∧ _ < 4096 + bytes.length
    rw [natural]
    omega
  have cell : (space bytes).cells (4096 + BitVec.ofNat 64 offset) =
      some ⟨byte, readExecute⟩ := by
    dsimp only [space]
    rw [ite_eq_left inCode, natural]
    simp only [Nat.add_sub_cancel_left, present, Option.map_some]
  have canonicalAt : canonical ((4096 : Word) + BitVec.ofNat 64 offset) = true := by
    simp only [canonical, natural, decide_eq_true_eq]
    exact Or.inl (by omega)
  have current : (toMemory (space bytes)).read (4096 + BitVec.ofNat 64 offset) =
      some byte := by dsimp only [toMemory]; rw [cell]; rfl
  have executable : (toMemory (space bytes)).executable
      (4096 + BitVec.ofNat 64 offset) = true := by dsimp only [toMemory]; rw [cell]; rfl
  change fetchByte (toMemory (space bytes)) (4096 + BitVec.ofNat 64 offset) = .ok byte
  rw [fetchByte, canonicalAt, executable]
  change (match (toMemory (space bytes)).read (4096 + BitVec.ofNat 64 offset) with
    | some value => Except.ok value
    | none => Except.error (Error.inaccessibleInstruction _)) = .ok byte
  rw [current]

theorem cells_far (bytes : List Byte) (bound : bytes.length ≤ 4096) (address : Word)
    (far : 8192 ≤ address.toNat) : (space bytes).cells address = payload.cells address := by
  have outside : ¬(codeRegion bytes).Contains address := by
    change ¬(4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)
    omega
  simp [space, outside]

theorem memory_agrees_far (bytes : List Byte) (bound : bytes.length ≤ 4096)
    (base : Word) (length : Nat) (far : 8192 ≤ base.toNat)
    (span : base.toNat + length ≤ 2^64) :
    MemoryAgreesOn (toMemory (space bytes)) (toMemory payload) base length := by
  intro offset inside
  have small : offset < 2^64 := by omega
  have total : base.toNat + offset < 2^64 := by omega
  have natural : (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
      Nat.mod_eq_of_lt total]
  simp only [toMemory, cells_far bytes bound _ (by rw [natural]; omega)]

theorem arrayA_current (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    ArrayAt (toMemory (space bytes)) 131072 valuesA := by
  intro index value present
  match index with
  | 0 | 1 | 2 | 3 =>
    simp [valuesA] at present
    subst value
    rw [loadDWord_congr _ (toMemory payload) _
      (memory_agrees_far bytes bound _ 4 (by decide) (by decide))]
    rfl
  | index + 4 => simp [valuesA] at present

theorem arrayB_current (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    ArrayAt (toMemory (space bytes)) 196608 valuesB := by
  intro index value present
  match index with
  | 0 | 1 =>
    simp [valuesB] at present
    subst value
    rw [loadDWord_congr _ (toMemory payload) _
      (memory_agrees_far bytes bound _ 4 (by decide) (by decide))]
    rfl
  | index + 2 => simp [valuesB] at present

theorem stack_current (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    readWord (toMemory (space bytes)) 65544 = .ok 8192 := by
  rw [readWord_congr _ (toMemory payload) _
    (memory_agrees_far bytes bound _ 8 (by decide) (by decide))]
  rfl

def region (bytes : List Byte) : Nat → Region
  | 0 => codeRegion bytes
  | 1 => stackRegion
  | 2 => regionA
  | _ => regionB

/-- Four current disjoint allocations. Well-formedness below proves validity
and actual mappedness of every cell; this is not an assumed snapshot. -/
def world (bytes : List Byte) : Ownership.World where
  space := space bytes
  frontier := 4
  allocations identifier :=
    if identifier < 4 then some ⟨7, 0, region bytes identifier⟩ else none

def loan (bytes : List Byte) (identifier : Nat) : Borrowing.Loan :=
  ⟨⟨identifier, 0⟩, 7, 11, region bytes identifier⟩

def shared (bytes : List Byte) : Borrowing.State where
  resources := world bytes
  nextLoan := 4
  loans identifier := if identifier < 4 then some (loan bytes identifier) else none

private theorem four_cases (identifier : Nat) (bound : identifier < 4) :
    identifier = 0 ∨ identifier = 1 ∨ identifier = 2 ∨ identifier = 3 := by omega

theorem region_valid (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (identifier : Nat) (below : identifier < 4) :
    (region bytes identifier).valid = true := by
  rcases four_cases identifier below with rfl | rfl | rfl | rfl
  · simp only [region, codeRegion, Region.valid, decide_eq_true_eq]
    change 0 < bytes.length ∧ 4096 + bytes.length ≤ 2^64 ∧
      (4096 + bytes.length ≤ 2^47 ∨ 2^64 - 2^47 ≤ 4096)
    omega
  · change stackRegion.valid = true; decide
  · change regionA.valid = true; decide
  · change regionB.valid = true; decide

theorem region_readable (bytes : List Byte) (bound : bytes.length ≤ 4096)
    (identifier : Nat) (below : identifier < 4) (address : Word)
    (inside : (region bytes identifier).Contains address) :
    ∃ cell, (space bytes).cells address = some cell ∧ cell.permissions.readable = true := by
  rcases four_cases identifier below with rfl | rfl | rfl | rfl
  · obtain ⟨byte, found⟩ := code_cell bytes address inside
    exact ⟨⟨byte, readExecute⟩, found, rfl⟩
  all_goals
    have far : 8192 ≤ address.toNat := by
      simp [region, stackRegion, regionA, regionB, Region.Contains] at inside
      omega
    rw [cells_far bytes bound address far]
  · dsimp only [payload]
    rw [ite_eq_left (show stackRegion.Contains address from inside)]
    exact ⟨_, rfl, rfl⟩
  · have outside : ¬stackRegion.Contains address := by
      change ¬(65544 ≤ address.toNat ∧ address.toNat < 65544 + 8)
      change 131072 ≤ address.toNat ∧ address.toNat < 131072 + 16 at inside
      omega
    dsimp only [payload]
    rw [ite_eq_right outside, ite_eq_left (show regionA.Contains address from inside)]
    exact ⟨_, rfl, rfl⟩
  · have outsideStack : ¬stackRegion.Contains address := by
      change ¬(65544 ≤ address.toNat ∧ address.toNat < 65544 + 8)
      change 196608 ≤ address.toNat ∧ address.toNat < 196608 + 8 at inside
      omega
    have outsideA : ¬regionA.Contains address := by
      change ¬(131072 ≤ address.toNat ∧ address.toNat < 131072 + 16)
      change 196608 ≤ address.toNat ∧ address.toNat < 196608 + 8 at inside
      omega
    dsimp only [payload]
    rw [ite_eq_right outsideStack, ite_eq_right outsideA,
      ite_eq_left (show regionB.Contains address from inside)]
    exact ⟨_, rfl, rfl⟩

theorem world_valid (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) : Ownership.WellFormed (world bytes) := by
  constructor
  · intro identifier allocation found
    by_cases below : identifier < 4
    · simp only [world, below, ↓reduceIte, Option.some.injEq] at found
      subst allocation
      refine ⟨below, region_valid bytes positive bound identifier below, ?_⟩
      intro address inside
      obtain ⟨cell, present, _⟩ := region_readable bytes bound identifier below address inside
      exact ⟨cell, present⟩
    · simp [world, below] at found
  · intro left a right b foundA foundB different
    by_cases belowA : left < 4
    · by_cases belowB : right < 4
      · simp only [world, belowA, belowB, ↓reduceIte, Option.some.injEq] at foundA foundB
        subst a b
        rcases four_cases left belowA with rfl | rfl | rfl | rfl <;>
          rcases four_cases right belowB with rfl | rfl | rfl | rfl <;>
          simp_all [Ownership.Disjoint, region, codeRegion, stackRegion, regionA, regionB] <;> omega
      · simp [world, belowB] at foundB
    · simp [world, belowA] at foundA

theorem shared_valid (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) : Borrowing.WellFormed (shared bytes) := by
  refine ⟨world_valid bytes positive bound, ?_⟩
  intro identifier held found
  by_cases below : identifier < 4
  · simp only [shared, below, ↓reduceIte, Option.some.injEq] at found
    subst held
    refine ⟨below, ⟨7, 0, region bytes identifier⟩, ?_, rfl, rfl, ?_,
      region_valid bytes positive bound identifier below, region_readable bytes bound identifier below⟩
    · simp [shared, world, loan, below]
    · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · simp [shared, below] at found

def callA (bytes : List Byte) : Call :=
  ⟨10, ⟨0, 1, 2⟩, 4096, bytes, 65544, 131072, valuesA, 8192⟩

def callB (bytes : List Byte) : Call :=
  ⟨10, ⟨0, 1, 3⟩, 4096, bytes, 65544, 196608, valuesB, 8192⟩

theorem contractA (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) : Contract (shared bytes) (callA bytes) := by
  refine ⟨shared_valid bytes positive bound, ?_, code_current bytes bound,
    stack_current bytes bound, arrayA_current bytes bound,
    by change (131072 : Word).toNat + 4 * 4 ≤ 2^64; decide,
    by change canonical 8192 = true; decide,
    by change (65544 : Word).toNat + 8 < 2^64; decide,
    by change canonical ((65544 : Word) + 8) = true; decide⟩
  refine ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
    fun _ => ⟨_, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change 4096 + bytes.length ≤ 65544 ∨ 65544 + 8 ≤ 4096
    omega
  · intro _
    change 131072 + 16 ≤ 4096 ∨ 4096 + bytes.length ≤ 131072
    omega
  · intro _
    change Ownership.Disjoint regionA stackRegion
    decide

theorem contractB (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) : Contract (shared bytes) (callB bytes) := by
  refine ⟨shared_valid bytes positive bound, ?_, code_current bytes bound,
    stack_current bytes bound, arrayB_current bytes bound,
    by change (196608 : Word).toNat + 4 * 2 ≤ 2^64; decide,
    by change canonical 8192 = true; decide,
    by change (65544 : Word).toNat + 8 < 2^64; decide,
    by change canonical ((65544 : Word) + 8) = true; decide⟩
  refine ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
    fun _ => ⟨_, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change 4096 + bytes.length ≤ 65544 ∨ 65544 + 8 ≤ 4096
    omega
  · intro _
    change 196608 + 8 ≤ 4096 ∨ 4096 + bytes.length ≤ 196608
    omega
  · intro _
    change Ownership.Disjoint regionB stackRegion
    decide

def pairEntry (bytes : List Byte) : X86.State where
  registers register := match register with
    | .rdi => 131072
    | .rsi => 4
    | .rdx => 196608
    | .rcx => 2
    | .rsp => 65544
    | _ => 0xfedcba9876543210
  rip := 4096
  flags := 0x602
  memory := toMemory (space bytes)

def strideEntry (bytes : List Byte) : X86.State :=
  { pairEntry bytes with registers := fun register =>
      if register = .rsi then 2 else (pairEntry bytes).registers register }

/-- Raw machine preconditions also admit the empty span. The current OS
constructors below require positivity because a live code loan is nonempty. -/
theorem pair_raw_pre (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    Pair32.Pre bytes (pairEntry bytes) valuesA valuesB 8192 :=
  ⟨code_current bytes bound, arrayA_current bytes bound, arrayB_current bytes bound,
    by change (131072 : Word).toNat + 4 * 4 ≤ 2^64; decide,
    by change (196608 : Word).toNat + 4 * 2 ≤ 2^64; decide,
    rfl, rfl, stack_current bytes bound, by decide,
    by change canonical ((65544 : Word) + 8) = true; decide⟩

theorem stride_raw_pre (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    Stride32.Pre bytes (strideEntry bytes) valuesA 2 8192 :=
  ⟨code_current bytes bound, arrayA_current bytes bound,
    by change (131072 : Word).toNat + 4 * 4 ≤ 2^64; decide,
    rfl, rfl, stack_current bytes bound, by decide,
    by change canonical ((65544 : Word) + 8) = true; decide⟩

/-- Every nonempty bounded candidate has useful current OS inputs, including
unsupported machine code. No claim of execution or functional correctness is
made by constructing this witness. -/
def pair (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) : PairWitness bytes where
  shared := shared bytes
  callA := callA bytes
  callB := callB bytes
  initial := pairEntry bytes
  code := rfl
  admitted := ⟨⟨contractA bytes positive bound, rfl⟩,
    ⟨contractB bytes positive bound, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  entry := rfl
  stack := rfl
  baseA := rfl
  countA := rfl
  baseB := rfl
  countB := rfl
  usefulA := by change valuesA ≠ []; decide
  usefulB := by change valuesB ≠ []; decide

def stride (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) : StrideWitness bytes where
  shared := shared bytes
  call := callA bytes
  initial := strideEntry bytes
  count := 2
  code := rfl
  admitted := ⟨contractA bytes positive bound, rfl⟩
  entry := rfl
  stack := rfl
  base := rfl
  length := rfl
  counter := rfl
  useful := by decide

end EDSL.Grading.Domain
