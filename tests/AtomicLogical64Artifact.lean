/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.AtomicLogical64.Artifact
import EDSL.X86.StackRead64
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.AtomicLogical64Artifact
open X86 OS.AddressSpace
open AtomicLogical64

/-- Independently assembled full-width LOCK OR [RDI],RSI; RET. -/
def bytes : List Byte := [0xf0, 0x48, 0x09, 0x37, 0xc3]
theorem raw_accepted : AtomicLogical64.Artifact.checkRaw bytes = true := by decide +kernel
example : AtomicLogical64.Artifact.checkRaw [0x48, 0x09, 0x37, 0xc3] = false := by decide +kernel
example : AtomicLogical64.Artifact.checkRaw [0xf0, 0x09, 0x37, 0xc3] = false := by decide +kernel
example : AtomicLogical64.Artifact.checkRaw [0xf0, 0x48, 0x09, 0x17, 0xc3] = false := by decide +kernel
example : AtomicLogical64.Artifact.checkRaw (bytes.take 4) = false := by decide +kernel
example : AtomicLogical64.Artifact.checkRaw (bytes ++ [0x90]) = false := by decide +kernel
example : AtomicLogical64.Artifact.checkRaw (0x90 :: bytes) = false := by decide +kernel
example : AtomicLogical64.Artifact.checkRaw (bytes.set 4 0x90) = false := by decide +kernel

/-- Owned ELF64LE ET_EXEC, one five-byte RX segment at entry 0x400080,
file offset 128. There is no executable padding and no executable BSS. -/
def elfHeader : List Byte :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   2, 0, 62, 0, 1, 0, 0, 0, 0x80, 0, 0x40, 0, 0, 0, 0, 0,
   0x40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 64, 0, 56, 0, 1, 0, 0, 0, 0, 0, 0, 0,
   1, 0, 0, 0, 5, 0, 0, 0, 0x80, 0, 0, 0, 0, 0, 0, 0,
   0x80, 0, 0x40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   5, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0,
   0, 0x10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def elf : List Byte := elfHeader ++ bytes
def image : ELF.Image := ⟨0x400080, [⟨128, 0x400080, 5, 5, 5, 4096⟩]⟩
theorem elf_accepted : AtomicLogical64.Artifact.checkELF elf image = true := by decide +kernel
theorem elf_parsed : ELF.parse elf = .ok image := (AtomicLogical64.Artifact.checkELF_sound elf_accepted).1

/-- Parse each mutant anew, so rejection cannot be explained merely by passing
stale metadata from the positive fixture to checkParsed. -/
def acceptsFile (file : List Byte) : Bool :=
  match ELF.parse file with
  | .error _ => false
  | .ok parsed => AtomicLogical64.Artifact.checkELF file parsed

example : acceptsFile elf = true := by decide +kernel
example : acceptsFile (elf.set 24 0x81) = false := by decide +kernel
example : acceptsFile (elf.set 130 0x21) = false := by decide +kernel
example : acceptsFile (elf.set 129 0x40) = false := by decide +kernel
example : acceptsFile (elf.set 128 0x90) = false := by decide +kernel
example : acceptsFile (elf.set 131 0x17) = false := by decide +kernel
example : acceptsFile (elf.set 132 0x90) = false := by decide +kernel
example : acceptsFile (elf.take 132) = false := by decide +kernel
example : acceptsFile (elf.set 68 4) = false := by decide +kernel
example : acceptsFile (elf.set 104 6) = false := by decide +kernel
example : acceptsFile (((elf ++ [0x90]).set 96 6).set 104 6) = false := by decide +kernel
example : acceptsFile ((((elf.set 72 127).set 80 127).set 96 6).set 104 6) = false := by decide +kernel
example : acceptsFile (elf.set 0 0) = false := by decide +kernel
example : acceptsFile (elf.set 4 1) = false := by decide +kernel
example : acceptsFile (elf.set 5 2) = false := by decide +kernel
example : acceptsFile (elf.set 16 3) = false := by decide +kernel
example : acceptsFile (elf.set 54 48) = false := by decide +kernel
example : acceptsFile (elf.take 110) = false := by decide +kernel

-- These larger executable intervals remain valid ELF images selecting the
-- exact routine. Their rejection must exercise completeText, not parse failure.
example : ELF.parse (elf.set 104 6) =
    .ok ⟨0x400080,[⟨128,0x400080,5,6,5,4096⟩]⟩ := ELF.checkParsed_sound _ _ (by decide +kernel)
example : ELF.parse (((elf ++ [0x90]).set 96 6).set 104 6) =
    .ok ⟨0x400080,[⟨128,0x400080,6,6,5,4096⟩]⟩ := ELF.checkParsed_sound _ _ (by decide +kernel)
example : ELF.parse ((((elf.set 72 127).set 80 127).set 96 6).set 104 6) =
    .ok ⟨0x400080,[⟨127,0x40007f,6,6,5,4096⟩]⟩ := ELF.checkParsed_sound _ _ (by decide +kernel)

-- A caller cannot rebind a checked file to invented segment/entry metadata.
example : AtomicLogical64.Artifact.checkELF elf {image with entry := 0x400081} = false := by decide +kernel
example : AtomicLogical64.Artifact.checkELF elf ⟨0x400080, [⟨128, 0x400080, 5, 6, 5, 4096⟩]⟩ = false := by decide +kernel
-- Alignment is irrelevant to completeText and entry fetch. Only the parser's
-- equality to the actual program header rejects this fabricated metadata.
def forgedAlignment : ELF.Image := ⟨0x400080,[⟨128,0x400080,5,5,5,1⟩]⟩
example : AtomicLogical64.Artifact.completeText forgedAlignment = true ∧
    ELF.checkEntry elf forgedAlignment bytes = true := by decide +kernel
example : AtomicLogical64.Artifact.checkELF elf forgedAlignment = false := by decide +kernel
-- Pass the bad file directly to the checker: an outer parser in acceptsFile
-- must not conceal a missing checkParsed gate inside checkELF itself.
example : AtomicLogical64.Artifact.checkELF (elf.set 0 0) image = false := by decide +kernel

/-- Section offsets/counts/string indexes and trailing symbol-like names are
irrelevant to this program-header profile, even if they suggest another name. -/
def renamed : List Byte :=
  ((((elf.set 40 0xff).set 58 0x40).set 60 7).set 62 6) ++
    [0x77, 0x72, 0x6f, 0x6e, 0x67, 0, 0x6c, 0x6f, 0x63, 0x6b, 0]
example : AtomicLogical64.Artifact.checkELF renamed image = true := by decide +kernel

def dataHeader (flags : Byte) : List Byte :=
  [1, 0, 0, 0, flags, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0x50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   1, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0,
   0, 0x10, 0, 0, 0, 0, 0, 0]
def twoSegments (flags : Byte) : List Byte :=
  ((elfHeader.take 64).set 24 0xc0).set 56 2 ++
  (((elfHeader.drop 64).take 56).set 8 0xc0).set 16 0xc0 ++
  dataHeader flags ++ List.replicate 16 0 ++ bytes

def dataImage : ELF.Image :=
  ⟨0x4000c0, [⟨192, 0x4000c0, 5, 5, 5, 4096⟩, ⟨0, 0x500000, 1, 8, 4, 4096⟩]⟩
example : AtomicLogical64.Artifact.checkELF (twoSegments 4) dataImage = true := by decide +kernel
example : acceptsFile (twoSegments 5) = false := by decide +kernel
example : ELF.parse (twoSegments 5) =
    .ok ⟨0x4000c0,[⟨192,0x4000c0,5,5,5,4096⟩,⟨0,0x500000,1,8,5,4096⟩]⟩ :=
  ELF.checkParsed_sound _ _ (by decide +kernel)

-- A concrete checked allocator/store/loader/adopter chain, with arbitrary
-- full64 data. Installing ELF preserves existing owned data and caller stack.
def dataMapped : OS.Ownership.World :=
  OS.Ownership.install (OS.Ownership.empty empty) (mapUnchecked empty ⟨65536,16⟩ readWrite) 0 ⟨65536,16⟩
theorem data_allocated : OS.Ownership.allocate (OS.Ownership.empty empty) 0 ⟨65536,16⟩ readWrite =
    .ok (dataMapped, ⟨0,0⟩) :=
  OS.Ownership.allocate_success _ _ _ _ (OS.Ownership.empty_wellFormed _) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem data_valid : OS.Ownership.WellFormed dataMapped :=
  (OS.Ownership.allocate_wellFormed _ _ _ _ _ (OS.Ownership.empty_wellFormed _) data_allocated).1

def dataStored (old : Word) : OS.Ownership.World :=
  { dataMapped with space := writeQWordCells dataMapped.space 65536 old }
theorem data_stored (old : Word) : OS.Ownership.storeWord64 dataMapped 0 ⟨0,0⟩ 65536 old = .ok (dataStored old) :=
  OS.Ownership.storeWord64_success _ _ _ _ _ ⟨0,0,⟨65536,16⟩⟩ (by rfl) (by decide +kernel) (by decide +kernel)
theorem stored_valid (old : Word) : OS.Ownership.WellFormed (dataStored old) :=
  (OS.Ownership.storeWord64_wellFormed _ _ _ _ _ _ data_valid (data_stored old)).1

def neighborStored (old : Word) : OS.Ownership.World :=
  { dataStored old with space := writeQWordCells (dataStored old).space 65544 0x1122334455667788 }
theorem neighbor_stored (old : Word) :
    OS.Ownership.storeWord64 (dataStored old) 0 ⟨0,0⟩ 65544 0x1122334455667788 = .ok (neighborStored old) :=
  OS.Ownership.storeWord64_success _ _ _ _ _ ⟨0,0,⟨65536,16⟩⟩ (by rfl) (by decide +kernel) (by rfl)
theorem neighbor_valid (old : Word) : OS.Ownership.WellFormed (neighborStored old) :=
  (OS.Ownership.storeWord64_wellFormed _ _ _ _ _ _ (stored_valid old) (neighbor_stored old)).1

def stackMapped (old : Word) : OS.Ownership.World :=
  OS.Ownership.install (neighborStored old) (mapUnchecked (neighborStored old).space ⟨32768,8⟩ readWrite) 0 ⟨32768,8⟩
theorem stack_allocated (old : Word) : OS.Ownership.allocate (neighborStored old) 0 ⟨32768,8⟩ readWrite =
    .ok (stackMapped old, ⟨1,0⟩) :=
  OS.Ownership.allocate_success _ _ _ _ (neighbor_valid old) (by decide +kernel) (by decide +kernel) (by rfl)
theorem mapped_valid (old : Word) : OS.Ownership.WellFormed (stackMapped old) :=
  (OS.Ownership.allocate_wellFormed _ _ _ _ _ (neighbor_valid old) (stack_allocated old)).1

def prior (old : Word) : OS.Ownership.World :=
  { stackMapped old with space := writeQWordCells (stackMapped old).space 32768 8192 }
theorem caller_stored (old : Word) : OS.Ownership.storeWord64 (stackMapped old) 0 ⟨1,0⟩ 32768 8192 = .ok (prior old) :=
  OS.Ownership.storeWord64_success _ _ _ _ _ ⟨0,0,⟨32768,8⟩⟩ (by rfl) (by decide +kernel) (by rfl)
theorem prior_valid (old : Word) : OS.Ownership.WellFormed (prior old) :=
  (OS.Ownership.storeWord64_wellFormed _ _ _ _ _ _ (mapped_valid old) (caller_stored old)).1

/-- Prove rounded-page freshness by the address interval, without enumerating
4096 cells or increasing the kernel's default reduction budget. -/
theorem image_fresh (old : Word) : ELF.fresh image (prior old).space = true := by
  apply List.all_eq_true.mpr
  intro segment member
  have same : segment = ⟨128,0x400080,5,5,5,4096⟩ := List.mem_singleton.mp member
  subst segment
  apply List.all_eq_true.mpr
  intro address member
  have inside := OS.Ownership.addresses_inside (ELF.Segment.pageRegion ⟨128,0x400080,5,5,5,4096⟩)
    (by decide +kernel) address member
  have lower : 0x400000 ≤ address.toNat := inside.1
  have dataOut : ¬ (⟨65536,16⟩ : Region).Contains address := by
    intro h; have := h.2; change address.toNat < 65552 at this; omega
  have stackOut : ¬ (⟨32768,8⟩ : Region).Contains address := by
    intro h; have := h.2; change address.toNat < 32776 at this; omega
  have targetOut : ¬ (qwordRegion 65536).Contains address := by
    intro h; have := h.2; change address.toNat < 65544 at this; omega
  have neighborOut : ¬ (qwordRegion 65544).Contains address := by
    intro h; have := h.2; change address.toNat < 65552 at this; omega
  suffices absent : (prior old).space.cells address = none by simp [absent]
  simp only [prior, stackMapped, neighborStored, dataStored, dataMapped, OS.Ownership.install]
  rw [writeQWord_frame _ _ _ _ stackOut, map_frame _ _ _ _ stackOut,
    writeQWord_frame _ _ _ _ neighborOut, writeQWord_frame _ _ _ _ targetOut,
    map_frame _ _ _ _ dataOut]
  rfl

def loaded (old : Word) : OS.Ownership.World :=
  { prior old with space := ELF.install elf image (prior old).space }
theorem loaded_valid (old : Word) : OS.Ownership.WellFormed (loaded old) := by
  apply OS.Ownership.changeSpace_wellFormed _ _ (prior_valid old)
  intro identifier allocation live address inside
  obtain ⟨cell, found⟩ := (prior_valid old).1 identifier allocation live |>.2.2 address inside
  exact ⟨cell, ELF.install_preserves_existing elf image (prior old).space
    (ELF.parse_valid _ _ elf_parsed) (image_fresh old) address cell found⟩

def owned (old : Word) : OS.Ownership.World :=
  OS.Ownership.install (loaded old) (loaded old).space 0 ⟨0x400080,5⟩
theorem code_adopted (old : Word) : OS.Ownership.adopt (loaded old) 0 ⟨0x400080,5⟩ = .ok (owned old, ⟨2,0⟩) :=
  OS.Ownership.adopt_success _ _ _ (loaded_valid old) (by decide +kernel) (by rfl) (by rfl)
theorem owned_valid (old : Word) : OS.Ownership.WellFormed (owned old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (loaded_valid old) (code_adopted old)).1

def raw (old : Word) : Shared := OS.Atomics64.empty (OS.Atomics.empty (OS.Borrowing.empty (owned old)))
theorem raw_valid (old : Word) : OS.Atomics64.WellFormed (raw old) :=
  OS.Atomics64.empty_wellFormed _ (OS.Atomics.empty_wellFormed _ (OS.Borrowing.empty_wellFormed _ (owned_valid old)))
def enrolled (old : Word) : Shared := OS.Atomics64.installCell (raw old) ⟨0,⟨0,0⟩,65536⟩
theorem target_enrolled (old : Word) : OS.Atomics64.enroll (raw old) 0 ⟨0,0⟩ 65536 = .ok (enrolled old, ⟨0⟩) := by rfl
theorem enrolled_valid (old : Word) : OS.Atomics64.WellFormed (enrolled old) :=
  (OS.Atomics64.enroll_wellFormed _ _ _ _ _ (raw_valid old) (target_enrolled old)).1

def issued (old : Word) : Shared := OS.Atomics64.installHandle (enrolled old) ⟨11,⟨0⟩⟩
theorem handle_issued (old : Word) : OS.Atomics64.issue (enrolled old) 0 ⟨0⟩ 11 = .ok (issued old, ⟨0⟩) := by rfl
theorem issued_valid (old : Word) : OS.Atomics64.WellFormed (issued old) :=
  (OS.Atomics64.issue_wellFormed _ _ _ _ _ (enrolled_valid old) (handle_issued old)).1

def withCode (old : Word) : Shared :=
  { issued old with legacy := { (issued old).legacy with shared := OS.Borrowing.installLoan (issued old).legacy.shared ⟨⟨2,0⟩,0,11,⟨0x400080,5⟩⟩ } }
theorem code_borrowed (old : Word) : OS.Atomics64.readBorrow (issued old) 0 ⟨2,0⟩ 11 ⟨0x400080,5⟩ =
    .ok (withCode old,0) := by rfl
theorem code_valid (old : Word) : OS.Atomics64.WellFormed (withCode old) :=
  OS.Atomics64.readBorrow_wellFormed _ _ _ _ _ _ (issued_valid old) (code_borrowed old)

def shared (old : Word) : Shared :=
  { withCode old with legacy := { (withCode old).legacy with shared := OS.Borrowing.installLoan (withCode old).legacy.shared ⟨⟨1,0⟩,0,11,⟨32768,8⟩⟩ } }
theorem stack_borrowed (old : Word) : OS.Atomics64.readBorrow (withCode old) 0 ⟨1,0⟩ 11 ⟨32768,8⟩ =
    .ok (shared old,1) := by rfl
theorem shared_valid (old : Word) : OS.Atomics64.WellFormed (shared old) :=
  OS.Atomics64.readBorrow_wellFormed _ _ _ _ _ _ (code_valid old) (stack_borrowed old)

def input : Input := ⟨11,⟨0⟩,0,1,8192⟩
def initial (old mask : Word) : X86.State where
  registers register := match register with
    | .rdi => 65536
    | .rsi => mask
    | .rsp => 32768
    | .rax => 0xa5a55a5af0f00f0f
    | _ => 0x123456789abcdef0
  rip := 0x400080
  flags := 0x202
  memory := toMemory (shared old).legacy.shared.resources.space

theorem caller_read (old : Word) : readWord (initial old 0).memory 32768 = .ok (8192 : Word) := by
  have stored := OS.Ownership.storeWord64_sound _ _ _ _ _ _ (caller_stored old)
  have read : readWord (toMemory (prior old).space) 32768 = .ok (8192 : Word) :=
    readWord_of_loadQWord _ _ _ stored.2.2.2.2.1
  have frame : MemoryAgreesOn (initial old 0).memory (toMemory (prior old).space) 32768 8 := by
    intro offset bound
    have offsetSmall : offset < 2^64 := by omega
    have sumSmall : 32768 + offset < 2^64 := by omega
    have address : ((32768 : Word) + BitVec.ofNat 64 offset).toNat = 32768 + offset := by
      change (32768 + offset % 2^64) % 2^64 = 32768 + offset
      rw [Nat.mod_eq_of_lt offsetSmall, Nat.mod_eq_of_lt sumSmall]
    have outside : ∀ segment ∈ image.segments,
        ¬ segment.Contains ((32768 : Word) + BitVec.ofNat 64 offset).toNat := by
      intro segment member
      have same : segment = ⟨128,0x400080,5,5,5,4096⟩ := List.mem_singleton.mp member
      subst segment
      rw [address]
      change ¬ (4194432 ≤ 32768 + offset ∧ 32768 + offset < 4194437)
      omega
    have cells := ELF.install_outside elf image (prior old).space _ outside
    exact (toMemory_agrees_at _ _ _ cells).1
  exact (readWord_congr _ _ _ frame).trans read

theorem resources (old mask : Word) : Resources bytes input (shared old) (initial old mask) := by
  refine ⟨shared_valid old, ⟨⟨11,⟨0⟩⟩,⟨0,⟨0,0⟩,65536⟩, by rfl, rfl⟩, rfl,
    ⟨⟨⟨2,0⟩,0,11,⟨0x400080,5⟩⟩,rfl,rfl,rfl⟩,
    ⟨⟨⟨1,0⟩,0,11,⟨32768,8⟩⟩,rfl,rfl,rfl⟩, ?_,
    by decide +kernel,
    by change 32768 + 8 < (2:Nat)^64; decide +kernel,
    by change canonical (32768 + 8) = true; decide +kernel⟩
  exact caller_read old

/-- Actual fresh full-file installation supplies CodeAt; current resources
come from the checked operations above, for every old word and mask. -/
theorem loaded_pre (old mask : Word) : Pre bytes input (shared old) (initial old mask) :=
  AtomicLogical64.Artifact.pre_of_loaded elf_accepted (prior old).space (resources old mask) rfl rfl

theorem old_read (old mask : Word) :
    loadQWord (initial old mask).memory 65536 = .ok old := by
  change Except.ok (joinQWord (old.extractLsb' 0 8) (old.extractLsb' 8 8)
    (old.extractLsb' 16 8) (old.extractLsb' 24 8) (old.extractLsb' 32 8)
    (old.extractLsb' 40 8) (old.extractLsb' 48 8) (old.extractLsb' 56 8)) = .ok old
  rw [qword_join_extracts]


theorem raw_semantics_nonvacuous (old mask : Word) :
    LockedLogical64.AllExecutions (initial old mask) (ResultContract input (shared old) (initial old mask)) :=
  AtomicLogical64.Artifact.raw_sound raw_accepted input (shared old) (initial old mask) (loaded_pre old mask)

/-- The loaded theorem is inhabited by this actual fresh installation and
present resource setup; it is not merely a universal implication about Pre. -/
theorem loaded_semantics_nonvacuous (old mask : Word) :
    ELF.load elf (prior old).space = .ok ⟨image, ELF.install elf image (prior old).space⟩ ∧
      LockedLogical64.AllExecutions (initial old mask) (ResultContract input (shared old) (initial old mask)) :=
  (AtomicLogical64.Artifact.elf_sound elf_accepted).2.2 (prior old).space (image_fresh old)
    input (shared old) (initial old mask) (resources old mask) rfl rfl

/-- Observations independent of byte-update expressions: natural-number bit
membership, actual event/actor identities, ABI return, and current loan frames. -/
structure Observed (old mask : Word) (output : Result) (changed : Shared × Event) : Prop where
  mutation : OS.Atomics64.logicalDiscard (shared old) 11 ⟨0⟩ mask = .ok changed
  valid : OS.Atomics64.WellFormed changed.1
  retired : output.instructions = 2
  events : output.events = [changed.2.logical]
  identity : changed.2.actor = 11 ∧ changed.2.handle = ⟨0⟩ ∧ changed.2.cell = ⟨0⟩
  operation : changed.2.logical.op = .bor ∧ changed.2.logical.mask = mask ∧ changed.2.logical.event.address = 65536
  before : changed.2.logical.event.before = old
  bits : ∀ index : Fin 64, changed.2.logical.event.after.toNat.testBit index = true ↔
    old.toNat.testBit index = true ∨ mask.toNat.testBit index = true
  readback : loadQWord output.state.memory 65536 = .ok changed.2.logical.event.after
  memory : output.state.memory = toMemory changed.1.legacy.shared.resources.space
  accesses : output.accesses = [.rmw8 65536, .stack8 32768]
  returned : output.state.rip = 8192 ∧ output.state.registers .rsp = 32776 ∧ canonical (output.state.registers .rsp) = true
  abi : output.state.registers .rax = 0xa5a55a5af0f00f0f ∧
    output.state.registers .rdi = 65536 ∧ output.state.registers .rsi = mask ∧
    ∀ register, register ≠ .rsp → output.state.registers register = (initial old mask).registers register
  frame : ∀ query, 8 ≤ (query - (65536 : Word)).toNat →
    output.state.memory.read query = (initial old mask).memory.read query
  registries : changed.1.cells = (shared old).cells ∧ changed.1.handles = (shared old).handles
  loans : ∀ identifier loan, (shared old).legacy.shared.loans identifier = some loan →
    changed.1.legacy.shared.loans identifier = some loan ∧
    ∀ query, loan.region.Contains query → changed.1.legacy.shared.resources.space.cells query =
      (shared old).legacy.shared.resources.space.cells query

/-- Every old/mask and every AF stream has an actual successful bounded run
from the inhabited checked domain, with one event and the independent oracle. -/
theorem all_words_run (old mask : Word) (choices : Choices) :
    ∃ output changed, LockedLogical64.run choices 2 (initial old mask) = .ok output ∧
      Observed old mask output changed := by
  obtain ⟨output, ran, changed, mutation, valid, retired, events, accesses, memory,
    rip, rsp, registers, canonical, beforeRead, readback, bits, frame, cells, handles, loans⟩ :=
    AtomicLogical64.Artifact.raw_run raw_accepted input (shared old) (initial old mask) (loaded_pre old mask) choices
  have before : changed.2.logical.event.before = old :=
    (Except.ok.inj ((old_read old mask).symm.trans beforeRead)).symm
  have sound := OS.Atomics64.logicalDiscard_sound _ _ _ _ _ mutation
  have identity := OS.Atomics64.logicalDiscard_identity _ _ _ _ _
    ⟨11,⟨0⟩⟩ ⟨0,⟨0,0⟩,65536⟩ mutation (by rfl)
  refine ⟨output,changed,ran,{
    mutation := mutation, valid := valid, retired := retired, events := events,
    identity := ⟨sound.2.2.2.2.1,sound.2.2.2.2.2,identity.1⟩,
    operation := ⟨sound.2.1,sound.2.2.1,identity.2⟩,
    before := before, bits := ?_, readback := readback, memory := memory,
    accesses := accesses, returned := ⟨rip,rsp,canonical⟩,
    abi := ⟨registers .rax (by decide +kernel),registers .rdi (by decide +kernel),registers .rsi (by decide +kernel),registers⟩,
    frame := frame, registries := ⟨cells,handles⟩, loans := loans }⟩
  simpa only [Logical64.MathematicalResult, Logical64.HasBit, before, initial] using bits

/-- The actual fixed names survive and still protect their contents, including
all code bytes and the caller's original return slot. -/
theorem named_loans_framed (old mask : Word) (choices : Choices) :
    ∃ (output : Result) (changed : Shared × Event), LockedLogical64.run choices 2 (initial old mask) = .ok output ∧
      LoanAt changed.1 11 0 ⟨0x400080,5⟩ ∧ LoanAt changed.1 11 1 ⟨32768,8⟩ ∧
      (∀ query, (⟨0x400080,5⟩ : Region).Contains query →
        changed.1.legacy.shared.resources.space.cells query = (shared old).legacy.shared.resources.space.cells query) ∧
      (∀ query, (⟨32768,8⟩ : Region).Contains query →
        changed.1.legacy.shared.resources.space.cells query = (shared old).legacy.shared.resources.space.cells query) := by
  obtain ⟨output,changed,ran,observed⟩ := all_words_run old mask choices
  have code := observed.loans 0 ⟨⟨2,0⟩,0,11,⟨0x400080,5⟩⟩ rfl
  have stack := observed.loans 1 ⟨⟨1,0⟩,0,11,⟨32768,8⟩⟩ rfl
  exact ⟨output,changed,ran,⟨_,code.1,rfl,rfl⟩,⟨_,stack.1,rfl,rfl⟩,code.2,stack.2⟩

-- Real current-authority and allocation-wide gates, not assumed mutations.
example (old mask : Word) : OS.Atomics64.logicalDiscard (shared old) 12 ⟨0⟩ mask = .error .wrongActor := by rfl
example (old : Word) : OS.Atomics64.enroll (raw old) 0 ⟨0,1⟩ 65536 = .error (.ownership .staleEpoch) := by rfl
example (old : Word) : OS.Atomics64.enroll (raw old) 0 ⟨0,0⟩ 65548 = .error (.ownership .outsideAllocation) := by rfl
example (old : Word) : OS.Atomics64.mutate (shared old) (.store64 0 ⟨0,0⟩ 65544 0) = .error .reserved := by rfl
example (old : Word) : OS.Atomics64.mutate (shared old) (.transfer 0 ⟨0,0⟩ 11) = .error .reserved := by rfl
example (old : Word) : OS.Atomics64.readBorrow (shared old) 0 ⟨0,0⟩ 11 ⟨65544,8⟩ = .error .reserved := by rfl
example (old : Word) : OS.Atomics64.mutate (shared old) (.protect 0 ⟨2,0⟩ readOnly) =
    .error (.legacy (.authority .borrowed)) := by rfl
example (old : Word) : OS.Atomics64.mutate (shared old) (.release 0 ⟨1,0⟩) =
    .error (.legacy (.authority .borrowed)) := by rfl
example (old : Word) : OS.Borrowing.authorize (shared old).legacy.shared 12 0 = .error .wrongBorrower := by rfl

def codeFinished (old : Word) : Shared :=
  { shared old with legacy := { (shared old).legacy with shared :=
    { (shared old).legacy.shared with loans := fun query => if query = 0 then none else (shared old).legacy.shared.loans query } } }
theorem code_finished (old : Word) : OS.Atomics64.finishLoan (shared old) 11 0 = .ok (codeFinished old) := by rfl
example (old mask : Word) : ¬ Resources bytes input (codeFinished old) (initial old mask) := by
  intro pre
  obtain ⟨loan,live,_,_⟩ := pre.codeLoan
  change none = some loan at live
  contradiction

def closed (old : Word) : Shared := OS.Atomics64.removeHandle (shared old) ⟨0⟩
theorem handle_closed (old : Word) : OS.Atomics64.close (shared old) 11 ⟨0⟩ = .ok (closed old) := by rfl
example (old mask : Word) : OS.Atomics64.logicalDiscard (closed old) 11 ⟨0⟩ mask = .error .missingHandle := by rfl
example (old mask : Word) : ¬ Resources bytes input (closed old) (initial old mask) := by
  intro pre
  obtain ⟨handle,cell,authorized,_⟩ := pre.authority
  change Except.error OS.Atomics64.Fault.missingHandle = Except.ok (handle,cell) at authorized
  contradiction


/-- Literal byte oracles below are selected independently of the operation's
byte-store and word-evaluation expressions. -/
def targetBytes (memory : Memory) : List (Option Byte) :=
  [memory.read 65536, memory.read 65537, memory.read 65538, memory.read 65539,
   memory.read 65540, memory.read 65541, memory.read 65542, memory.read 65543]

theorem literal_run (old mask expected : Word) (expectedBytes : List Byte)
    (oracle : Logical64.MathematicalResult .union old mask expected)
    (endian : ∀ memory, targetBytes (writeQWordUnchecked memory 65536 expected) = expectedBytes.map some)
    (choices : Choices) :
    ∃ output changed, LockedLogical64.run choices 2 (initial old mask) = .ok output ∧
      Observed old mask output changed ∧ loadQWord output.state.memory 65536 = .ok expected ∧
      targetBytes output.state.memory = expectedBytes.map some := by
  obtain ⟨output,changed,ran,observed⟩ := all_words_run old mask choices
  have value : changed.2.logical.event.after = expected :=
    @Logical64.MathematicalResult.unique .union old mask _ expected observed.bits oracle
  have effect := OS.Atomics64.logicalDiscard_effect _ _ _ _ _ observed.mutation
  have written : output.state.memory = writeQWordUnchecked (initial old mask).memory 65536 expected := by
    rw [observed.memory, effect.shared.projection, observed.operation.2.2, value]
    rfl
  refine ⟨output,changed,ran,observed,?_,?_⟩
  · simpa only [value] using observed.readback
  · rw [written]
    exact endian _

-- Distinct high and low bytes exercise the complete qword, source register,
-- address, little-endian store, one-event result and all AF streams together.
example (choices : Choices) :
    ∃ output changed, LockedLogical64.run choices 2
        (initial 0x0123456789abcdef 0x8040201008040201) = .ok output ∧
      Observed 0x0123456789abcdef 0x8040201008040201 output changed ∧
      loadQWord output.state.memory 65536 = .ok 0x8163657789afcfef ∧
      targetBytes output.state.memory = [some 0xef,some 0xcf,some 0xaf,some 0x89,
        some 0x77,some 0x65,some 0x63,some 0x81] :=
  literal_run _ _ _ [0xef,0xcf,0xaf,0x89,0x77,0x65,0x63,0x81]
    (by unfold Logical64.MathematicalResult Logical64.HasBit; decide +kernel) (by intro memory; rfl) choices

-- Zero must preserve the current complete word, including the upper half.
example (choices : Choices) :
    ∃ output changed, LockedLogical64.run choices 2 (initial 0xfedcba9876543210 0) = .ok output ∧
      Observed 0xfedcba9876543210 0 output changed ∧
      loadQWord output.state.memory 65536 = .ok 0xfedcba9876543210 ∧
      targetBytes output.state.memory = [some 0x10,some 0x32,some 0x54,some 0x76,
        some 0x98,some 0xba,some 0xdc,some 0xfe] :=
  literal_run _ _ _ [0x10,0x32,0x54,0x76,0x98,0xba,0xdc,0xfe]
    (by unfold Logical64.MathematicalResult Logical64.HasBit; decide +kernel) (by intro memory; rfl) choices

-- A mask containing only bit63 must not be truncated to a dword or sign-
-- extended from another operand; the existing bit32 and bit0 both survive.
example (choices : Choices) :
    ∃ output changed, LockedLogical64.run choices 2
        (initial 0x0000000100000001 0x8000000000000000) = .ok output ∧
      Observed 0x0000000100000001 0x8000000000000000 output changed ∧
      loadQWord output.state.memory 65536 = .ok 0x8000000100000001 ∧
      targetBytes output.state.memory = [some 1,some 0,some 0,some 0,some 1,some 0,some 0,some 0x80] :=
  literal_run _ _ _ [1,0,0,0,1,0,0,0x80]
    (by unfold Logical64.MathematicalResult Logical64.HasBit; decide +kernel) (by intro memory; rfl) choices

example (choices : Choices) :
    ∃ output changed, LockedLogical64.run choices 2 (initial 0 0) = .ok output ∧
      Observed 0 0 output changed ∧ loadQWord output.state.memory 65536 = .ok 0 ∧
      targetBytes output.state.memory = [some 0,some 0,some 0,some 0,some 0,some 0,some 0,some 0] :=
  literal_run _ _ _ [0,0,0,0,0,0,0,0]
    (by unfold Logical64.MathematicalResult Logical64.HasBit; decide +kernel) (by intro memory; rfl) choices

/-- Probe actual neighboring data, checked executable bytes and the real caller
slot after a symbolic run, rather than only comparing registry assignments. -/
theorem concrete_frames (old mask : Word) (choices : Choices) :
    ∃ output changed, LockedLogical64.run choices 2 (initial old mask) = .ok output ∧
      Observed old mask output changed ∧
      output.state.memory.read 65544 = some 0x88 ∧ output.state.memory.read 65551 = some 0x11 ∧
      output.state.memory.read 0x400080 = some 0xf0 ∧ output.state.memory.read 0x400084 = some 0xc3 ∧
      output.state.memory.read 32769 = some 0x20 := by
  obtain ⟨output,changed,ran,observed⟩ := all_words_run old mask choices
  refine ⟨output,changed,ran,observed,?_,?_,?_,?_,?_⟩
  · exact (observed.frame 65544 (by decide +kernel)).trans (by rfl)
  · exact (observed.frame 65551 (by decide +kernel)).trans (by rfl)
  · exact (observed.frame 0x400080 (by decide +kernel)).trans (by rfl)
  · exact (observed.frame 0x400084 (by decide +kernel)).trans (by rfl)
  · exact (observed.frame 32769 (by decide +kernel)).trans (by rfl)

end EDSL.Tests.AtomicLogical64Artifact

#audit_edsl
