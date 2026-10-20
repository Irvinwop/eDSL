/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.AtomicSet64
import EDSL.AtomicLogical64.Artifact
import EDSL.X86.StackRead64
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.AtomicSet64Artifact
open X86 OS.AddressSpace AtomicSet64

/-- Literal independently assembled instructions, chosen by the task name. -/
def referenceBytes : Logical64.Operation → List Byte
  | .intersection => [0xf0, 0x48, 0x21, 0x37, 0xc3]
  | .union => [0xf0, 0x48, 0x09, 0x37, 0xc3]
  | .symmetricDifference => [0xf0, 0x48, 0x31, 0x37, 0xc3]

theorem raw_accepted (operation : Logical64.Operation) :
    Artifact.checkRaw operation (referenceBytes operation) = true := by
  cases operation <;> decide +kernel

example : Artifact.checkRaw .intersection (referenceBytes .union) = false := by decide +kernel
example : Artifact.checkRaw .intersection (referenceBytes .symmetricDifference) = false := by decide +kernel
example : Artifact.checkRaw .union (referenceBytes .intersection) = false := by decide +kernel
example : Artifact.checkRaw .union (referenceBytes .symmetricDifference) = false := by decide +kernel
example : Artifact.checkRaw .symmetricDifference (referenceBytes .intersection) = false := by decide +kernel
example : Artifact.checkRaw .symmetricDifference (referenceBytes .union) = false := by decide +kernel

example (operation : Logical64.Operation) :
    Artifact.checkRaw operation ((referenceBytes operation).drop 1) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) :
    Artifact.checkRaw operation ((referenceBytes operation).set 1 0x40) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) :
    Artifact.checkRaw operation ((referenceBytes operation).set 3 0x17) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) :
    Artifact.checkRaw operation ((referenceBytes operation).take 4) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) :
    Artifact.checkRaw operation ((referenceBytes operation).set 4 0x90) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) :
    Artifact.checkRaw operation (referenceBytes operation ++ [0x90]) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) :
    Artifact.checkRaw operation (0x90 :: referenceBytes operation) = false := by
  cases operation <;> decide +kernel

-- The old OR-only checker and runner remain a distinct public profile.
example : AtomicLogical64.Artifact.checkRaw (referenceBytes .intersection) = false := by decide +kernel
example : AtomicLogical64.Artifact.checkRaw (referenceBytes .symmetricDifference) = false := by decide +kernel
example : AtomicLogical64.Artifact.checkRaw (referenceBytes .union) = true := by decide +kernel

/-- One exact five-byte RX segment, independently encoded ELF64LE ET_EXEC. -/
def elfHeader : List Byte :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   2, 0, 62, 0, 1, 0, 0, 0, 0x80, 0, 0x40, 0, 0, 0, 0, 0,
   0x40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 64, 0, 56, 0, 1, 0, 0, 0, 0, 0, 0, 0,
   1, 0, 0, 0, 5, 0, 0, 0, 0x80, 0, 0, 0, 0, 0, 0, 0,
   0x80, 0, 0x40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   5, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0,
   0, 0x10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def elf (operation : Logical64.Operation) : List Byte := elfHeader ++ referenceBytes operation
def image : ELF.Image := ⟨0x400080, [⟨128, 0x400080, 5, 5, 5, 4096⟩]⟩
theorem elf_accepted (operation : Logical64.Operation) : Artifact.checkELF operation (elf operation) image = true := by
  cases operation <;> decide +kernel

def acceptsFile (operation : Logical64.Operation) (file : List Byte) : Bool :=
  match ELF.parse file with
  | .error _ => false
  | .ok parsed => Artifact.checkELF operation file parsed

example : acceptsFile .intersection (elf .union) = false := by decide +kernel
example : acceptsFile .union (elf .symmetricDifference) = false := by decide +kernel
example : acceptsFile .symmetricDifference (elf .intersection) = false := by decide +kernel
example (operation : Logical64.Operation) : acceptsFile operation ((elf operation).set 24 0x81) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) : acceptsFile operation ((elf operation).set 129 0x40) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) : acceptsFile operation ((elf operation).set 131 0x17) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) : acceptsFile operation ((elf operation).set 132 0x90) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) : acceptsFile operation ((elf operation).take 132) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) : acceptsFile operation ((elf operation).set 0 0) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) : acceptsFile operation ((elf operation).set 4 1) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) : acceptsFile operation ((elf operation).set 5 2) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) : acceptsFile operation ((elf operation).set 16 3) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) : acceptsFile operation ((elf operation).set 54 48) = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) : acceptsFile operation ((elf operation).take 110) = false := by
  cases operation <;> decide +kernel

/-- These valid images still pass the entry-window checker. Full executable
segment rejection must catch BSS, suffix, and prefix beyond that window. -/
def extended : ELF.Image := ⟨0x400080, [⟨128,0x400080,5,6,5,4096⟩]⟩
def suffixed : ELF.Image := ⟨0x400080, [⟨128,0x400080,6,6,5,4096⟩]⟩
def prefixed : ELF.Image := ⟨0x400080, [⟨127,0x40007f,6,6,5,4096⟩]⟩
def partialImage : ELF.Image := ⟨0x400080, [⟨128,0x400080,4,5,5,4096⟩]⟩
def suffixELF (operation : Logical64.Operation) : List Byte :=
  (((elf operation) ++ [0x90]).set 96 6).set 104 6
def prefixELF (operation : Logical64.Operation) : List Byte :=
  ((((elf operation).set 72 127).set 80 127).set 96 6).set 104 6

example (operation : Logical64.Operation) :
    ELF.checkParsed ((elf operation).set 96 4) partialImage = true ∧
    Artifact.checkELF operation ((elf operation).set 96 4) partialImage = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) :
    ELF.checkParsed ((elf operation).set 104 6) extended = true ∧
    ELF.checkEntry ((elf operation).set 104 6) extended (referenceBytes operation) = true ∧
    Artifact.checkELF operation ((elf operation).set 104 6) extended = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) :
    ELF.checkParsed (suffixELF operation) suffixed = true ∧
    ELF.checkEntry (suffixELF operation) suffixed (referenceBytes operation) = true ∧
    Artifact.checkELF operation (suffixELF operation) suffixed = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) :
    ELF.checkParsed (prefixELF operation) prefixed = true ∧
    ELF.checkEntry (prefixELF operation) prefixed (referenceBytes operation) = true ∧
    Artifact.checkELF operation (prefixELF operation) prefixed = false := by
  cases operation <;> decide +kernel

def forgedAlignment : ELF.Image := ⟨0x400080,[⟨128,0x400080,5,5,5,1⟩]⟩
example (operation : Logical64.Operation) :
    Artifact.completeText forgedAlignment = true ∧
    ELF.checkEntry (elf operation) forgedAlignment (referenceBytes operation) = true ∧
    Artifact.checkELF operation (elf operation) forgedAlignment = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) :
    Artifact.checkELF operation (elf operation) {image with entry := 0x400081} = false := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) :
    Artifact.checkELF operation ((elf operation).set 0 0) image = false := by
  cases operation <;> decide +kernel

def dataHeader (flags : Byte) : List Byte :=
  [1, 0, 0, 0, flags, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0x50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   1, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0,
   0, 0x10, 0, 0, 0, 0, 0, 0]
def twoSegments (operation : Logical64.Operation) (flags : Byte) : List Byte :=
  ((elfHeader.take 64).set 24 0xc0).set 56 2 ++
  (((elfHeader.drop 64).take 56).set 8 0xc0).set 16 0xc0 ++
  dataHeader flags ++ List.replicate 16 0 ++ referenceBytes operation
def dataImage : ELF.Image :=
  ⟨0x4000c0,[⟨192,0x4000c0,5,5,5,4096⟩,⟨0,0x500000,1,8,4,4096⟩]⟩
def extraTextImage : ELF.Image :=
  ⟨0x4000c0,[⟨192,0x4000c0,5,5,5,4096⟩,⟨0,0x500000,1,8,5,4096⟩]⟩
example (operation : Logical64.Operation) :
    Artifact.checkELF operation (twoSegments operation 4) dataImage = true := by
  cases operation <;> decide +kernel
example (operation : Logical64.Operation) :
    ELF.checkParsed (twoSegments operation 5) extraTextImage = true ∧
    ELF.checkEntry (twoSegments operation 5) extraTextImage (referenceBytes operation) = true ∧
    Artifact.checkELF operation (twoSegments operation 5) extraTextImage = false := by
  cases operation <;> decide +kernel

/-- Section names and a nonloaded suffix are irrelevant, but remain literally
bound in emitted full-file certificates rather than silently discarded. -/
def renamed (operation : Logical64.Operation) : List Byte :=
  (((((elf operation).set 40 0xff).set 58 0x40).set 60 7).set 62 6) ++
    [0x77,0x72,0x6f,0x6e,0x67,0,0x6c,0x6f,0x63,0x6b,0]
example (operation : Logical64.Operation) :
    Artifact.checkELF operation (renamed operation) image = true := by
  cases operation <;> decide +kernel

/-- Literal caller/operand/neighbor bytes, independent of the backend's store
helper. The target has distinct low/high halves and the caller returns to 8192. -/
def prior : Space where
  cells address := match address.toNat with
    | 32769 => some ⟨0x20,readWrite⟩
    | 32768 | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some ⟨0,readWrite⟩
    | 65536 => some ⟨0x10,readWrite⟩
    | 65537 => some ⟨0x32,readWrite⟩
    | 65538 => some ⟨0x54,readWrite⟩
    | 65539 => some ⟨0x76,readWrite⟩
    | 65540 => some ⟨0x98,readWrite⟩
    | 65541 => some ⟨0xba,readWrite⟩
    | 65542 => some ⟨0xdc,readWrite⟩
    | 65543 => some ⟨0xfe,readWrite⟩
    | 65544 => some ⟨0x88,readWrite⟩
    | 65545 => some ⟨0x77,readWrite⟩
    | 65546 => some ⟨0x66,readWrite⟩
    | 65547 => some ⟨0x55,readWrite⟩
    | 65548 => some ⟨0x44,readWrite⟩
    | 65549 => some ⟨0x33,readWrite⟩
    | 65550 => some ⟨0x22,readWrite⟩
    | 65551 => some ⟨0x11,readWrite⟩
    | _ => none

theorem image_fresh : ELF.fresh image prior = true := by
  apply List.all_eq_true.mpr
  intro segment member
  have same : segment = ⟨128,0x400080,5,5,5,4096⟩ := List.mem_singleton.mp member
  subst segment
  apply List.all_eq_true.mpr
  intro address member
  have inside := OS.Ownership.addresses_inside
    (ELF.Segment.pageRegion ⟨128,0x400080,5,5,5,4096⟩) (by decide +kernel) address member
  have lower : 0x400000 ≤ address.toNat := inside.1
  have absent : prior.cells address = none := by
    simp only [prior]
    split <;> first | rfl | omega
  simp [absent]

def loaded (operation : Logical64.Operation) : OS.Ownership.World :=
  OS.Ownership.empty (ELF.install (elf operation) image prior)
def dataOwned (operation : Logical64.Operation) : OS.Ownership.World :=
  OS.Ownership.install (loaded operation) (loaded operation).space 0 ⟨65536,16⟩
theorem data_adopted (operation : Logical64.Operation) :
    OS.Ownership.adopt (loaded operation) 0 ⟨65536,16⟩ = .ok (dataOwned operation,⟨0,0⟩) := by rfl
theorem data_valid (operation : Logical64.Operation) : OS.Ownership.WellFormed (dataOwned operation) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (OS.Ownership.empty_wellFormed _)
    (data_adopted operation)).1
def stackOwned (operation : Logical64.Operation) : OS.Ownership.World :=
  OS.Ownership.install (dataOwned operation) (dataOwned operation).space 0 ⟨32768,8⟩
theorem stack_adopted (operation : Logical64.Operation) :
    OS.Ownership.adopt (dataOwned operation) 0 ⟨32768,8⟩ = .ok (stackOwned operation,⟨1,0⟩) := by rfl
theorem stack_valid (operation : Logical64.Operation) : OS.Ownership.WellFormed (stackOwned operation) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (data_valid operation) (stack_adopted operation)).1
def codeOwned (operation : Logical64.Operation) : OS.Ownership.World :=
  OS.Ownership.install (stackOwned operation) (stackOwned operation).space 0 ⟨0x400080,5⟩
theorem code_adopted (operation : Logical64.Operation) :
    OS.Ownership.adopt (stackOwned operation) 0 ⟨0x400080,5⟩ = .ok (codeOwned operation,⟨2,0⟩) := by
  cases operation <;> rfl
theorem code_valid (operation : Logical64.Operation) : OS.Ownership.WellFormed (codeOwned operation) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (stack_valid operation) (code_adopted operation)).1
def raw (operation : Logical64.Operation) : Shared :=
  OS.Atomics64.empty (OS.Atomics.empty (OS.Borrowing.empty (codeOwned operation)))
theorem raw_valid (operation : Logical64.Operation) : OS.Atomics64.WellFormed (raw operation) :=
  OS.Atomics64.empty_wellFormed _ (OS.Atomics.empty_wellFormed _
    (OS.Borrowing.empty_wellFormed _ (code_valid operation)))
def enrolled (operation : Logical64.Operation) : Shared :=
  OS.Atomics64.installCell (raw operation) ⟨0,⟨0,0⟩,65536⟩
theorem target_enrolled (operation : Logical64.Operation) :
    OS.Atomics64.enroll (raw operation) 0 ⟨0,0⟩ 65536 = .ok (enrolled operation,⟨0⟩) := by rfl
theorem enrolled_valid (operation : Logical64.Operation) : OS.Atomics64.WellFormed (enrolled operation) :=
  (OS.Atomics64.enroll_wellFormed _ _ _ _ _ (raw_valid operation) (target_enrolled operation)).1
def issued (operation : Logical64.Operation) : Shared :=
  OS.Atomics64.installHandle (enrolled operation) ⟨11,⟨0⟩⟩
theorem handle_issued (operation : Logical64.Operation) :
    OS.Atomics64.issue (enrolled operation) 0 ⟨0⟩ 11 = .ok (issued operation,⟨0⟩) := by rfl
theorem issued_valid (operation : Logical64.Operation) : OS.Atomics64.WellFormed (issued operation) :=
  (OS.Atomics64.issue_wellFormed _ _ _ _ _ (enrolled_valid operation) (handle_issued operation)).1

def withCode (operation : Logical64.Operation) (short : Bool) : Shared :=
  { issued operation with legacy := { (issued operation).legacy with shared := OS.Borrowing.installLoan (issued operation).legacy.shared ⟨⟨2,0⟩,0,11,⟨0x400080,if short then 4 else 5⟩⟩ } }
theorem code_borrowed (operation : Logical64.Operation) (short : Bool) :
    OS.Atomics64.readBorrow (issued operation) 0 ⟨2,0⟩ 11 ⟨0x400080,if short then 4 else 5⟩ =
      .ok (withCode operation short,0) := by
  cases operation <;> cases short <;> rfl
theorem code_borrow_valid (operation : Logical64.Operation) (short : Bool) :
    OS.Atomics64.WellFormed (withCode operation short) :=
  OS.Atomics64.readBorrow_wellFormed _ _ _ _ _ _ (issued_valid operation) (code_borrowed operation short)
def shared (operation : Logical64.Operation) (short : Bool) : Shared :=
  { withCode operation short with legacy := { (withCode operation short).legacy with shared := OS.Borrowing.installLoan (withCode operation short).legacy.shared ⟨⟨1,0⟩,0,11,⟨32768,8⟩⟩ } }
theorem stack_borrowed (operation : Logical64.Operation) (short : Bool) :
    OS.Atomics64.readBorrow (withCode operation short) 0 ⟨1,0⟩ 11 ⟨32768,8⟩ =
      .ok (shared operation short,1) := by
  cases short <;> rfl
theorem shared_valid (operation : Logical64.Operation) (short : Bool) :
    OS.Atomics64.WellFormed (shared operation short) :=
  OS.Atomics64.readBorrow_wellFormed _ _ _ _ _ _ (code_borrow_valid operation short)
    (stack_borrowed operation short)

def input : Input := ⟨11,⟨0⟩,0,1,8192⟩
def initial (operation : Logical64.Operation) : X86.State where
  registers register := match register with
    | .rdi => 65536 | .rsi => 0x80000000ffffffff | .rsp => 32768
    | _ => 0xdeadbeef76543210
  rip := 0x400080
  flags := 0xed7
  memory := toMemory (shared operation false).legacy.shared.resources.space

theorem resources (operation : Logical64.Operation) :
    Resources (bytes operation) input (shared operation false) (initial operation) := by
  refine ⟨shared_valid operation false, ⟨⟨11,⟨0⟩⟩,⟨0,⟨0,0⟩,65536⟩,by rfl,rfl⟩,rfl,
    ⟨⟨⟨2,0⟩,0,11,⟨0x400080,5⟩⟩,rfl,rfl,rfl⟩,
    ⟨⟨⟨1,0⟩,0,11,⟨32768,8⟩⟩,rfl,rfl,rfl⟩,by rfl,
    by decide +kernel,
    by change 32768 + 8 < (2:Nat)^64; decide +kernel,
    by change canonical (32768 + 8) = true; decide +kernel⟩

theorem loaded_pre (operation : Logical64.Operation) :
    Pre (bytes operation) input (shared operation false) (initial operation) :=
  Artifact.pre_of_loaded (elf_accepted operation) prior (resources operation) rfl rfl

/-- Both the raw theorem and loaded theorem have a checked inhabited domain. -/
theorem loaded_semantics_nonvacuous (operation : Logical64.Operation) :
    ELF.load (elf operation) prior = .ok ⟨image,ELF.install (elf operation) image prior⟩ ∧
      LockedSet64.AllExecutions (initial operation)
        (ResultContract operation input (shared operation false) (initial operation)) :=
  (Artifact.elf_sound (elf_accepted operation)).2.2 prior image_fresh input
    (shared operation false) (initial operation) (resources operation) rfl rfl

-- Short code authority must not admit the complete routine, even though all
-- five executable bytes and the complete caller stack actually exist.
example (operation : Logical64.Operation) :
    ¬ Resources (bytes operation) input (shared operation true) (initial operation) := by
  intro admitted
  obtain ⟨loan,live,_,region⟩ := admitted.codeLoan
  have same : loan = ⟨⟨2,0⟩,0,11,⟨0x400080,4⟩⟩ := Option.some.inj live.symm
  subst loan
  have length := congrArg Region.length region
  change 4 = 5 at length
  contradiction

example (operation : Logical64.Operation) :
    OS.Atomics64.logicalUpdate operation.toLogicalOp (shared operation false) 12 ⟨0⟩ 0 =
      .error .wrongActor := by rfl
example (operation : Logical64.Operation) :
    OS.Atomics64.mutate (shared operation false) (.store64 0 ⟨0,0⟩ 65544 0) = .error .reserved := by rfl
example : LockedLogical64.run (fun _ => false) 2 (initial .intersection) = .error .unsupportedEncoding := by rfl
example : LockedLogical64.run (fun _ => false) 2 (initial .symmetricDifference) = .error .unsupportedEncoding := by rfl

/-- Independently worked whole-word answers, retaining distinct upper bytes. -/
def answer : Logical64.Operation → Word
  | .intersection => 0x8000000076543210
  | .union => 0xfedcba98ffffffff
  | .symmetricDifference => 0x7edcba9889abcdef
theorem answer_mathematical (operation : Logical64.Operation) :
    Logical64.MathematicalResult operation 0xfedcba9876543210 0x80000000ffffffff (answer operation) := by
  cases operation <;> unfold Logical64.MathematicalResult Logical64.HasBit answer <;> decide +kernel

/-- Every AF stream yields the independent full64 answer, exact RET/ABI, an
actual checked event and intact caller/code/neighbor cells. -/
theorem all_choices_run (operation : Logical64.Operation) (choices : Choices) :
    ∃ output changed, LockedSet64.run choices 2 (initial operation) = .ok output ∧
      OS.Atomics64.logicalUpdate operation.toLogicalOp (shared operation false) 11 ⟨0⟩
        0x80000000ffffffff = .ok changed ∧
      output.events = [changed.2.logical] ∧
      changed.2.actor = 11 ∧ changed.2.handle = ⟨0⟩ ∧ changed.2.cell = ⟨0⟩ ∧
      changed.2.logical.op = operation.toLogicalOp ∧
      changed.2.logical.event.before = 0xfedcba9876543210 ∧
      loadQWord output.state.memory 65536 = .ok (answer operation) ∧
      output.instructions = 2 ∧ output.state.rip = 8192 ∧
      output.state.registers .rsp = 32776 ∧ canonical (output.state.registers .rsp) = true ∧
      output.state.registers .rax = 0xdeadbeef76543210 ∧
      output.state.memory.read 65544 = some 0x88 ∧ output.state.memory.read 65551 = some 0x11 ∧
      output.state.memory.read 0x400080 = some 0xf0 ∧ output.state.memory.read 0x400084 = some 0xc3 ∧
      output.state.memory.read 32769 = some 0x20 ∧
      LoanAt changed.1 11 0 ⟨0x400080,5⟩ ∧ LoanAt changed.1 11 1 ⟨32768,8⟩ := by
  have reference : referenceBytes operation = bytes operation :=
    of_decide_eq_true (raw_accepted operation)
  have pre : Pre (referenceBytes operation) input (shared operation false) (initial operation) := by
    rw [reference]
    exact loaded_pre operation
  obtain ⟨output,ran,changed,success,_,_,events,_,_,rip,rsp,registers,canonical,
    readBefore,readAfter,bits,frame,_,_,_,loans⟩ :=
    Artifact.raw_run (raw_accepted operation) input (shared operation false) (initial operation) pre choices
  have actualCost := AtomicSet64.exact2 operation (loaded_pre operation) (LockedSet64.run_sound ran)
  have before : changed.2.logical.event.before = 0xfedcba9876543210 :=
    (Except.ok.inj readBefore).symm
  have result : changed.2.logical.event.after = answer operation :=
    Logical64.MathematicalResult.unique (by simpa only [before,initial] using bits) (answer_mathematical operation)
  have sound := OS.Atomics64.logicalUpdate_sound _ _ _ _ _ _ success
  have identity := OS.Atomics64.logicalUpdate_identity _ _ _ _ _ _
    ⟨11,⟨0⟩⟩ ⟨0,⟨0,0⟩,65536⟩ success (by rfl)
  have codeLoan := loans 0 ⟨⟨2,0⟩,0,11,⟨0x400080,5⟩⟩ rfl
  have stackLoan := loans 1 ⟨⟨1,0⟩,0,11,⟨32768,8⟩⟩ rfl
  refine ⟨output,changed,ran,success,events,sound.2.2.2.2.1,sound.2.2.2.2.2,identity.1,
    sound.2.1,before,?_,actualCost,rip,rsp,canonical,registers .rax (by decide +kernel),
    ?_,?_,?_,?_,?_,⟨_,codeLoan.1,rfl,rfl⟩,⟨_,stackLoan.1,rfl,rfl⟩⟩
  · simpa only [result,initial] using readAfter
  · exact (frame 65544 (by change 8 ≤ ((65544 : Word) - 65536).toNat; decide +kernel)).trans (by rfl)
  · exact (frame 65551 (by change 8 ≤ ((65551 : Word) - 65536).toNat; decide +kernel)).trans (by rfl)
  · cases operation <;> exact (frame 0x400080 (by decide +kernel)).trans (by rfl)
  · cases operation <;> exact (frame 0x400084 (by decide +kernel)).trans (by rfl)
  · exact (frame 32769 (by change 8 ≤ ((32769 : Word) - 65536).toNat; decide +kernel)).trans (by rfl)

/-- A one-instruction fuel allowance cannot silently drop the real RET. -/
example (operation : Logical64.Operation) (choices : Choices) :
    LockedSet64.run choices 1 (initial operation) = .error .exhaustedFuel := by
  obtain ⟨output,ran,contract⟩ := AtomicSet64.run operation (loaded_pre operation) choices
  exact (LockedSet64.run_sound ran).exhausted (by rw [contract.instructions]; decide +kernel)

end EDSL.Tests.AtomicSet64Artifact

#audit_edsl
#print axioms EDSL.AtomicSet64.semantics
#print axioms EDSL.AtomicSet64.exact2
#print axioms EDSL.AtomicSet64.Artifact.elf_sound
