/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine
import EDSL.X86.CallReturn.Machine
import EDSL.WordMath.Rotation
import EDSL.OS.CallResources

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.Sequential

/-!
Register ROL64 by CL under `targetProfile`: long mode, four-level canonical
fetch, stable ordinary modeled RAM, CET/IBT/shadow stacks disabled and no
asynchronous interference. No operand address, DATA or stack premise is needed.
Full Memory equality includes both permission maps. These are local model
proofs, not a refinement of physical CPUs, Linux, loading or PUSHFQ.

Intel SDM Vol.2B RCL/RCR/ROL/ROR, especially Flags Affected:
https://cdrdv2.intel.com/v1/dl/getContent/671241
https://cdrdv2-public.intel.com/782151/253667-sdm-vol-2b.pdf
The explicit masked-zero flag rule takes precedence over the unqualified OF
undefined branch in the pseudocode. Only 48/49 D3 /0, mod=3 is supported;
REX.R/X aliases, other widths/count sources/groups and memory forms reject.
-/

theorem rolCount64_lt (rcx : Word) : rolCount64 rcx < 64 := Nat.mod_lt _ (by decide)

/-- High RCX bits and even CL's high two bits cannot affect the count. -/
theorem rolCount64_low8 (rcx : Word) :
    rolCount64 rcx = (rcx.setWidth 8).toNat % 64 := by
  simp [rolCount64, BitVec.toNat_setWidth, Nat.mod_mod_of_dvd, show 64 ∣ 2^8 by decide]

/-- Bridge for an unrestricted low32 input, including MOV32's cleared high half. -/
theorem rolCount64_low32 (count : BitVec 32) :
    rolCount64 (count.setWidth 64) = count.toNat % 64 := by
  simp [rolCount64, BitVec.toNat_setWidth, Nat.mod_eq_of_lt
    (Nat.lt_trans count.isLt (by decide : 2^32 < 2^64))]

/-- Exactly three authenticated fetches suffice; there is no suffix fetch. -/
theorem decodeAt_rolCL64 {state : State} {rex modrm : Byte}
    (canonicalREX : rex = 0x48 ∨ rex = 0x49)
    (f0 : fetchByte state.memory state.rip = .ok rex)
    (f1 : fetchByte state.memory (state.rip + 1) = .ok 0xd3)
    (f2 : fetchByte state.memory (state.rip + 2) = .ok modrm)
    (registerMode : modrm.toNat / 64 = 3) (group : modrm.toNat / 8 % 8 = 0) :
    decodeAt state = .ok (.rolCL64 (rexModRMRM rex modrm)) := by
  have decoded : decodeREXWAt state rex = .ok (.rolCL64 (rexModRMRM rex modrm)) := by
    unfold decodeREXWAt
    rw [f1, ok_bind]
    rcases canonicalREX with rfl | rfl <;> simp only [↓reduceIte] <;>
      rw [f2, ok_bind] <;> simp [registerMode, group]
  rcases canonicalREX with rfl | rfl <;>
    simpa [decodeAt, X86.decodeAt, decodeNewAt, f0] using decoded

/-- Unsupported REX aliases reject before attempting to fetch a ModRM. The
enclosing decoder is responsible for authenticating the supplied REX byte. -/
theorem decodeREXWAt_rolCL64_badREX {state : State} {rex : Byte}
    (opcode : fetchByte state.memory (state.rip + 1) = .ok 0xd3)
    (not48 : rex ≠ 0x48) (not49 : rex ≠ 0x49) :
    decodeREXWAt state rex = .error .unsupportedEncoding := by
  unfold decodeREXWAt
  rw [opcode, ok_bind]
  simp only [↓reduceIte]
  rw [ite_eq_left (And.intro not48 not49)]
  rfl

/-- Invalid group or memory mode rejects after ModRM, independently of every
possible address/immediate suffix. Unsupported code is not a defect claim. -/
theorem decodeAt_rolCL64_rejects {state : State} {rex modrm : Byte}
    (canonicalREX : rex = 0x48 ∨ rex = 0x49)
    (f0 : fetchByte state.memory state.rip = .ok rex)
    (f1 : fetchByte state.memory (state.rip + 1) = .ok 0xd3)
    (f2 : fetchByte state.memory (state.rip + 2) = .ok modrm)
    (unsupported : modrm.toNat / 64 ≠ 3 ∨ modrm.toNat / 8 % 8 ≠ 0) :
    decodeAt state = .error .unsupportedEncoding := by
  have decoded : decodeREXWAt state rex = .error .unsupportedEncoding := by
    unfold decodeREXWAt
    rw [f1, ok_bind]
    rcases canonicalREX with rfl | rfl <;> simp only [↓reduceIte] <;>
      rw [f2, ok_bind] <;> simp [unsupported]
  rcases canonicalREX with rfl | rfl <;>
    simpa [decodeAt, X86.decodeAt, decodeNewAt, f0] using decoded

theorem decodeAt_rolCL64_modrm_fault {state : State} {rex : Byte} {error : Error}
    (canonicalREX : rex = 0x48 ∨ rex = 0x49)
    (f0 : fetchByte state.memory state.rip = .ok rex)
    (f1 : fetchByte state.memory (state.rip + 1) = .ok 0xd3)
    (f2 : fetchByte state.memory (state.rip + 2) = .error error) :
    decodeAt state = .error error := by
  have decoded : decodeREXWAt state rex = .error error := by
    unfold decodeREXWAt
    rw [f1, ok_bind]
    rcases canonicalREX with rfl | rfl <;> simp only [↓reduceIte] <;>
      rw [f2, error_bind] <;> simp
  rcases canonicalREX with rfl | rfl <;>
    simpa [decodeAt, X86.decodeAt, decodeNewAt, f0] using decoded

/-- Exact executor result; both operands are from the old state even for RCX. -/
theorem execute_rolCL64 (state : State) (destination : Register) (choice : Bool) :
    execute state (.rolCL64 destination) choice =
      .ok ⟨.next { state.writeRegister destination
        ((state.registers destination).rotateLeft (rolCount64 (state.registers .rcx))) with
        rip := state.rip + 3,
        flags := rolFlags64 state.flags
          ((state.registers destination).rotateLeft (rolCount64 (state.registers .rcx)))
          (rolCount64 (state.registers .rcx)) choice }, []⟩ := rfl

theorem step_rolCL64 {state : State} {destination : Register}
    (decoded : decodeAt state = .ok (.rolCL64 destination)) (choice : Bool) :
    step choice state = execute state (.rolCL64 destination) choice :=
  step_eq_execute choice decoded

/-- Independent bit-origin relation plus the complete architectural frame.
RSP and RCX may be destinations; no prestate restrictions are imposed. -/
theorem execute_rolCL64_context (state : State) (destination : Register) (choice : Bool) :
    ∃ final, execute state (.rolCL64 destination) choice = .ok ⟨.next final, []⟩ ∧
      WordMath.IsRotateLeft64 (state.registers destination)
        (rolCount64 (state.registers .rcx)) (final.registers destination) ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧
      final.flags = rolFlags64 state.flags (final.registers destination)
        (rolCount64 (state.registers .rcx)) choice ∧
      final.flags &&& ~~~(0x801 : Word) = state.flags &&& ~~~(0x801 : Word) ∧
      final.rip = state.rip + 3 := by
  refine ⟨_, rfl, ?_, ?_, rfl, ?_, rolFlags64_frame .., rfl⟩
  · simpa [State.writeRegister] using
      WordMath.rotateLeft64_satisfies (state.registers destination) (rolCount64 (state.registers .rcx))
  · intro register different
    simp [State.writeRegister, different]
  · simp [State.writeRegister]

/-- A zero masked count preserves the entire GPR function and every flag. -/
theorem execute_rolCL64_zero (state : State) (destination : Register) (choice : Bool)
    (zero : rolCount64 (state.registers .rcx) = 0) :
    execute state (.rolCL64 destination) choice =
      .ok ⟨.next { state with rip := state.rip + 3 }, []⟩ := by
  rw [execute_rolCL64]
  have same : (state.registers destination).rotateLeft 0 = state.registers destination := by
    apply WordMath.isRotateLeft_unique (WordMath.rotateLeft64_satisfies _ _)
    intro i bound
    simp [WordMath.rotationOrigin, Nat.mod_eq_of_lt bound]
  simp only [zero, same, rolFlags64, ↓reduceIte]
  congr 4
  funext register
  by_cases h : register = destination <;> simp [State.writeRegister, h]

theorem rolCL64_effects (state : State) (destination : Register) :
    (Instruction.rolCL64 destination).length = 3 ∧
    (Instruction.rolCL64 destination).operandReads state = [] ∧
    (Instruction.rolCL64 destination).storeIntent state = none ∧
    (Instruction.rolCL64 destination).storeIntent64 state = none ∧
    (Instruction.rolCL64 destination).isLocked = false ∧
    (Instruction.rolCL64 destination).choosesAF = false ∧
    ∀ choice, ∃ final, execute state (.rolCL64 destination) choice = .ok ⟨.next final, []⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨_, rfl⟩⟩

theorem rolFlags64_preserved_bit (old result : Word) (count : Nat) (choice : Bool)
    (i : Nat) (notCarry : i ≠ 0) (notOverflow : i ≠ 11) :
    (rolFlags64 old result count choice).getLsbD i = old.getLsbD i := by
  by_cases bound : i < 64
  · have frame := congrArg (fun flags : Word => flags.getLsbD i) (rolFlags64_frame old result count choice)
    have mask : (0x801 : Word).getLsbD i = false := by
      change ((2^0 ||| 2^11) : Nat).testBit i = false
      simp only [Nat.testBit_or, Nat.testBit_two_pow]
      simp [Ne.symm notCarry, Ne.symm notOverflow]
    simpa only [BitVec.getLsbD_and, BitVec.getLsbD_not, bound, decide_true,
      mask, Bool.not_false, Bool.and_true] using frame
  · simp [BitVec.getLsbD_of_ge, Nat.le_of_not_lt bound]

/-- Independent flag table: count zero requires whole-word equality; nonzero
requires CF and a complete frame outside CF/OF, and count one defines OF.
There is no restriction on OF for a larger count. -/
def RolFlags64Admissible (old result : Word) (count : Nat) (actual : Word) : Prop :=
  if count = 0 then actual = old else
    actual &&& ~~~(0x801 : Word) = old &&& ~~~(0x801 : Word) ∧
    actual.getLsbD 0 = result.getLsbD 0 ∧
    (count = 1 → actual.getLsbD 11 = xor (result.getLsbD 63) (result.getLsbD 0))

private theorem rolFlags64_unique (old result actual : Word) (count : Nat) (choice : Bool)
    (nonzero : count ≠ 0)
    (frame : actual &&& ~~~(0x801 : Word) = old &&& ~~~(0x801 : Word))
    (carry : actual.getLsbD 0 = result.getLsbD 0)
    (overflow : actual.getLsbD 11 =
      if count = 1 then xor (result.getLsbD 63) (result.getLsbD 0) else choice) :
    actual = rolFlags64 old result count choice := by
  apply BitVec.eq_of_getLsbD_eq
  intro i bound
  by_cases h0 : i = 0
  · subst i; exact carry.trans (rolFlags64_bits old result count choice nonzero).1.symm
  by_cases h11 : i = 11
  · subst i; exact overflow.trans (rolFlags64_bits old result count choice nonzero).2.symm
  have mask : (0x801 : Word).getLsbD i = false := by
    change ((2^0 ||| 2^11) : Nat).testBit i = false
    simp only [Nat.testBit_or, Nat.testBit_two_pow]
    simp [Ne.symm h0, Ne.symm h11]
  have same := congrArg (fun flags : Word => flags.getLsbD i) frame
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, bound, decide_true,
    mask, Bool.not_false, Bool.and_true] at same
  exact same.trans (rolFlags64_preserved_bit old result count choice i h0 h11).symm

/-- The observed OF is always an exact witness, including inactive choices. -/
theorem rolFlags64_observed_witness {old result actual : Word} {count : Nat}
    (admitted : RolFlags64Admissible old result count actual) :
    actual = rolFlags64 old result count (actual.getLsbD 11) := by
  by_cases zero : count = 0
  · simpa [RolFlags64Admissible, rolFlags64, zero] using admitted
  · have parts : actual &&& ~~~(0x801 : Word) = old &&& ~~~(0x801 : Word) ∧
        actual.getLsbD 0 = result.getLsbD 0 ∧
        (count = 1 → actual.getLsbD 11 = xor (result.getLsbD 63) (result.getLsbD 0)) := by
      simpa only [RolFlags64Admissible, zero, ↓reduceIte] using admitted
    apply rolFlags64_unique old result actual count _ zero parts.1 parts.2.1
    by_cases one : count = 1
    · simp only [one, ↓reduceIte]; exact parts.2.2 one
    · simp [one]

theorem rolFlags64_admissible_iff (old result : Word) (count : Nat) (actual : Word) :
    RolFlags64Admissible old result count actual ↔ ∃ choice, actual = rolFlags64 old result count choice := by
  constructor
  · exact fun admitted => ⟨actual.getLsbD 11, rolFlags64_observed_witness admitted⟩
  · rintro ⟨choice, rfl⟩
    by_cases zero : count = 0
    · simp [RolFlags64Admissible, rolFlags64, zero]
    · simp only [RolFlags64Admissible, zero, ↓reduceIte]
      exact ⟨rolFlags64_frame .., (rolFlags64_bits old result count choice zero).1,
        fun one => by simpa [one] using (rolFlags64_bits old result count choice zero).2⟩

theorem rolFlags64_choices (old result : Word) (count : Nat) (left right : Bool) :
    rolFlags64 old result count left &&& ~~~(0x800 : Word) =
      rolFlags64 old result count right &&& ~~~(0x800 : Word) := by
  unfold rolFlags64
  split
  · rfl
  · by_cases one : count = 1
    · simp [one]
    · cases left <;> cases right <;>
        simp [one, flagBit, BitVec.and_or_distrib_right]

theorem rolFlags64_choice_injective (old result : Word) (count : Nat) (left right : Bool)
    (undefinedOF : 1 < count) :
    rolFlags64 old result count left = rolFlags64 old result count right ↔ left = right := by
  have nonzero : count ≠ 0 := by omega
  have notOne : count ≠ 1 := by omega
  constructor
  · intro same
    have bit := congrArg (fun flags : Word => flags.getLsbD 11) same
    simpa only [(rolFlags64_bits old result count left nonzero).2,
      (rolFlags64_bits old result count right nonzero).2, notOne, ↓reduceIte] using bit
  · rintro rfl; rfl

theorem rolFlags64_admits_both (old result : Word) (count : Nat) :
    RolFlags64Admissible old result count (rolFlags64 old result count false) ∧
    RolFlags64Admissible old result count (rolFlags64 old result count true) :=
  ⟨(rolFlags64_admissible_iff ..).mpr ⟨false, rfl⟩,
    (rolFlags64_admissible_iff ..).mpr ⟨true, rfl⟩⟩

theorem execute_rolCL64_flags {state final : State} {destination : Register}
    {choice : Bool} {reads : List Read}
    (actual : execute state (.rolCL64 destination) choice = .ok ⟨.next final, reads⟩) :
    RolFlags64Admissible state.flags (final.registers destination)
      (rolCount64 (state.registers .rcx)) final.flags ∧
    final.flags.getLsbD 4 = state.flags.getLsbD 4 := by
  cases actual
  constructor
  · simp only [State.writeRegister, ↓reduceIte]
    exact (rolFlags64_admissible_iff ..).mpr ⟨choice, rfl⟩
  · exact rolFlags64_preserved_bit _ _ _ _ 4 (by decide) (by decide)

theorem execute_rolCL64_choices (state : State) (destination : Register) (left right : Bool) :
    ∃ first second,
      execute state (.rolCL64 destination) left = .ok ⟨.next first, []⟩ ∧
      execute state (.rolCL64 destination) right = .ok ⟨.next second, []⟩ ∧
      first.registers = second.registers ∧ first.memory = second.memory ∧ first.rip = second.rip ∧
      first.flags &&& ~~~(0x800 : Word) = second.flags &&& ~~~(0x800 : Word) ∧
      (1 < rolCount64 (state.registers .rcx) →
        first.flags.getLsbD 11 = left ∧ second.flags.getLsbD 11 = right) := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rolFlags64_choices .., ?_⟩
  intro undefinedOF
  have nonzero : rolCount64 (state.registers .rcx) ≠ 0 := by omega
  have notOne : rolCount64 (state.registers .rcx) ≠ 1 := by omega
  simp only [(rolFlags64_bits _ _ _ left nonzero).2,
    (rolFlags64_bits _ _ _ right nonzero).2, notOne, ↓reduceIte, and_self]

/-- AF metadata has exactly its historical meaning, including for ROL. -/
theorem Instruction.choiceFlag_af_iff (instruction : Instruction) (state : State) :
    instruction.choiceFlag state = some .af ↔ instruction.choosesAF = true := by
  cases instruction <;> simp [Instruction.choiceFlag, Instruction.choosesAF]

/-- Every active choice, regardless of flag identity, changes only that named
bit. Both values occur in the model; no claim of physical variability follows. -/
theorem execute_choice_context (state : State) (instruction : Instruction) (flag : ChoiceFlag)
    (selected : instruction.choiceFlag state = some flag) (left right : Bool) :
    ∃ first second,
      execute state instruction left = .ok ⟨.next first, []⟩ ∧
      execute state instruction right = .ok ⟨.next second, []⟩ ∧
      first.registers = second.registers ∧ first.memory = second.memory ∧ first.rip = second.rip ∧
      first.flags &&& ~~~flag.mask = second.flags &&& ~~~flag.mask ∧
      first.flags.getLsbD flag.bitIndex = left ∧ second.flags.getLsbD flag.bitIndex = right := by
  cases instruction <;> simp [Instruction.choiceFlag, Instruction.choosesAF] at selected
  case logicalReg32 operation destination source prefixed =>
    cases selected
    exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, logicalFlags32_choices ..,
      (logicalFlags32_bits ..).2.2.1, (logicalFlags32_bits ..).2.2.1⟩
  case logicalImm32 operation destination immediate prefixed =>
    cases selected
    exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, logicalFlags32_choices ..,
      (logicalFlags32_bits ..).2.2.1, (logicalFlags32_bits ..).2.2.1⟩
  case xorSelf32 destination =>
    cases selected
    exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, logicalFlags32_choices ..,
      (logicalFlags32_bits ..).2.2.1, (logicalFlags32_bits ..).2.2.1⟩
  case test32 leftReg rightReg prefixed =>
    cases selected
    exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, logicalFlags32_choices ..,
      (logicalFlags32_bits ..).2.2.1, (logicalFlags32_bits ..).2.2.1⟩
  case test64 leftReg rightReg =>
    cases selected
    exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, logicalFlags64_choices ..,
      (logicalFlags64_bits ..).2.2.1, (logicalFlags64_bits ..).2.2.1⟩
  case logicalReg64 operation destination source =>
    cases selected
    exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, logicalFlags64_choices ..,
      (logicalFlags64_bits ..).2.2.1, (logicalFlags64_bits ..).2.2.1⟩
  case shrOne64 destination =>
    cases selected
    exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, shrOneFlags64_choices ..,
      (shrOneFlags64_bits ..).2.2.1, (shrOneFlags64_bits ..).2.2.1⟩
  case rolCL64 destination =>
    rcases selected with ⟨active, rfl⟩
    obtain ⟨first, second, e1, e2, registers, memory, pc, frame, bits⟩ :=
      execute_rolCL64_choices state destination left right
    exact ⟨first, second, e1, e2, registers, memory, pc, frame, bits active⟩

/-- A complete state frame outside the permitted undefined bit. This relation
does not evaluate an instruction or select a value for its undefined flag. -/
structure ChoiceStateAdmissible (flag : ChoiceFlag) (baseline actual : State) : Prop where
  registers : actual.registers = baseline.registers
  memory : actual.memory = baseline.memory
  rip : actual.rip = baseline.rip
  flags : actual.flags &&& ~~~flag.mask = baseline.flags &&& ~~~flag.mask

theorem ChoiceFlag.mask_bit (flag : ChoiceFlag) (i : Nat) :
    flag.mask.getLsbD i = decide (i = flag.bitIndex) := by
  cases flag with
  | af =>
    change (2^4 : Nat).testBit i = decide (i = 4)
    rw [Nat.testBit_two_pow]; simp [eq_comm]
  | of =>
    change (2^11 : Nat).testBit i = decide (i = 11)
    rw [Nat.testBit_two_pow]; simp [eq_comm]

private theorem choiceFlags_unique (flag : ChoiceFlag) (left right : Word)
    (frame : left &&& ~~~flag.mask = right &&& ~~~flag.mask)
    (bit : left.getLsbD flag.bitIndex = right.getLsbD flag.bitIndex) : left = right := by
  apply BitVec.eq_of_getLsbD_eq
  intro i bound
  by_cases same : i = flag.bitIndex
  · simpa only [same] using bit
  · have h := congrArg (fun flags : Word => flags.getLsbD i) frame
    simpa only [BitVec.getLsbD_and, BitVec.getLsbD_not, bound, decide_true,
      ChoiceFlag.mask_bit, same, decide_false, Bool.not_false, Bool.and_true] using h

/-- The named observed flag is an exact executor witness for ANY active
choice instruction, provided the complete defined-state frame agrees. -/
theorem execute_choice_observed_witness {state baseline actual : State}
    {instruction : Instruction} {flag : ChoiceFlag}
    (selected : instruction.choiceFlag state = some flag)
    (reference : execute state instruction false = .ok ⟨.next baseline, []⟩)
    (admitted : ChoiceStateAdmissible flag baseline actual) :
    execute state instruction (actual.flags.getLsbD flag.bitIndex) = .ok ⟨.next actual, []⟩ := by
  obtain ⟨first, second, e1, e2, registers, memory, pc, flags, _, bit⟩ :=
    execute_choice_context state instruction flag selected false (actual.flags.getLsbD flag.bitIndex)
  have same : first = baseline := by rw [reference] at e1; cases e1; rfl
  subst first
  have finalFlags : actual.flags = second.flags :=
    choiceFlags_unique flag actual.flags second.flags (admitted.flags.trans flags) bit.symm
  have finalState : actual = second := by
    have regs := admitted.registers.trans registers
    have mem := admitted.memory.trans memory
    have rip := admitted.rip.trans pc
    cases actual; cases second
    exact (State.mk.injEq ..).mpr ⟨regs, rip, finalFlags, mem⟩
  rw [← finalState] at e2
  exact e2

/-- Independent state admissibility exactly exhausts the one-bit execution
choices. Inactive choices instead use `execute_choice_independent`. -/
theorem execute_choice_admissible_iff {state baseline actual : State}
    {instruction : Instruction} {flag : ChoiceFlag}
    (selected : instruction.choiceFlag state = some flag)
    (reference : execute state instruction false = .ok ⟨.next baseline, []⟩) :
    ChoiceStateAdmissible flag baseline actual ↔
      ∃ choice, execute state instruction choice = .ok ⟨.next actual, []⟩ := by
  constructor
  · intro admitted
    exact ⟨_, execute_choice_observed_witness selected reference admitted⟩
  · rintro ⟨choice, executed⟩
    obtain ⟨first, second, e1, e2, registers, memory, pc, flags, _⟩ :=
      execute_choice_context state instruction flag selected false choice
    rw [reference] at e1
    rw [executed] at e2
    cases e1; cases e2
    exact ⟨registers.symm, memory.symm, pc.symm, flags.symm⟩

/-- Present OS caller/code loans, ownership epochs and maps survive this
authenticated production step in the same complete shared world. RSP changes
do not confer permission to read a replacement return slot. -/
theorem current_rolCL64_step {call : OS.CallResources.Call} {shared : OS.CallResources.Shared}
    {before : State} {destination : Register}
    (current : OS.CallResources.Current call shared before)
    (decoded : decodeAt before = .ok (.rolCL64 destination)) (choice : Bool) :
    ∃ after, step choice before = .ok ⟨.next after, []⟩ ∧
      OS.CallResources.Current call shared after ∧
      WordMath.IsRotateLeft64 (before.registers destination)
        (rolCount64 (before.registers .rcx)) (after.registers destination) ∧
      (∀ register, register ≠ destination → after.registers register = before.registers register) ∧
      after.memory = before.memory ∧ after.rip = before.rip + 3 := by
  obtain ⟨after, executed, value, registers, memory, _, _, pc⟩ :=
    execute_rolCL64_context before destination choice
  refine ⟨after, ?_, current.sameMemory memory, value, registers, memory, pc⟩
  rw [step_eq_execute choice decoded]
  exact executed

end EDSL.X86.Sequential

namespace EDSL.X86.CallReturn

theorem execute_choice_independent (state : State) (instruction : Instruction) (left right : Bool)
    (noChoice : instruction.choiceFlag state = none) :
    execute state instruction left = execute state instruction right := by
  cases instruction with
  | sequential old => exact Sequential.execute_choice_independent state old left right noChoice
  | callRelative32 _ | push64 _ _ | pop64 _ _ | leaDisp8 _ _ _ => rfl

theorem execute_rolCL64 (state : State) (destination : Register) (choice : Bool) :
    execute state (liftSequential (.rolCL64 destination)) choice =
      Sequential.execute state (.rolCL64 destination) choice :=
  execute_liftSequential state (.rolCL64 destination) choice

end EDSL.X86.CallReturn
