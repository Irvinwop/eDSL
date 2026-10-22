/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Model

set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-- The arithmetic status bits that an instruction may leave undefined.
The choice domain names bits, independently of any particular opcode. -/
inductive StatusFlag where
  | cf | pf | af | zf | sf | of
  deriving DecidableEq, Repr

/-- A complete, independently chosen valuation of the arithmetic status bits.
An instruction uses only its declared undefined bits; defined bits are supplied
by its arithmetic semantics. This does not change the existing Bool API. -/
structure FlagChoices where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving DecidableEq, Repr

namespace FlagChoices

def get (choices : FlagChoices) : StatusFlag → Bool
  | .cf => choices.cf
  | .pf => choices.pf
  | .af => choices.af
  | .zf => choices.zf
  | .sf => choices.sf
  | .of => choices.of

/-- Construct one complete valuation from arbitrary requested bit values. -/
def ofFunction (values : StatusFlag → Bool) : FlagChoices :=
  ⟨values .cf, values .pf, values .af, values .zf, values .sf, values .of⟩

@[simp] theorem get_ofFunction (values : StatusFlag → Bool) (flag : StatusFlag) :
    (ofFunction values).get flag = values flag := by
  cases flag <;> rfl

/-- No relationship between different selected status bits is required. -/
theorem independent_selection (values : StatusFlag → Bool) :
    ∃ choices : FlagChoices, ∀ flag, choices.get flag = values flag :=
  ⟨ofFunction values, get_ofFunction values⟩

/-- A compatibility valuation; universal claims about this diagonal alone do
not establish universal claims about independently undefined flags. -/
def uniform (value : Bool) : FlagChoices := ofFunction fun _ => value

@[simp] theorem get_uniform (value : Bool) (flag : StatusFlag) :
    (uniform value).get flag = value := by
  simp [uniform]

/-- Replace one selected bit and retain all other choices. -/
def set (choices : FlagChoices) (flag : StatusFlag) (value : Bool) : FlagChoices :=
  match flag with
  | .cf => { choices with cf := value }
  | .pf => { choices with pf := value }
  | .af => { choices with af := value }
  | .zf => { choices with zf := value }
  | .sf => { choices with sf := value }
  | .of => { choices with of := value }

@[simp] theorem get_set (choices : FlagChoices) (selected queried : StatusFlag) (value : Bool) :
    (choices.set selected value).get queried =
      if queried = selected then value else choices.get queried := by
  cases selected <;> cases queried <;> simp [get, set]

/-- Valuations agree on the bits the instruction actually consults.
Inactive bits may differ freely. Repeated entries do not strengthen agreement. -/
def Agreement (active : List StatusFlag) (left right : FlagChoices) : Prop :=
  ∀ flag, flag ∈ active → left.get flag = right.get flag

theorem Agreement.refl (active : List StatusFlag) (choices : FlagChoices) :
    Agreement active choices choices := fun _ _ => rfl

theorem Agreement.symm {active : List StatusFlag} {left right : FlagChoices}
    (agree : Agreement active left right) : Agreement active right left :=
  fun flag member => (agree flag member).symm

theorem Agreement.trans {active : List StatusFlag} {left middle right : FlagChoices}
    (first : Agreement active left middle) (second : Agreement active middle right) :
    Agreement active left right :=
  fun flag member => (first flag member).trans (second flag member)

theorem Agreement.mono {active smaller : List StatusFlag} {left right : FlagChoices}
    (agree : Agreement active left right)
    (subset : ∀ flag, flag ∈ smaller → flag ∈ active) : Agreement smaller left right :=
  fun flag member => agree flag (subset flag member)

/-- One finite representative for each combination of active bits. Inactive
bits are false. Duplicate active entries are allowed and may repeat rows;
the coverage theorem does not depend on a distinctness precondition. -/
def representatives : List StatusFlag → List FlagChoices
  | [] => [uniform false]
  | flag :: rest =>
      (representatives rest).map (fun choices => choices.set flag false) ++
      (representatives rest).map (fun choices => choices.set flag true)

theorem representatives_length (active : List StatusFlag) :
    (representatives active).length = 2 ^ active.length := by
  induction active with
  | nil => rfl
  | cons flag rest induction =>
    simp only [representatives, List.length_append, List.length_map, induction,
      List.length_cons, Nat.pow_succ, Nat.mul_two]

/-- Every complete valuation has a representative with exactly the same
active bits, including when the active list contains duplicates. -/
theorem representatives_complete (active : List StatusFlag) (choices : FlagChoices) :
    ∃ candidate ∈ representatives active, Agreement active choices candidate := by
  induction active with
  | nil =>
    exact ⟨uniform false, by simp [representatives], by simp [Agreement]⟩
  | cons flag rest induction =>
    obtain ⟨candidate, member, agree⟩ := induction
    refine ⟨candidate.set flag (choices.get flag), ?_, ?_⟩
    · simp only [representatives, List.mem_append, List.mem_map]
      cases choices.get flag with
      | false => exact .inl ⟨candidate, member, rfl⟩
      | true => exact .inr ⟨candidate, member, rfl⟩
    · intro queried present
      rcases List.mem_cons.mp present with same | inRest
      · subst queried
        simp
      · by_cases same : queried = flag
        · subst queried
          simp
        · simpa [get_set, same] using agree queried inRest

/-- The invariant needed to replace an infinite-looking valuation quantifier
by its finite representatives. It must hold for the actual client predicate. -/
def Invariant (active : List StatusFlag) (predicate : FlagChoices → Prop) : Prop :=
  ∀ {left right}, Agreement active left right → (predicate left ↔ predicate right)

/-- Finite enumeration is complete only under explicit inactive-bit
independence. No representative is treated as a preferred physical value. -/
theorem forall_iff_representatives (active : List StatusFlag) (predicate : FlagChoices → Prop)
    (independent : Invariant active predicate) :
    (∀ choices, predicate choices) ↔
      ∀ candidate ∈ representatives active, predicate candidate := by
  constructor
  · intro all candidate _
    exact all candidate
  · intro admitted choices
    obtain ⟨candidate, member, agree⟩ := representatives_complete active choices
    exact (independent agree).mpr (admitted candidate member)

/-- Executable finite reflection of a decidable client predicate. -/
def check (active : List StatusFlag) (predicate : FlagChoices → Prop)
    [DecidablePred predicate] : Bool :=
  (representatives active).all fun choices => decide (predicate choices)

theorem check_eq_true_iff (active : List StatusFlag) (predicate : FlagChoices → Prop)
    [DecidablePred predicate] (independent : Invariant active predicate) :
    check active predicate = true ↔ ∀ choices, predicate choices := by
  rw [forall_iff_representatives active predicate independent]
  simp only [check, List.all_eq_true, decide_eq_true_eq]

/-- Four independently undefined bits have sixteen representatives. -/
theorem four_status_representatives :
    (representatives [.pf, .af, .zf, .sf]).length = 16 := by
  rw [representatives_length]
  rfl

/-- Every requested PF/AF/ZF/SF pattern is admitted by that finite domain,
including patterns whose bits differ from one another. -/
theorem four_status_patterns (pf af zf sf : Bool) :
    ∃ choices ∈ representatives [.pf, .af, .zf, .sf],
      choices.get .pf = pf ∧ choices.get .af = af ∧
      choices.get .zf = zf ∧ choices.get .sf = sf := by
  let desired : FlagChoices := ⟨false, pf, af, zf, sf, false⟩
  obtain ⟨choices, member, agree⟩ :=
    representatives_complete [.pf, .af, .zf, .sf] desired
  refine ⟨choices, member, ?_, ?_, ?_, ?_⟩
  · exact (agree .pf (by simp)).symm
  · exact (agree .af (by simp)).symm
  · exact (agree .zf (by simp)).symm
  · exact (agree .sf (by simp)).symm

end FlagChoices
end EDSL.X86.Sequential
