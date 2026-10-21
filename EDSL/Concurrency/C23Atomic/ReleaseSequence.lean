/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Coherence
import EDSL.Audit

/-!
Release-sequence prefixes and induction over actual RMW read-from sources.
Only structural well-formedness and the RMW predecessor condition are needed;
clients need not establish full atomic-fragment legality first. Modification
ranks may have gaps, and locations and values remain arbitrary types.

The selected RF edge supplies the source identity and observed value. An RMW's
read and write share one event and object; equal values never select a writer.
These model lemmas supply no source/native mapping, synchronization or
happens-before legality, fairness or corpus claim.
-/

set_option autoImplicit false

namespace EDSL.Concurrency.C23Atomic

variable {Location Value : Type} {c : Candidate Location Value}

/-- The actual RMW constructor supplies a read on its write's object. -/
private theorem rmw_read_of_write {index : Nat} {location : Location} {stored : Value}
    (rmw : IsRMW c index) (written : Writes c index location stored) :
    ∃ observed, Reads c index location observed := by
  obtain ⟨event, live, actualRMW⟩ := rmw
  obtain ⟨other, otherLive, object, _⟩ := written
  have sameEvent : other = event := Option.some.inj (otherLive.symm.trans live)
  subst other
  have hasRead : ∃ value, event.access.readValue = some value := by
    cases event with
    | mk _ _ access =>
        cases access with
        | «initialize» _ => cases actualRMW
        | load _ _ => cases actualRMW
        | store _ _ => cases actualRMW
        | rmw _ before _ => exact ⟨before, rfl⟩
  obtain ⟨observed, readValue⟩ := hasRead
  exact ⟨observed, event, live, object, readValue⟩

/-- Distinct members are strictly above their head: rank uniqueness is used
only for writes to the same object, with no equality assumption on values. -/
theorem ReleaseMember.rank_lt {head member : Nat} (wellFormed : WellFormed c)
    (membership : ReleaseMember c head member) (different : head ≠ member) :
    c.rank head < c.rank member := by
  obtain ⟨location, headValue, memberValue, headWrite, memberWrite, lower, _⟩ :=
    membership.2
  by_cases strict : c.rank head < c.rank member
  · exact strict
  · have sameRank := Nat.le_antisymm lower (Nat.le_of_not_lt strict)
    exact False.elim (different (wellFormed.rankUnique head member location headValue
      memberValue headWrite memberWrite sameRank))

/-- The actual RF source of a non-head RMW member is an earlier member.
If it were below the head, the head would contradict immediate-predecessor
legality. No adjacency of numeric ranks or full `Legal` premise is required. -/
theorem ReleaseMember.source_prefix {head member writer : Nat}
    (wellFormed : WellFormed c) (membership : ReleaseMember c head member)
    (different : head ≠ member) (rmw : IsRMW c member)
    (source : ReadsFrom c member writer)
    (predecessor : ModBefore c writer member ∧
      ∀ middle, ModBefore c writer middle → ¬ ModBefore c middle member) :
    ReleaseMember c head writer ∧ c.rank writer < c.rank member := by
  obtain ⟨location, headValue, memberValue, headWrite, memberWrite, _, _⟩ :=
    membership.2
  obtain ⟨observed, read⟩ := rmw_read_of_write rmw memberWrite
  have sourceWrite : Writes c writer location observed := source.source read
  have sourceBefore : c.rank writer < c.rank member := by
    obtain ⟨_, _, _, _, _, before⟩ := predecessor.1
    exact before
  have headBefore : c.rank head < c.rank member :=
    ReleaseMember.rank_lt wellFormed membership different
  have lower : c.rank head ≤ c.rank writer := by
    apply Nat.le_of_not_lt
    intro belowHead
    have beforeHead : ModBefore c writer head :=
      ⟨location, observed, headValue, sourceWrite, headWrite, belowHead⟩
    have beforeMember : ModBefore c head member :=
      ⟨location, headValue, memberValue, headWrite, memberWrite, headBefore⟩
    exact predecessor.2 head beforeHead beforeMember
  exact ⟨releaseMember_prefix membership headWrite sourceWrite lower
    (Nat.le_of_lt sourceBefore), sourceBefore⟩

/-- Prove a property of every release-sequence member from its head, a
same-thread case and an RMW step from its actual RF source. The same-thread
case receives strict modification-rank order, not an extra sequencing edge.
RMW sources exist by `WellFormed.readsSource` applied to the actual RMW read;
their membership and smaller rank follow from `source_prefix`.

The predecessor premise is exactly the universal RMW obligation exposed by
`Legal.rmwPredecessor`, independently of the other legality conditions. -/
theorem ReleaseMember.induction {head : Nat} (wellFormed : WellFormed c)
    (predecessor : ∀ {index writer}, IsRMW c index → ReadsFrom c index writer →
      ModBefore c writer index ∧
        ∀ middle, ModBefore c writer middle → ¬ ModBefore c middle index)
    {P : Nat → Prop} (headCase : P head)
    (sameThreadStep : ∀ {member}, ReleaseMember c head member →
      SameThread c head member → c.rank head < c.rank member → P member)
    (rmwStep : ∀ {member writer}, ReleaseMember c head member →
      IsRMW c member → ReadsFrom c member writer → ReleaseMember c head writer →
      c.rank writer < c.rank member → P writer → P member)
    {member : Nat} (membership : ReleaseMember c head member) : P member := by
  have allRanks : ∀ rank index, c.rank index = rank →
      ReleaseMember c head index → P index := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
        intro index atRank memberOf
        by_cases isHead : head = index
        · cases isHead
          exact headCase
        · have headBefore : c.rank head < c.rank index :=
            ReleaseMember.rank_lt wellFormed memberOf isHead
          obtain ⟨location, _, memberValue, _, memberWrite, _, contiguous⟩ :=
            memberOf.2
          rcases contiguous index memberValue memberWrite headBefore (Nat.le_refl _) with
            same | rmw
          · exact sameThreadStep memberOf same headBefore
          · obtain ⟨observed, read⟩ := rmw_read_of_write rmw memberWrite
            obtain ⟨writer, source⟩ := wellFormed.readsSource index location observed read
            obtain ⟨sourceMember, sourceBefore⟩ :=
              ReleaseMember.source_prefix wellFormed memberOf isHead rmw source
                (predecessor rmw source)
            have smaller : c.rank writer < rank := by
              rw [← atRank]
              exact sourceBefore
            have sourceCase : P writer :=
              ih (c.rank writer) smaller writer rfl sourceMember
            exact rmwStep memberOf rmw source sourceMember sourceBefore sourceCase
  exact allRanks (c.rank member) member rfl membership

end EDSL.Concurrency.C23Atomic

#audit_edsl
