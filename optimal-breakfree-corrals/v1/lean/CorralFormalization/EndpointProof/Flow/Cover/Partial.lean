import CorralFormalization.EndpointProof.Selector.Assembly.Matchings

/-!
Deterministic open-cover surgery for the iterative part of the paired cover construction.

A partial cover has an actual matching on every vertex except its current
open set. `extend` consumes a supplied actual matching for the old open set,
a fresh next set and a fresh paired augmentation, leaving a new open set.
This file does not construct a six-root supplier or establish the eventual
availability/budget of any flow.
-/

open scoped Classical

namespace EndpointFlow.Cover

open EndpointSelector EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [DecidableEq G]

/-- An exact matching of an original set plus paired reservoir vertices,
except for an explicitly retained output set. -/
structure PartialCover (Q : Vertex G → Prop) (S : Finset (Vertex G)) where
  added : Finset (Vertex G)
  output : Finset (Vertex G)
  added_Q : ∀ v ∈ added, Q v
  added_paired : ∀ v ∈ added, (v.1,-v.2) ∈ added
  added_nonzero : ∀ v ∈ added, v.2 ≠ 0
  original_added_disjoint : Disjoint S added
  output_subset : output ⊆ S ∪ added
  matching : MatchingOn ((S ∪ added) \ output)

/-- Before the first merge the original set is entirely open. -/
def PartialCover.initial (Q : Vertex G → Prop) (S : Finset (Vertex G)) :
    PartialCover Q S where
  added := ∅
  output := S
  added_Q := by simp
  added_paired := by simp
  added_nonzero := by simp
  original_added_disjoint := by simp
  output_subset := by simp
  matching := by simpa using (MatchingOn.empty (G := G))

/-- The new flow's matched vertices are disjoint from the old matching. -/
theorem old_new_matching_disjoint {Q : Vertex G → Prop} {S X T O : Finset (Vertex G)}
    (P : PartialCover Q S)
    (hX : Disjoint X (S ∪ P.added))
    (hT : Disjoint T ((S ∪ P.added) ∪ X)) :
    Disjoint ((S ∪ P.added) \ P.output) (((P.output ∪ X) ∪ T) \ O) := by
  apply Finset.disjoint_left.mpr
  intro v hvold hvnew
  have hold : v ∈ S ∪ P.added := (Finset.mem_sdiff.mp hvold).1
  have hnotopen : v ∉ P.output := (Finset.mem_sdiff.mp hvold).2
  have hnew : v ∈ (P.output ∪ X) ∪ T := (Finset.mem_sdiff.mp hvnew).1
  rcases Finset.mem_union.mp hnew with hOX | hTnew
  · rcases Finset.mem_union.mp hOX with hO | hXnew
    · exact hnotopen hO
    · exact Finset.disjoint_left.mp hX hXnew hold
  · exact Finset.disjoint_left.mp hT hTnew (Finset.mem_union_left _ hold)

/-- The exact cover ledger for one merge. The new open set belongs to the
fresh augmentation and consequently cannot hide an old matched vertex. -/
theorem merge_covered_eq {Q : Vertex G → Prop} {S X T O : Finset (Vertex G)}
    (P : PartialCover Q S) (hO : O ⊆ T)
    (hT : Disjoint T ((S ∪ P.added) ∪ X)) :
    ((S ∪ P.added) \ P.output) ∪ (((P.output ∪ X) ∪ T) \ O) =
      ((S ∪ X) ∪ (P.added ∪ T)) \ O := by
  ext v
  have ho : v ∈ P.output → v ∈ S ∪ P.added := fun hv ↦ P.output_subset hv
  have hn : v ∈ O → v ∈ T := fun hv ↦ hO hv
  have hdis : v ∈ T → v ∉ S ∪ P.added := by
    intro ht hmem
    exact Finset.disjoint_left.mp hT ht (Finset.mem_union_left _ hmem)
  simp only [Finset.mem_union, Finset.mem_sdiff] at *
  tauto

/-- Add one actual flow to an existing partial cover. Freshness hypotheses
are explicit; no claim is made that the required flow exists. -/
def PartialCover.extend {Q : Vertex G → Prop} {S X T O : Finset (Vertex G)}
    (P : PartialCover Q S)
    (hX : Disjoint X (S ∪ P.added))
    (hT : Disjoint T ((S ∪ P.added) ∪ X))
    (hO : O ⊆ T)
    (hTQ : ∀ v ∈ T, Q v)
    (hTpair : ∀ v ∈ T, (v.1,-v.2) ∈ T)
    (hTnonzero : ∀ v ∈ T, v.2 ≠ 0)
    (M : MatchingOn (((P.output ∪ X) ∪ T) \ O)) :
    PartialCover Q (S ∪ X) where
  added := P.added ∪ T
  output := O
  added_Q := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact P.added_Q v hv
    · exact hTQ v hv
  added_paired := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (P.added_paired v hv)
    · exact Finset.mem_union_right _ (hTpair v hv)
  added_nonzero := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact P.added_nonzero v hv
    · exact hTnonzero v hv
  original_added_disjoint := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvT
    rcases Finset.mem_union.mp hvS with hvS | hvX <;>
      rcases Finset.mem_union.mp hvT with hvOld | hvNew
    · exact Finset.disjoint_left.mp P.original_added_disjoint hvS hvOld
    · exact Finset.disjoint_left.mp hT hvNew
        (Finset.mem_union_left _ (Finset.mem_union_left _ hvS))
    · exact Finset.disjoint_left.mp hX hvX (Finset.mem_union_right _ hvOld)
    · exact Finset.disjoint_left.mp hT hvNew (Finset.mem_union_right _ hvX)
  output_subset := by
    intro v hv
    exact Finset.mem_union_right _ (Finset.mem_union_right _ (hO hv))
  matching := by
    have hdis := old_new_matching_disjoint (O := O) P hX hT
    have hjoin := P.matching.union M hdis
    rw [merge_covered_eq P hO hT] at hjoin
    exact hjoin

theorem PartialCover.extend_card_le {Q : Vertex G → Prop} {S X T O : Finset (Vertex G)}
    (P : PartialCover Q S) (hX : Disjoint X (S ∪ P.added))
    (hT : Disjoint T ((S ∪ P.added) ∪ X)) (hO : O ⊆ T)
    (hTQ : ∀ v ∈ T, Q v) (hTpair : ∀ v ∈ T, (v.1,-v.2) ∈ T)
    (hTnonzero : ∀ v ∈ T, v.2 ≠ 0)
    (M : MatchingOn (((P.output ∪ X) ∪ T) \ O)) :
    (P.extend hX hT hO hTQ hTpair hTnonzero M).added.card ≤ P.added.card + T.card :=
  Finset.card_union_le _ _

/-- Once the remaining output is itself an actual hyperedge, close the
partial cover into an exact matching of all original and added vertices. -/
def PartialCover.close {Q : Vertex G → Prop} {S : Finset (Vertex G)}
    (P : PartialCover Q S) (hEdge : IsHyperedge P.output) : MatchingOn (S ∪ P.added) := by
  have hm : MatchingOn P.output := {
    edges := {P.output}
    valid := by simpa using hEdge
    disjoint := by simp
    cover := by simp
  }
  have hd : Disjoint ((S ∪ P.added) \ P.output) P.output := Finset.sdiff_disjoint
  have h := P.matching.union hm hd
  simpa only [Finset.sdiff_union_of_subset P.output_subset] using h

end
end EndpointFlow.Cover
