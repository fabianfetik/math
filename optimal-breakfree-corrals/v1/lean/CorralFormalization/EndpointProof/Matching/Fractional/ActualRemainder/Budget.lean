import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Geometry
import CorralFormalization.EndpointProof.Matching.CoreCapacityReceiver

/-!
# Actual-target edit accounting

All deletions are charged in the same tagged symmetric-difference metric.
For signed physical inventories this is exactly the paper's total physical
edit distance.  The zero charge is zero when the remaining inventory is
already nonzero, and at most three otherwise.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.ActualRemainder

open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly

noncomputable section

variable {G : Type*} [AddCommGroup G]

def taggedDistance (R T : Finset (Vertex G)) : ℕ := (R \ T).card + (T \ R).card

theorem taggedDistance_signedTarget (RX RY RC X Y C : Finset G) :
    taggedDistance (signedTarget RX RY RC) (signedTarget X Y C) =
      physicalEditDistance RX RY RC X Y C := by
  simp only [taggedDistance, signedTarget_sdiff, signedTarget_card, physicalEditDistance]
  omega

omit [AddCommGroup G] in
/-- Restricting to one role cannot increase the edit cost of its size. -/
theorem taggedDistance_slice_size_bound (R T : Finset (Vertex G)) (p : Fin 3) :
    |((slice T p).card : ℝ) - ((slice R p).card : ℝ)| ≤ (taggedDistance R T : ℝ) := by
  have hupper (S U : Finset (Vertex G)) :
      (slice S p).card ≤ (slice U p).card + (S \ U).card := by
    have hsub : slice S p ⊆ slice U p ∪ (S \ U) := by
      intro v hv
      have hvS := (Finset.mem_filter.mp hv).1
      have hvp := (Finset.mem_filter.mp hv).2
      by_cases hvU : v ∈ U
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvU, hvp⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvS, hvU⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hTU : ((slice T p).card : ℝ) ≤ ((slice R p).card : ℝ) + ((T \ R).card : ℝ) :=
    by exact_mod_cast hupper T R
  have hRT : ((slice R p).card : ℝ) ≤ ((slice T p).card : ℝ) + ((R \ T).card : ℝ) :=
    by exact_mod_cast hupper R T
  simp only [taggedDistance, Nat.cast_add]
  apply abs_le.mpr
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (R \ T).card,
    Nat.cast_nonneg (α := ℝ) (T \ R).card]

omit [AddCommGroup G] in
/-- Deleting actual vertices costs at most their actual cardinality. -/
theorem taggedDistance_sdiff_le (R T D : Finset (Vertex G)) :
    taggedDistance R (T \ D) ≤ taggedDistance R T + D.card := by
  have hmissing : R \ (T \ D) ⊆ (R \ T) ∪ D := by
    intro v hv
    have hvR := (Finset.mem_sdiff.mp hv).1
    by_cases hvT : v ∈ T
    · have hvD : v ∈ D := by
        by_contra hvD
        exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mpr ⟨hvT, hvD⟩)
      exact Finset.mem_union_right _ hvD
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvR, hvT⟩)
  have hextra : (T \ D) \ R ⊆ T \ R := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).1,
      (Finset.mem_sdiff.mp hv).2⟩
  have hm := (Finset.card_le_card hmissing).trans (Finset.card_union_le _ _)
  have he := Finset.card_le_card hextra
  unfold taggedDistance
  omega

/-- Exact zero charge chosen from the actual remaining inventory. -/
def zeroCharge (W : Finset (Vertex G)) : ℕ := if ∀ v ∈ W, v.2 ≠ 0 then 0 else 3

theorem zeroCharge_le_three (W : Finset (Vertex G)) : zeroCharge W ≤ 3 := by
  unfold zeroCharge
  split <;> omega

theorem ZeroStep.card_le_charge {W : Finset (Vertex G)}
    {F : Finset (Finset (Vertex G))} (Z : ZeroStep W F) :
    Z.covered.card ≤ zeroCharge W := by
  unfold zeroCharge
  split
  · rename_i hnz
    rw [Z.empty_if_nonzero hnz]
    simp
  · exact Z.card_le_three

/-- The complete manuscript deletion bill, with the optional last `+3`
replaced by its exact zero-or-three charge. -/
theorem preprocessed_distance_le {R T A P : Finset (Vertex G)} (M : Matching P)
    {F : Finset (Finset (Vertex G))} (Z : ZeroStep (residual T A P) F) :
    taggedDistance R ((residual T A P) \ Z.covered) ≤
      taggedDistance R T + A.card + 3 * M.edges.card + zeroCharge (residual T A P) := by
  have hfirst := taggedDistance_sdiff_le R T (A ∪ P)
  have hsecond := taggedDistance_sdiff_le R (residual T A P) Z.covered
  have hcard := Finset.card_union_le A P
  have hP := matching_card M
  have hZ := Z.card_le_charge
  change taggedDistance R (T \ (A ∪ P)) ≤ taggedDistance R T + (A ∪ P).card at hfirst
  change taggedDistance R ((residual T A P) \ Z.covered) ≤
    taggedDistance R (T \ (A ∪ P)) + Z.covered.card at hsecond
  omega

theorem preprocessed_distance_le_add_three {R T A P : Finset (Vertex G)} (M : Matching P)
    {F : Finset (Finset (Vertex G))} (Z : ZeroStep (residual T A P) F) :
    taggedDistance R ((residual T A P) \ Z.covered) ≤
      taggedDistance R T + A.card + 3 * M.edges.card + 3 := by
  have := preprocessed_distance_le (R := R) M Z
  have := zeroCharge_le_three (residual T A P)
  omega

end
end EndpointMatching.Fractional.ActualRemainder
