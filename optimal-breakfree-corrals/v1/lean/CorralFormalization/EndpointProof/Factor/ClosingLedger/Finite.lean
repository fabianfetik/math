import CorralFormalization.EndpointProof.Factor.InventoryBudget

/-! # Actual finite-set edit costs at the sole closing call

Every estimate below is proved from the finite sets themselves. In particular,
removing prescribed terminals is charged by their actual cardinalities.
-/
open scoped Classical symmDiff
namespace EndpointFactor.ClosingLedger
open EndpointMatching.AbsorptionAssembly
variable {G : Type*}

/-- A concrete symmetric difference splits into its two disjoint edits. -/
theorem symmDiff_card (A B : Finset G) :
    (A ∆ B).card = (A \ B).card + (B \ A).card := by
  rw [Finset.symmDiff_def,Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr (fun _ hA hB =>
    (Finset.mem_sdiff.mp hA).2 (Finset.mem_sdiff.mp hB).1)

/-- Triangle inequality proved at actual finite-set cardinalities. -/
theorem symmDiff_card_triangle (A B C : Finset G) :
    (A ∆ C).card ≤ (A ∆ B).card + (B ∆ C).card := by
  have hsub : A ∆ C ⊆ (A ∆ B) ∪ (B ∆ C) := by
    intro x hx
    simp only [Finset.mem_symmDiff,Finset.mem_union] at hx ⊢
    tauto
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Terminal removal costs at most its actual size, even without a subset
assumption. There is no assumed edit bound. -/
theorem symmDiff_sdiff_card_le (A removed : Finset G) :
    (A ∆ (A \ removed)).card ≤ removed.card := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_symmDiff,Finset.mem_sdiff] at hx
  tauto

/-- If all removed terminals occur, their cost is exactly their size. -/
theorem symmDiff_sdiff_card (A removed : Finset G) (hremoved : removed ⊆ A) :
    (A ∆ (A \ removed)).card = removed.card := by
  congr 1
  ext x
  have hh : x ∈ removed → x ∈ A := fun hx => hremoved hx
  simp only [Finset.mem_symmDiff,Finset.mem_sdiff]
  tauto

/-- Conversion from the actual physical metric to the three finite edits. -/
theorem physicalEditDistance_eq (rawLast rawFirst rawC last first C : Finset G) :
    physicalEditDistance rawLast rawFirst rawC last first C =
      (rawLast ∆ last).card + (rawFirst ∆ first).card + (rawC ∆ C).card := by
  simp only [physicalEditDistance,symmDiff_card]
  omega

/-- The exact finite ledger before inserting the paper's component bounds. -/
theorem closing_edit_triangle
    (rawLast rawFirst rawC specialLast specialFirst ends H₀ Hf X Y : Finset G) :
    physicalEditDistance rawLast rawFirst rawC (ends \ Y) (specialFirst \ X) Hf ≤
      (rawLast ∆ specialLast).card + (ends ∆ specialLast).card + Y.card +
      (rawFirst ∆ specialFirst).card + X.card + (rawC ∆ H₀).card + (Hf ∆ H₀).card := by
  have hlast₁ := symmDiff_card_triangle rawLast specialLast (ends \ Y)
  have hlast₂ := symmDiff_card_triangle specialLast ends (ends \ Y)
  have hlast₃ := symmDiff_sdiff_card_le ends Y
  have hfirst₁ := symmDiff_card_triangle rawFirst specialFirst (specialFirst \ X)
  have hfirst₂ := symmDiff_sdiff_card_le specialFirst X
  have hcolour := symmDiff_card_triangle rawC H₀ Hf
  rw [symmDiff_comm specialLast ends] at hlast₂
  rw [symmDiff_comm H₀ Hf] at hcolour
  rw [physicalEditDistance_eq]
  omega

end EndpointFactor.ClosingLedger
