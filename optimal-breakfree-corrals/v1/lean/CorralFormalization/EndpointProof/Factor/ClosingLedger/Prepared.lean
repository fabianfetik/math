import CorralFormalization.EndpointProof.Factor.ClosingLedger.ExactEditBound
import CorralFormalization.EndpointProof.Factor.Allocation.OrdinaryInput

/-! # uniform exact-matching theorem's edit premise from the actual prepared target and attached outcome

No special-layer, endpoint, or bank distance estimate is supplied to these
adapters. Those facts are extracted from the existing concrete constructors.
-/
open scoped Classical symmDiff
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointFactor.OrdinaryFragments
open EndpointMatching.AbsorptionAssembly
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
variable {dist : Densities m} {sample : AugmentedSample G m}
variable {W D X Y : Finset G} {ℓ w d : ℕ}

/-- The prepared physical classes and the actual attached ordinary paths pay
all seven concrete terms in the final edit triangle. -/
theorem PreparedTarget.closing_edit_bound
    (P : PreparedTarget dist sample W D X Y ℓ w d)
    (A : LayerData G (m+1) ℓ) (hLayer : A.layer = P.ordinaryLayer)
    (O : Outcome A P.ordinaryPool P.leftover P.bank Y)
    (hXYcard : X.card = Y.card) :
    (physicalEditDistance (vertexSet (forgetAugmented sample) (lastVertex m))
      (vertexSet (forgetAugmented sample) (firstVertex m))
      (colourSet (forgetAugmented sample) (specialColour m))
      (O.after.ends \ Y) (P.special 0 \ X)
      (remainingBank P.bank O.joins P.ordinaryPool A.colors) : ℝ) ≤
        (6+3*dist.q)*(d : ℝ)+3*explicitSizeTolerance (Fintype.card G)+
          11*X.card+4*A.deficit+3*w := by
  have hleft : P.leftover.card = w := P.leftover_card
  have hlast : ((vertexSet (forgetAugmented sample) (lastVertex m) ∆ P.special 2).card : ℝ) ≤
      (2+dist.q)*(d : ℝ)+explicitSizeTolerance (Fintype.card G)+4*X.card := by
    simpa [specialVertexRole,lastVertex] using (P.special_data 2).2.2
  have hfirst : ((vertexSet (forgetAugmented sample) (firstVertex m) ∆ P.special 0).card : ℝ) ≤
      (2+dist.q)*(d : ℝ)+explicitSizeTolerance (Fintype.card G)+4*X.card := by
    simpa [specialVertexRole,firstVertex] using (P.special_data 0).2.2
  have hends : (O.after.ends ∆ P.special 2).card = 2*(A.deficit+w) := by
    simpa [hLayer,ordinaryLayer,← Fin.succ_last,hleft] using O.end_discrepancy
  have hbank : ((remainingBank P.bank O.joins P.ordinaryPool A.colors) ∆ P.bank).card =
      2*A.deficit+w := by
    simpa [hleft] using O.remaining_discrepancy
  exact ClosingLedger.closing_edit_bound _ _ _ _ _ _ _ _ X Y dist.q d
    (explicitSizeTolerance (Fintype.card G)) X.card A.deficit w rfl hXYcard.symm
    hlast hfirst hends P.bank_edit hbank

/-- The exact closing target selected from the prepared sample lies in the
exact-matching edit radius, using only the already proved numerical target bounds. -/
theorem PreparedTarget.closing_edit_budget
    (P : PreparedTarget dist sample W D X Y ℓ w d)
    (A : LayerData G (m+1) ℓ) (hLayer : A.layer = P.ordinaryLayer)
    (O : Outcome A P.ordinaryPool P.leftover P.bank Y)
    (hXYcard : X.card = Y.card) (Δ ε : ℝ)
    (hq : dist.q ≤ 1/3) (hd : (d : ℝ) ≤ 2*ε*Fintype.card G)
    (hs : explicitSizeTolerance (Fintype.card G) ≤ ε*Fintype.card G)
    (hK : (X.card : ℝ) ≤ ε*Fintype.card G) (hw : (w : ℝ) ≤ ε*Fintype.card G)
    (hε : 0 < ε) (hεΔ : ε ≤ Δ/100000)
    (hh : (A.deficit : ℝ) ≤ Δ*Fintype.card G/10000) :
    (physicalEditDistance (vertexSet (forgetAugmented sample) (lastVertex m))
      (vertexSet (forgetAugmented sample) (firstVertex m))
      (colourSet (forgetAugmented sample) (specialColour m))
      (O.after.ends \ Y) (P.special 0 \ X)
      (remainingBank P.bank O.joins P.ordinaryPool A.colors) : ℝ) <
        Δ*Fintype.card G := by
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  exact (P.closing_edit_bound A hLayer O hXYcard).trans_lt
    (InventoryBudget.finalEdit_budget dist.q Δ ε (Fintype.card G) d
      (explicitSizeTolerance (Fintype.card G)) X.card A.deficit w hq
      (Nat.cast_nonneg _) hd hs hK hw hε hεΔ hN hh)

/-- The non-strict edit premise in the exact notation of `exactMatchingEvent_apply`.
All target sets are the actual constructed inventories. -/
theorem PreparedTarget.closing_edit_within_radius
    (P : PreparedTarget dist sample W D X Y ℓ w d)
    (A : LayerData G (m+1) ℓ) (hLayer : A.layer = P.ordinaryLayer)
    (O : Outcome A P.ordinaryPool P.leftover P.bank Y)
    (hXYcard : X.card = Y.card) (ε : ℝ)
    (hq : dist.q ≤ 1/3) (hd : (d : ℝ) ≤ 2*ε*Fintype.card G)
    (hs : explicitSizeTolerance (Fintype.card G) ≤ ε*Fintype.card G)
    (hK : (X.card : ℝ) ≤ ε*Fintype.card G) (hw : (w : ℝ) ≤ ε*Fintype.card G)
    (hε : 0 < ε) (hεΔ : ε ≤ explicitDelta dist.q/100000)
    (hh : (A.deficit : ℝ) ≤ explicitDelta dist.q*Fintype.card G/10000) :
    (physicalEditDistance (vertexSet (forgetAugmented sample) (lastVertex m))
      (vertexSet (forgetAugmented sample) (firstVertex m))
      (colourSet (forgetAugmented sample) (specialColour m))
      (O.after.ends \ Y) (P.special 0 \ X)
      (remainingBank P.bank O.joins P.ordinaryPool A.colors) : ℝ) ≤
        (1 / 10^6 : ℝ) * CorralFormalization.EndpointProof.RateBudget.SamplingConstants.kappa dist.q *
          Fintype.card G := by
  simpa only [explicitDelta] using
    (P.closing_edit_budget A hLayer O hXYcard (explicitDelta dist.q) ε
      hq hd hs hK hw hε hεΔ hh).le

end
end EndpointFactor.Allocation
