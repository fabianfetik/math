import CorralFormalization.EndpointProof.Factor.Allocation.OrdinaryInput
import CorralFormalization.EndpointProof.Factor.Allocation.LayerBudgetBounds

/-!
# Connect the actual prepared target to the ordinary fragment outcome

The donor budget is paid using the genuine special-layer, bank and leftover
inventories and the bound on the actual ordinary matching deficit.
-/

open scoped BigOperators Classical symmDiff
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointFactor.OrdinaryFragments
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
variable {dist : Densities m} {sample : AugmentedSample G m}
variable {W D X Y : Finset G} {ℓ w d : ℕ}

theorem PreparedTarget.exists_fragmentOutcome
    (P : PreparedTarget dist sample W D X Y ℓ w d)
    (A : LayerData G (m+1) ℓ)
    (hAlayer : A.layer = P.ordinaryLayer)
    (hAcolors : ∀ i, A.color i ⊆ P.ordinaryColour i)
    (hpair : PairSupplyEvent dist (forgetAugmented sample))
    (hXYcard : X.card = Y.card) (hKcap : X.card ≤ ℓ) (hDzero : (0 : G) ∉ D)
    (ε Δ : ℝ) (hq : 0 < dist.q) (hq3 : dist.q ≤ 1/3) (hε : 0 < ε)
    (hΔq : Δ ≤ dist.q^2) (hεΔ : ε ≤ Δ/100000)
    (hd : (d : ℝ) ≤ 2*ε*Fintype.card G)
    (hs : explicitSizeTolerance (Fintype.card G) ≤ ε*Fintype.card G)
    (hK : (X.card : ℝ) ≤ ε*Fintype.card G)
    (hw : (w : ℝ) ≤ ε*Fintype.card G)
    (hAdef : (A.deficit : ℝ) ≤ Δ*Fintype.card G/10000) :
    Nonempty (Outcome A P.ordinaryPool P.leftover P.bank Y) := by
  have hL := P.leftover_disjoint_vertices A hAlayer
  have hUP := P.matching_colors_subset_ordinaryPool A hAcolors
  have hPcard := P.ordinaryPool_card
  have hPzero : (0 : G) ∉ P.ordinaryPool := fun hx => hDzero (P.ordinaryPool_subset hx)
  have hHP := P.bank_disjoint_ordinaryPool
  have hleftN : P.leftover.card = w := by simpa [PreparedTarget.leftover] using P.leftover_card
  have hHcard : P.bank.card + Y.card = ℓ + P.leftover.card := by
    have h := P.bank_card hKcap
    rw [hleftN, ← hXYcard]
    exact h
  have hHzero := P.bank_nonzero hDzero
  have hYlast : Y ⊆ A.layer (Fin.last (m+1)) := by
    rw [hAlayer, P.ordinaryLayer_last]
    exact P.ends_in_special
  have hlast : (((vertexSet (forgetAugmented sample) (lastVertex m) \
      A.layer (Fin.last (m+1))).card : ℝ)) ≤
      (2+dist.q)*(d : ℝ)+explicitSizeTolerance (Fintype.card G)+4*X.card := by
    have h := P.special_raw_loss 2
    simpa [hAlayer, P.ordinaryLayer_last, specialVertexRole, lastVertex] using h
  have hbank := P.bank_loss
  change ((colourSet (forgetAugmented sample) (specialColour m) \ P.bank).card : ℝ) ≤
    d+explicitSizeTolerance (Fintype.card G)+X.card at hbank
  have hYcard : (Y.card : ℝ) = X.card := by exact_mod_cast hXYcard.symm
  have hleftcard : (P.leftover.card : ℝ) = w := by exact_mod_cast hleftN
  have hn : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos (α := G)
  have hnumeric := donor_budget_numeric dist.q ε Δ (Fintype.card G) d
    (explicitSizeTolerance (Fintype.card G)) X.card A.deficit w
    hq hq3 hε hn (Nat.cast_nonneg _) hΔq hεΔ hd hs hK hw hAdef
  have hbudget : (((vertexSet (forgetAugmented sample) (lastVertex m) \
      A.layer (Fin.last (m+1))).card + Y.card +
      (colourSet (forgetAugmented sample) (specialColour m) \ P.bank).card +
      3*A.deficit+2*P.leftover.card : ℕ) : ℝ) <
        dist.q^2*(Fintype.card G : ℝ)/2 := by
    push_cast
    change (((vertexSet (forgetAugmented sample) (lastVertex m) \
      A.layer (Fin.last (m+1))).card : ℝ)) + (Y.card : ℝ) +
      ((colourSet (forgetAugmented sample) (specialColour m) \ P.bank).card : ℝ) +
      3*(A.deficit : ℝ)+2*(P.leftover.card : ℝ) < _
    nlinarith only [hlast, hbank, hYcard, hleftcard, hnumeric]
  exact exists_outcome hpair A P.ordinaryPool P.leftover P.bank Y hL hUP hPcard hPzero
    hHP hHcard hHzero hYlast hbudget

end
end EndpointFactor.Allocation
