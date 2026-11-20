import CorralFormalization.EndpointProof.Factor.Allocation.ForcedSpecialLayers
import CorralFormalization.EndpointProof.Router.GlobalGeometry.RouteCompletion

/-! # The actual paper forbidden set and router ledger -/

open scoped BigOperators Classical
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointRouter
noncomputable section
variable {G : Type*} [Fintype G] [DecidableEq G]

/-- Special classes and the raw reserve points/colours outside the requested
target. The two roles are numerical coordinates, as in the written proof. -/
def explicitRouterForbidden (special : Fin 3 → Finset G)
    (RV RC W D : Finset G) : Finset G :=
  Finset.univ.biUnion special ∪ (RV \ W) ∪ (RC \ D)

theorem explicitRouterForbidden_card
    (special : Fin 3 → Finset G) (RV RC W D : Finset G) (ℓ d K : ℕ)
    (hpair : ∀ i j, i ≠ j → Disjoint (special i) (special j))
    (hsize : ∀ i, (special i).card = ℓ)
    (hD : D.card + K = W.card)
    (hmiss : ((Finset.univ : Finset G) \ W).card ≤ d) :
    (explicitRouterForbidden special RV RC W D).card ≤ 3*ℓ + 2*d + K := by
  have hpair' : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint special := by
    intro i _ j _ hij
    exact hpair i j hij
  have hspecial : (Finset.univ.biUnion special).card = 3*ℓ := by
    rw [Finset.card_biUnion hpair']
    simp [hsize]
  have hRV : (RV \ W).card ≤ ((Finset.univ : Finset G) \ W).card := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  have hRC : (RC \ D).card ≤ ((Finset.univ : Finset G) \ D).card := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  have hW := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ W)
  have hD' := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  have hunion1 := Finset.card_union_le (Finset.univ.biUnion special) (RV \ W)
  have hunion2 := Finset.card_union_le (Finset.univ.biUnion special ∪ (RV \ W)) (RC \ D)
  change (Finset.univ.biUnion special ∪ (RV \ W) ∪ (RC \ D)).card ≤ _
  omega

/-- The displayed paper slack pays the actual finite forbidden set and all
`22ℓ` router requests. -/
theorem explicitRouterForbidden_ledger
    (special : Fin 3 → Finset G) (RV RC W D : Finset G) (ℓ d K : ℕ)
    (q ε b : ℝ)
    (hpair : ∀ i j, i ≠ j → Disjoint (special i) (special j))
    (hsize : ∀ i, (special i).card = ℓ)
    (hD : D.card + K = W.card)
    (hmiss : ((Finset.univ : Finset G) \ W).card ≤ d)
    (hℓ : (ℓ : ℝ) ≤ q * Fintype.card G)
    (hd : (d : ℝ) ≤ 2*ε * Fintype.card G)
    (hK : (K : ℝ) ≤ ε * Fintype.card G)
    (hslack : 25*q + 5*ε < b/4)
    (hn : 0 < Fintype.card G) :
    (((explicitRouterForbidden special RV RC W D).card + 22*ℓ : ℕ) : ℝ) ≤
      b * Fintype.card G / 4 := by
  have hf := explicitRouterForbidden_card special RV RC W D ℓ d K hpair hsize hD hmiss
  have hf' : ((explicitRouterForbidden special RV RC W D).card : ℝ) ≤ 3*ℓ + 2*d + K := by
    exact_mod_cast hf
  have hn' : 0 < (Fintype.card G : ℝ) := by exact_mod_cast hn
  have hscaled := mul_lt_mul_of_pos_right hslack hn'
  push_cast
  nlinarith

/-- Exact conversion from the finite division ledger to `ℓ = qn - qd`. -/
theorem layer_capacity_eq (n k ℓ d : ℕ) (q : ℝ)
    (hdiv : k*ℓ + d = n) (hqk : q*(k : ℝ) = 1) :
    (ℓ : ℝ) = q*n - q*d := by
  have hdiv' : (k : ℝ)*(ℓ : ℝ) + d = n := by exact_mod_cast hdiv
  have hm := congrArg (fun x : ℝ => x*(ℓ : ℝ)) hqk
  have hmul := congrArg (fun x : ℝ => q*x) hdiv'
  nlinarith [hm, hmul]

end
end EndpointFactor.Allocation
