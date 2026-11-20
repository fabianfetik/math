import CorralFormalization.EndpointProof.Factor.Allocation.PhysicalRouter
import CorralFormalization.EndpointProof.Factor.Allocation.RawRoles

/-!
# Actual generic vertex layers after special layers and router

All available raw generic pieces are protected simultaneously. The size
and raw-loss premises are derived from the same categorical sample and the
actual router/special-layer inventories, not from an abstract layer supplier.
-/

open scoped BigOperators Classical
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointRouter
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}

/-- Once the special layers and router use their actual exact inventories,
the remaining target has exactly `m*ℓ + w` elements. -/
theorem generic_vertex_room (sample : AugmentedSample G m) (special : Fin 3 → Finset G)
    (W D : Finset G) (ℓ w : ℕ) (router : PhysicalRouter sample special W D ℓ)
    (hsize : ∀ i, (special i).card = ℓ)
    (hpair : ∀ i j, i ≠ j → Disjoint (special i) (special j))
    (hsubset : ∀ i, special i ⊆ W)
    (hW : W.card = (m+12)*ℓ+w) :
    (W \ (Finset.univ.biUnion special ∪ fixedInteriorFinset router.first router.second)).card =
      m*ℓ+w := by
  let specials := Finset.univ.biUnion special
  let interior := fixedInteriorFinset router.first router.second
  have hpair' : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint special := by
    intro i _ j _ hij
    exact hpair i j hij
  have hs : specials.card = 3*ℓ := by
    dsimp [specials]
    rw [Finset.card_biUnion hpair']
    simp [hsize]
  have hsw : specials ⊆ W := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact hsubset i hi
  have hblockedW : specials ∪ interior ⊆ W :=
    Finset.union_subset hsw router.interior_in_target
  have hblocked : (specials ∪ interior).card = 12*ℓ := by
    rw [Finset.card_union_of_disjoint router.interior_avoids_special.symm, hs, router.interior_card]
    omega
  have hsplit := Finset.card_sdiff_add_card_eq_card hblockedW
  have hexpand : (m+12)*ℓ = m*ℓ+12*ℓ := by ring
  rw [hexpand] at hW
  change (W \ (specials ∪ interior)).card = m*ℓ+w
  omega

/-- The concentration event bounds each actual generic raw vertex role. -/
theorem generic_vertex_raw_fits (dist : Densities m) (sample : Sample G m)
    (tolerance : ℝ) (ℓ : ℕ) (hsize : SizeEvent dist tolerance sample)
    (hfit : dist.a * Fintype.card G + tolerance ≤ (ℓ : ℝ)) :
    ∀ i : Fin m, (vertexSet sample (Sum.inr i)).card ≤ ℓ := by
  intro i
  have hi := hsize.1 (Sum.inr i)
  have hi' : |((vertexSet sample (Sum.inr i)).card : ℝ) -
      dist.a * Fintype.card G| ≤ tolerance := by
    simpa [vertexWeight, mul_comm] using hi
  have hreal : ((vertexSet sample (Sum.inr i)).card : ℝ) ≤ ℓ := by
    have h := (abs_le.mp hi').2
    linarith
  exact_mod_cast hreal

/-- Actual generic layers after special-layer and router placement. The
raw loss `d+2K` is paid by missing target points and the forced terminals. -/
theorem exists_explicit_generic_vertex_layers
    (dist : Densities m) (sample : AugmentedSample G m) (W D X Y : Finset G)
    (special : Fin 3 → Finset G) (ℓ w d : ℕ)
    (router : PhysicalRouter sample special W D ℓ)
    (hgood : GoodSample dist (explicitSizeTolerance (Fintype.card G)) (forgetAugmented sample))
    (hsize : ∀ i, (special i).card = ℓ)
    (hpair : ∀ i j, i ≠ j → Disjoint (special i) (special j))
    (hsubset : ∀ i, special i ⊆ W)
    (hcarrier : ∀ i, special i ⊆ forcedCarrier
      (fun j => vertexSet (forgetAugmented sample) (specialVertexRole j)) (specialForced X Y)
        W (vertexSet (forgetAugmented sample) (reserveVertex m)))
    (hXYcard : X.card = Y.card)
    (hW : W.card = (m+12)*ℓ+w)
    (hmiss : ((Finset.univ : Finset G) \ W).card ≤ d)
    (hfit : dist.a * Fintype.card G + explicitSizeTolerance (Fintype.card G) ≤ (ℓ : ℝ)) :
    ∃ chosen : Fin m → Finset G,
      (∀ i, chosen i ⊆ W \ (Finset.univ.biUnion special ∪
          fixedInteriorFinset router.first router.second) ∧
        (chosen i).card = ℓ ∧
        (vertexSet (forgetAugmented sample) (Sum.inr i) \ chosen i).card ≤ d+2*X.card) ∧
      (∀ i j, i ≠ j → Disjoint (chosen i) (chosen j)) ∧
      ((W \ (Finset.univ.biUnion special ∪ fixedInteriorFinset router.first router.second)) \
        Finset.univ.biUnion chosen).card = w := by
  let blocked := Finset.univ.biUnion special ∪ fixedInteriorFinset router.first router.second
  let cap : Fin m → ℕ := fun _ => ℓ
  have hroomExact := generic_vertex_room sample special W D ℓ w router hsize hpair hsubset hW
  have hroom : (∑ i, cap i) ≤ (W \ blocked).card := by
    simp only [cap, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    dsimp [blocked]
    rw [hroomExact]
    omega
  have hrawcap := generic_vertex_raw_fits dist (forgetAugmented sample)
    (explicitSizeTolerance (Fintype.card G)) ℓ hgood.2.2 hfit
  have hroles : Function.Injective (fun i : Fin m => (Sum.inr i : VertexRole m)) := by
    intro i j hij
    exact Sum.inr.inj hij
  obtain ⟨chosen, hchosen, hpairchosen, hleft⟩ :=
    exists_raw_vertex_layers (forgetAugmented sample) m W blocked
      (fun i => Sum.inr i) cap hroles hrawcap hroom
  refine ⟨chosen, ?_, hpairchosen, ?_⟩
  · intro i
    have hblock := generic_blocked_card (forgetAugmented sample) W X Y
      (fixedInteriorFinset router.first router.second) special i hcarrier router.interior_in_reserve hXYcard
    have hmissraw : (vertexSet (forgetAugmented sample) (Sum.inr i) \ W).card ≤ d := by
      have hsub : vertexSet (forgetAugmented sample) (Sum.inr i) \ W ⊆
          (Finset.univ : Finset G) \ W := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
      exact (Finset.card_le_card hsub).trans hmiss
    have hloss := (hchosen i).2.2.2
    refine ⟨(hchosen i).2.1, (hchosen i).2.2.1, ?_⟩
    dsimp [blocked] at hloss
    omega
  · dsimp [cap, blocked] at hleft
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_id] at hleft
    rw [hroomExact] at hleft
    omega

end
end EndpointFactor.Allocation
