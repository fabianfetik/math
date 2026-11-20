import CorralFormalization.EndpointProof.Selector.Stars.Availability

/-!
# Literal paper parameters for the actual rotated-star events

This supplies the B,C,...,C primitive independently of the B,B,C,C switch.
Its individual original-model projection has one augmentation for all star
queries; simultaneous projection with other primitives must happen before
forgetting the auxiliary labels.
-/

open scoped Classical NNReal

universe u

namespace EndpointSelector.Stars

open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G] {k : ℕ}

/-- No sampling admissibility premise remains beyond the literal density range. -/
theorem full_rotated_star_budget (hk : k ≤ 3)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G) :
    (EndpointFullProduct.fullMeasure q eta (1/4) (tau q/SamplingConstants.rho q)
      (le_of_lt hq0) hq1
      (samplingParameters_admissible q hq0 hq1).1
      (samplingParameters_admissible q hq0 hq1).2.1
      (samplingParameters_admissible q hq0 hq1).2.2.1
      (samplingParameters_admissible q hq0 hq1).2.2.2.1
      (samplingParameters_admissible q hq0 hq1).2.2.2.2.1).real
      {ω : EndpointFullProduct.FullSample G |
        ¬ EndpointFullProduct.FullAvailable (rotatedStarQueryEmbedding hk hodd (by omega))
          (fun r _ ↦ rotatedStarDemand r.1) (selectorBudget (p q) (Fintype.card G)) ω} ≤
      6*(Fintype.card G : ℝ)^k *
        Real.exp (-(p q^8/32000)*(Fintype.card G : ℝ)) := by
  obtain ⟨hη0,hη1,hα,hβ,hαβ,hp,hcat,hP,hQ⟩ := samplingParameters_admissible q hq0 hq1
  exact full_sample_rotated_star_budget hk hodd hn q eta (1/4) (tau q/SamplingConstants.rho q)
    (le_of_lt hq0) hq1 hη0 hη1 hα hβ hαβ (pNN q) (tauNN q) hp hcat hP hQ

theorem original_sample_rotated_star_budget (hk : k ≤ 3)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η α β : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α+β ≤ 1) (p τ : ℝ≥0) (hp : 0 < (p : ℝ)) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*α) (hQ : (τ : ℝ) = rho q η*β) :
    (EndpointFullProduct.originalMeasure q hq0 hq1).real
      {s : EndpointFullProduct.OriginalSample G |
        ¬ EndpointFullProduct.OriginalAdmitsAvailable
          (rotatedStarQueryEmbedding hk hodd (by omega))
          (fun r _ ↦ rotatedStarDemand r.1) (selectorBudget p (Fintype.card G)) s} ≤
      6*(Fintype.card G : ℝ)^k *
        Real.exp (-((p : ℝ)^8/32000)*(Fintype.card G : ℝ)) := by
  have hh := EndpointFullProduct.original_sample_four_orbit_budget hodd hn
    q η α β hq0 hq1 hη0 hη1 hα hβ hαβ p τ hp h hP hQ
    (rotatedStarQueryEmbedding hk hodd (by omega)) (fun r _ ↦ rotatedStarDemand r.1)
    (by simp) (fun r _ ↦ rotatedStarDemand_probability_ge_four p τ h hk r.1)
  have hc : (Fintype.card (RotatedStarQuery G k) : ℝ) ≤ 6*(Fintype.card G : ℝ)^k := by
    exact_mod_cast (rotatedStarQuery_card_le (G := G) (k := k))
  exact hh.trans (mul_le_mul_of_nonneg_right hc (le_of_lt (Real.exp_pos _)))

theorem original_rotated_star_budget (hk : k ≤ 3)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G) :
    (EndpointFullProduct.originalMeasure q (le_of_lt hq0) hq1).real
      {s : EndpointFullProduct.OriginalSample G |
        ¬ EndpointFullProduct.OriginalAdmitsAvailable
          (rotatedStarQueryEmbedding hk hodd (by omega))
          (fun r _ ↦ rotatedStarDemand r.1) (selectorBudget (p q) (Fintype.card G)) s} ≤
      6*(Fintype.card G : ℝ)^k *
        Real.exp (-(p q^8/32000)*(Fintype.card G : ℝ)) := by
  obtain ⟨hη0,hη1,hα,hβ,hαβ,hp,hcat,hP,hQ⟩ := samplingParameters_admissible q hq0 hq1
  exact original_sample_rotated_star_budget hk hodd hn q eta (1/4) (tau q/SamplingConstants.rho q)
    (le_of_lt hq0) hq1 hη0 hη1 hα hβ hαβ (pNN q) (tauNN q) hp hcat hP hQ

/-- One augmentation for all rotated-star queries of a fixed arity.  Other
primitive types need a joint full-sample event before this projection. -/
theorem one_augmentation_all_rotated_stars (hk : k ≤ 3)
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (s : EndpointFullProduct.OriginalSample G)
    (hgood : EndpointFullProduct.OriginalAdmitsAvailable
      (rotatedStarQueryEmbedding hk hodd hn) (fun r _ ↦ rotatedStarDemand r.1) budget s) :
    ∃ ω : EndpointFullProduct.FullSample G, EndpointFullProduct.originalProcess ω = s ∧
      ∀ (r : StarQuery G k) (σ : Equiv.Perm Part) (F : Finset G), F.card ≤ budget →
        ∃ u : G, StarValid r.val u ∧ Disjoint (starSupport r.val u) F ∧
          (∀ v ∈ starInterior r.val u, PVertex ω (σ v.1,v.2) ∧
            EndpointFullProduct.originalSigned (σ v.1) s v.2) ∧
          (starInterior r.val u).card ≤ 2+2*k ∧
          ∀ i, IsTwoEdgeMatchingOn (starState r.val u i)
            ((starCommonPair u ∪ starPair r.val u i) ∪ target (r.val i)) := by
  obtain ⟨ω,hω,havailable⟩ := hgood
  refine ⟨ω,hω,?_⟩
  intro r σ F hF
  obtain ⟨u,hv,hd,hP,hcard,hm⟩ :=
    successful_rotated_star_of_fullAvailable hk hodd hn budget ω havailable r σ F hF
  refine ⟨u,hv,hd,?_,hcard,hm⟩
  intro v hv
  exact ⟨(hP v hv).1,by rw [← hω]; exact (hP v hv).2⟩

/-- The threshold is chosen from q before the arity, ring and root queries.
This is the star primitive event, and is not by itself the complete selector. -/
theorem original_rotated_star_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (k : ℕ) (hk : k ≤ 3) (G : Type u) [CommRing G] [Fintype G]
      (hodd : Odd (Fintype.card G)) (hn : max N 2000 ≤ Fintype.card G),
      (EndpointFullProduct.originalMeasure q (le_of_lt hq0) hq1).real
        {s : EndpointFullProduct.OriginalSample G |
          ¬ EndpointFullProduct.OriginalAdmitsAvailable
            (rotatedStarQueryEmbedding hk hodd (by omega))
            (fun r _ ↦ rotatedStarDemand r.1) (selectorBudget (p q) (Fintype.card G)) s} ≤
        Real.exp (-(xi q^4/10^6)*(Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := sampling_rates_pay_polynomial_union q 6 3 hq0 hq1
  refine ⟨N,?_⟩
  intro k hk G _ _ hodd hn
  have hn2000 : 2000 ≤ Fintype.card G := (le_max_right N 2000).trans hn
  have hnN : N ≤ Fintype.card G := (le_max_left N 2000).trans hn
  have hpow : (Fintype.card G : ℝ)^k ≤ (Fintype.card G : ℝ)^3 := by
    apply pow_le_pow_right₀ _ hk
    exact_mod_cast (by omega : 1 ≤ Fintype.card G)
  have hbound := original_rotated_star_budget hk q hq0 hq1 hodd hn2000
  apply hbound.trans
  apply le_trans _ (hN (Fintype.card G) hnN).2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num))
    (le_of_lt (Real.exp_pos _))

end
end EndpointSelector.Stars
