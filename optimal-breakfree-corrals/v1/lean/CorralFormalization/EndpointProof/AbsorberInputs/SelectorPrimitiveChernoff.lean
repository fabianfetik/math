import CorralFormalization.EndpointProof.AbsorberInputs.PackedAvailabilityChernoff

/-! The literal packed-availability four-orbit successful-count and failure constants for
the actual switch and one/two/three-target star candidates, including all
part rotations. No packing, candidate probability or good event is supplied
by the caller. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

namespace AbsorberInputs
open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open EndpointFullProduct EndpointSelector
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

/-- The actual primitive count events. All packings precede the sample. -/
def selectorPrimitiveCountEvents (p : ℝ) (hodd : Odd (Fintype.card G))
    (hn : 1000 ≤ Fintype.card G) : Fin 4 → FullSample G → Prop :=
  ![FourOrbitSuccessfulCounts p (Assembly.rotatedQueryEmbedding hodd hn)
      (fun r _ => Assembly.rotatedSwitchDemand r.1),
    FourOrbitSuccessfulCounts p (Stars.rotatedStarQueryEmbedding (k := 1) (by omega) hodd hn)
      (fun r _ => Stars.rotatedStarDemand (k := 1) r.1),
    FourOrbitSuccessfulCounts p (Stars.rotatedStarQueryEmbedding (k := 2) (by omega) hodd hn)
      (fun r _ => Stars.rotatedStarDemand (k := 2) r.1),
    FourOrbitSuccessfulCounts p (Stars.rotatedStarQueryEmbedding (k := 3) (by omega) hodd hn)
      (fun r _ => Stars.rotatedStarDemand (k := 3) r.1)]

theorem rotated_star_count_error {k : ℕ} (hk : k ≤ 3)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (hp : 0 < (p : ℝ)) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = EndpointOriginalReservoir.rho q η*a)
    (hQ : (τ : ℝ) = EndpointOriginalReservoir.rho q η*b) :
    (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω : FullSample G | ¬ FourOrbitSuccessfulCounts (p : ℝ)
        (Stars.rotatedStarQueryEmbedding hk hodd (by omega))
        (fun r _ => Stars.rotatedStarDemand r.1) ω} ≤
      6*(Fintype.card G : ℝ)^k *
        Real.exp (-((p : ℝ)^4*(Fintype.card G : ℝ))/16000) := by
  have hp1 : (p : ℝ) ≤ 1 := by
    have hr : 3*(p : ℝ)+3*(τ : ℝ) ≤ 1 := by exact_mod_cast h
    nlinarith [τ.coe_nonneg]
  have ht := full_four_orbit_successful_counts hodd hn q η a b hq0 hq1
    hη0 hη1 ha hb hab p τ hp h hP hQ
    (Stars.rotatedStarQueryEmbedding hk hodd (by omega))
    (fun r _ => Stars.rotatedStarDemand r.1) (by simp) (fun r =>
      ⟨(p : ℝ)^(k+1),
        by simpa only [Stars.rotatedStarDemand_probability] using
          Stars.rotatedStarDemand_probability_ge_four p τ h hk r.1,
        pow_le_one₀ p.coe_nonneg hp1,
        fun _ => Stars.rotatedStarDemand_probability p τ r.1⟩)
  have hc : (Fintype.card (Stars.RotatedStarQuery G k) : ℝ) ≤
      6*(Fintype.card G : ℝ)^k := by
    exact_mod_cast (Stars.rotatedStarQuery_card_le (G := G) (k := k))
  exact ht.trans (mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _))

/-- The paper's successful count and mean-scale tail, for each actual
primitive family and all legal root queries at once. -/
theorem selector_primitive_count_error
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G) (i : Fin 4) :
    (parameterizedFullMeasure G q hq0 hq1).real
      {ω | ¬ selectorPrimitiveCountEvents (p q) hodd (by omega) i ω} ≤
      6*(Fintype.card G : ℝ)^(![2,1,2,3] : Fin 4 → ℕ) i *
        Real.exp (-((p q)^4*(Fintype.card G : ℝ))/16000) := by
  obtain ⟨hη0,hη1,ha,hb,hab,hp,hcat,hP,hQ⟩ := samplingParameters_admissible q hq0 hq1
  have hp1 : (pNN q : ℝ) ≤ 1 := by
    have hr : 3*(pNN q : ℝ)+3*(tauNN q : ℝ) ≤ 1 := by exact_mod_cast hcat
    nlinarith [NNReal.coe_nonneg (tauNN q)]
  have hsw := full_four_orbit_successful_counts hodd hn q eta (1/4)
    (tau q/SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
    (pNN q) (tauNN q) hp hcat hP hQ
    (Assembly.rotatedQueryEmbedding hodd (by omega))
    (fun r _ => Assembly.rotatedSwitchDemand r.1) (by simp) (fun r =>
      ⟨(pNN q : ℝ)^4,le_rfl,pow_le_one₀ (NNReal.coe_nonneg _) hp1,
        fun _ => Assembly.rotatedSwitchDemand_probability r.1 _ _⟩)
  have hc : (Fintype.card (Equiv.Perm (Fin 3) × RootQuery G) : ℝ) ≤
      6*(Fintype.card G : ℝ)^2 := by
    have hc' : (Fintype.card (RootQuery G) : ℝ) ≤ (Fintype.card G : ℝ)^2 := by
      exact_mod_cast (rootQuery_card_le (G := G))
    norm_num only [Fintype.card_prod,Fintype.card_perm,Fintype.card_fin,
      Nat.factorial,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_one,Nat.cast_succ]
    exact mul_le_mul_of_nonneg_left hc' (by norm_num : (0:ℝ) ≤ 6)
  have hsw' := hsw.trans (mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _))
  have hs1 := rotated_star_count_error (k := 1) (by omega) hodd hn q eta (1/4)
    (tau q/SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
    (pNN q) (tauNN q) hp hcat hP hQ
  have hs2 := rotated_star_count_error (k := 2) (by omega) hodd hn q eta (1/4)
    (tau q/SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
    (pNN q) (tauNN q) hp hcat hP hQ
  have hs3 := rotated_star_count_error (k := 3) (by omega) hodd hn q eta (1/4)
    (tau q/SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
    (pNN q) (tauNN q) hp hcat hP hQ
  have hpNN : (pNN q : ℝ) = p q := rfl
  rw [hpNN] at hsw' hs1 hs2 hs3
  fin_cases i
  · simpa [selectorPrimitiveCountEvents,parameterizedFullMeasure] using hsw'
  · simpa [selectorPrimitiveCountEvents,parameterizedFullMeasure] using hs1
  · simpa [selectorPrimitiveCountEvents,parameterizedFullMeasure] using hs2
  · simpa [selectorPrimitiveCountEvents,parameterizedFullMeasure] using hs3

/-- One common event gives at least p^4 n/4000 successful actual
orbit-disjoint candidates in every switch/star query, including all rotations. -/
theorem selector_primitive_counts_common_error
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G) :
    (parameterizedFullMeasure G q hq0 hq1).real
      {ω | ¬ ∀ i, selectorPrimitiveCountEvents (p q) hodd (by omega) i ω} ≤
      6*((Fintype.card G : ℝ)^3+2*(Fintype.card G : ℝ)^2+Fintype.card G) *
        Real.exp (-((p q)^4*(Fintype.card G : ℝ))/16000) := by
  have : IsProbabilityMeasure (parameterizedFullMeasure G q hq0 hq1) := by
    dsimp [parameterizedFullMeasure]
    infer_instance
  have hsub : {ω : FullSample G | ¬ ∀ i,
      selectorPrimitiveCountEvents (p q) hodd (by omega) i ω} ⊆
      ⋃ i : Fin 4, {ω | ¬ selectorPrimitiveCountEvents (p q) hodd (by omega) i ω} := by
    intro ω hbad
    simpa only [Set.mem_iUnion,Set.mem_ofPred_eq,not_forall] using hbad
  apply (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_iUnion_fintype_le _).trans ?_)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    selector_primitive_count_error q hq0 hq1 hodd hn i)
  convert hsum using 1
  simp [Fin.sum_univ_four]
  ring

/-- The same actual count sample supplies all existing primitive avoidance
contracts, ready for the deterministic coloured-selector compiler. -/
theorem selectorPrimitiveCountEvents.available
    (q : ℝ) (hq0 : 0 < q) (hodd : Odd (Fintype.card G))
    (hn : 1000 ≤ Fintype.card G) (ω : FullSample G)
    (hcounts : ∀ i, selectorPrimitiveCountEvents (p q) hodd hn i ω) :
    ∀ i, selectorPrimitiveEvents hodd hn (selectorBudget (p q) (Fintype.card G)) i ω := by
  have hp : 0 < p q := by unfold p SamplingConstants.rho eta; positivity
  intro i
  fin_cases i
  · exact (Assembly.fullAvailable_rotated_iff hodd hn _ ω).mp
      (FourOrbitSuccessfulCounts.available hp (hcounts 0))
  · exact FourOrbitSuccessfulCounts.available hp (hcounts 1)
  · exact FourOrbitSuccessfulCounts.available hp (hcounts 2)
  · exact FourOrbitSuccessfulCounts.available hp (hcounts 3)

/-- The actual common count event compiles to the full native selector
output, preserving the same augmentation and the p^4 Chernoff rate. -/
theorem coloured_selectors_explicit_chernoff_error_ring
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (C : ℕ) (hmargin : C+3996 ≤ selectorBudget (p q) (Fintype.card G)) :
    (parameterizedFullMeasure G q hq0 hq1).real
      {ω | ¬ EndpointFlow.AbelianTransport.ColouredSelectors ω C} ≤
      6*((Fintype.card G : ℝ)^3+2*(Fintype.card G : ℝ)^2+Fintype.card G) *
        Real.exp (-((p q)^4*(Fintype.card G : ℝ))/16000) := by
  have : IsProbabilityMeasure (parameterizedFullMeasure G q hq0 hq1) := by
    dsimp [parameterizedFullMeasure]
    infer_instance
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (selector_primitive_counts_common_error q hq0 hq1 hodd hn)
  intro ω hbad hcounts
  exact hbad (EndpointFlow.AbelianTransport.colouredSelectors_of_ring_same_sample ω C
    (Assembly.coloured_selectors_of_primitives hodd (by omega)
      (selectorBudget (p q) (Fintype.card G)) C hmargin ω
      (selectorPrimitiveCountEvents.available q hq0 hodd (by omega) ω hcounts)))

end

noncomputable section

/-- No ring or packing premise is needed from the caller. The original
AddCommGroup and the full augmented sample remain unchanged. -/
theorem coloured_selectors_explicit_chernoff_error_abelian
    {G : Type*} [Fintype G] [A : AddCommGroup G]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (C : ℕ) (hmargin : C+3996 ≤ selectorBudget (p q) (Fintype.card G)) :
    (parameterizedFullMeasure G q hq0 hq1).real
      {ω | ¬ EndpointFlow.AbelianTransport.ColouredSelectors ω C} ≤
      6*((Fintype.card G : ℝ)^3+2*(Fintype.card G : ℝ)^2+Fintype.card G) *
        Real.exp (-((p q)^4*(Fintype.card G : ℝ))/16000) := by
  obtain ⟨ring,hcompat⟩ := EndpointFlow.AbelianTransport.exists_compatible_commRing G
  cases hcompat
  let : CommRing G := ring
  exact coloured_selectors_explicit_chernoff_error_ring q hq0 hq1 hodd hn C hmargin

/-- Literal external selector capacity and a q-only explicit threshold,
with the mean-scale rate stated after the packed availability lemma. -/
theorem selector_same_sample_external_explicit_chernoff_error
    {G : Type*} [Fintype G] [AddCommGroup G]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hodd : Odd (Fintype.card G))
    (hn : selectorSameSampleThreshold q ≤ Fintype.card G) :
    (parameterizedFullMeasure G q hq0 hq1).real
      {ω | ¬ EndpointFlow.AbelianTransport.ColouredSelectors ω
        (selectorExternalBudget (p q) (Fintype.card G))} ≤
      6*((Fintype.card G : ℝ)^3+2*(Fintype.card G : ℝ)^2+Fintype.card G) *
        Real.exp (-((p q)^4*(Fintype.card G : ℝ))/16000) := by
  obtain ⟨hn2000,hmargin⟩ := selectorSameSampleThreshold_pays_slack q hq0 _ hn
  exact coloured_selectors_explicit_chernoff_error_abelian q hq0 hq1 hodd hn2000 _ hmargin

end
end AbsorberInputs
