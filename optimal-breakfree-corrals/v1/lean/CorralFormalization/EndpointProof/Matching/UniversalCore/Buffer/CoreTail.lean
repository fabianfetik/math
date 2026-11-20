import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.CoreProbability

open MeasureTheory
open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport EndpointFullProduct EndpointOriginalReservoir
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
open CorralFormalization.EndpointProof.Probability.ExponentialMargin
noncomputable section

/-- Explicit union bound for the actual selector, pair-count, tetrahedron
and buffer events on the common augmentation. -/
def coreFailureBound (q : ℝ) (n : ℕ) : ℝ :=
  24 * (n : ℝ)^3 * Real.exp (-((p q)^8 / 32000) * (n : ℝ)) +
    (6 * Real.exp (-(p q)^2 * (n : ℝ)/36) +
      6 * Real.exp (-(tau q)^2 * (n : ℝ)/36)) +
    (n : ℝ)^6 * Real.exp (-(tau q)^24 * (n : ℝ) / 2304) +
      6 * (n : ℝ)^7 * Real.exp (-(tau q)^20 * (n : ℝ) / 100) +
    Real.exp (-(tau q)^6 * (n : ℝ) / 144) +
      3 * (n : ℝ) * Real.exp (-(tau q)^4 * (n : ℝ) / 4)

/-- All polynomial prefactors are eventually absorbed into one explicit
exponential rate. The threshold depends only on the input density. -/
theorem coreFailureBound_eventually_exponential
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) :
    ∃ N : ℕ, ∀ n ≥ N, coreFailureBound q n ≤
      Real.exp (-((tau q)^24 / 64000) * (n : ℝ)) := by
  obtain ⟨hη0,hη1,ha,hb,hab,hp,hcat,hP,hQ⟩ := samplingParameters_admissible q hq0 hq1
  have hτ : 0 < tau q := by unfold tau p SamplingConstants.rho eta; positivity
  have hp0 : 0 < p q := by unfold p SamplingConstants.rho eta; positivity
  have hcat' : 3 * (pNN q : ℝ) + 3 * (tauNN q : ℝ) ≤ 1 := by exact_mod_cast hcat
  have hτthird : tau q ≤ 1 / 3 := by
    change 3 * p q + 3 * tau q ≤ 1 at hcat'
    nlinarith
  have hτone : tau q ≤ 1 := by linarith
  have hpone : p q ≤ 1 := by
    change 3 * p q + 3 * tau q ≤ 1 at hcat'
    nlinarith
  have hτp : tau q ≤ p q := by
    have hpow : (p q)^4 ≤ p q := pow_le_of_le_one (le_of_lt hp0) hpone (by norm_num)
    unfold tau
    nlinarith
  have ht24 : 0 < (tau q)^24 := pow_pos hτ _
  have hτ2 : (tau q)^24 ≤ (tau q)^2 :=
    pow_le_pow_of_le_one (le_of_lt hτ) hτone (by norm_num)
  have hτ4 : (tau q)^24 ≤ (tau q)^4 :=
    pow_le_pow_of_le_one (le_of_lt hτ) hτone (by norm_num)
  have hτ6 : (tau q)^24 ≤ (tau q)^6 :=
    pow_le_pow_of_le_one (le_of_lt hτ) hτone (by norm_num)
  have hτ8 : (tau q)^24 ≤ (p q)^8 := by
    calc
      (tau q)^24 ≤ (tau q)^8 :=
        pow_le_pow_of_le_one (le_of_lt hτ) hτone (by norm_num)
      _ ≤ (p q)^8 := pow_le_pow_left₀ (le_of_lt hτ) hτp 8
  have hp2 : (tau q)^24 ≤ (p q)^2 := by
    calc
      (tau q)^24 ≤ (tau q)^2 := hτ2
      _ ≤ (p q)^2 := pow_le_pow_left₀ (le_of_lt hτ) hτp 2
  have hτ20 : (tau q)^24 ≤ (tau q)^20 :=
    pow_le_pow_of_le_one (le_of_lt hτ) hτone (by norm_num)
  let C : Fin 7 → ℝ := ![24,6,6,1,6,1,3]
  let k : Fin 7 → ℕ := ![3,0,0,6,7,0,1]
  let a : Fin 7 → ℝ := ![(p q)^8/32000,(p q)^2/36,(tau q)^2/36,
    (tau q)^24/2304,(tau q)^20/100,(tau q)^6/144,(tau q)^4/4]
  have hrates : ∀ i, (tau q)^24 / 64000 < a i := by
    intro i
    fin_cases i <;> simp [a] <;> nlinarith
  obtain ⟨Ntail,hNtail⟩ := finite_polynomial_tails_absorbed C a k ((tau q)^24/64000) hrates
  refine ⟨Ntail, ?_⟩
  intro n hn
  have hsum := hNtail n hn
  have hbound :
      24 * (n : ℝ)^3 * Real.exp (-((p q)^8 / 32000) * (n : ℝ)) +
      (6 * Real.exp (-(p q)^2 * (n : ℝ)/36) +
        6 * Real.exp (-(tau q)^2 * (n : ℝ)/36)) +
      (n : ℝ)^6 * Real.exp (-(tau q)^24 * (n : ℝ) / 2304) +
        6 * (n : ℝ)^7 * Real.exp (-(tau q)^20 * (n : ℝ) / 100) +
      Real.exp (-(tau q)^6 * (n : ℝ) / 144) +
        3 * (n : ℝ) * Real.exp (-(tau q)^4 * (n : ℝ) / 4) ≤
        Real.exp (-((tau q)^24 / 64000) * (n : ℝ)) := by
    convert hsum using 1
    all_goals
      simp [C, k, a, Fin.sum_univ_succ]
      ring_nf
  exact hbound

/-- The proved core event on the full, common augmentation itself, with no
projection and no independent-event assumption. -/
theorem fullCore_explicit_failure_probability
    {G : Type*} [AddCommGroup G] [Fintype G]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (hodd : Odd (Fintype.card G))
    (hn : 1152 ≤ Fintype.card G)
    (hnlarge : (4000 : ℝ) ≤ (tau q)^2 * Fintype.card G)
    (hsel : selectorSameSampleThreshold q ≤ Fintype.card G) :
    (parameterizedFullMeasure G q hq0 hq1).real
      {ω | ¬ UniversalCoreEvent (tau q) ω} ≤ coreFailureBound q (Fintype.card G) := by
  obtain ⟨hη0,hη1,ha,hb,hab,hp,hcat,hP,hQ⟩ := samplingParameters_admissible q hq0 hq1
  have hτ : 0 < (tauNN q : ℝ) := by
    change 0 < tau q
    unfold tau p SamplingConstants.rho eta
    positivity
  have hcat' : 3 * (pNN q : ℝ) + 3 * (tauNN q : ℝ) ≤ 1 := by exact_mod_cast hcat
  have hτmax : (tauNN q : ℝ) ≤ 1 / 3 := by nlinarith [NNReal.coe_nonneg (pNN q)]
  have hτp : (tauNN q : ℝ) ≤ (pNN q : ℝ)^4 / 10^30 := by
    change tau q ≤ (p q)^4 / 10^30
    unfold tau
    ring_nf
    exact le_rfl
  let μ := fullMeasure (G := G) q eta (1/4) (tau q / SamplingConstants.rho q)
      (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
  have hPtail := selector_same_sample_external_error_of_threshold q hq0 hq1 hodd hsel
  have hPtail' : μ.real
      {ω | ¬ ColouredSelectors ω (selectorExternalBudget (pNN q : ℝ) (Fintype.card G))} ≤
      24 * (Fintype.card G : ℝ)^3 * Real.exp (-((p q)^8 / 32000) * (Fintype.card G : ℝ)) := by
    have hpNN : (pNN q : ℝ) = p q := rfl
    rw [hpNN]
    simpa only [μ, parameterizedFullMeasure] using hPtail
  have hItail : μ.real {ω | ¬ InventoryBounds (tauNN q : ℝ) ω} ≤
      6 * Real.exp (-(pNN q : ℝ)^2 * (Fintype.card G : ℝ)/36) +
        6 * Real.exp (-(tauNN q : ℝ)^2 * (Fintype.card G : ℝ)/36) := by
    change μ.real {ω | ¬ QPairInventoryEvent (tauNN q : ℝ) ω} ≤ _
    exact qInventoryEvent_failure_probability hodd q eta (1/4) (tau q / SamplingConstants.rho q)
      (le_of_lt hq0) hq1 hη0 hη1 ha hb hab (pNN q) (tauNN q) hcat hP hQ (by omega)
  have hresult := universalCore_failure_probability_of_component_tails hodd q eta (1/4)
    (tau q / SamplingConstants.rho q)
    (le_of_lt hq0) hq1 hη0 hη1 ha hb hab (pNN q) (tauNN q) hcat hP hQ hτ hτmax hτp
    hn hnlarge _ _ hPtail' hItail
  have hpNN : (pNN q : ℝ) = p q := rfl
  have hτNN : (tauNN q : ℝ) = tau q := rfl
  rw [hpNN, hτNN] at hresult
  simpa only [parameterizedFullMeasure, coreFailureBound] using hresult

/-- For every fixed density, one order threshold works for all finite odd
abelian groups, both for the common augmented sample and its projection to
the original sample. -/
theorem full_and_originalCore_eventually_exponential
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) :
    ∃ N : ℕ, ∀ (G : Type*) [AddCommGroup G] [Fintype G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (parameterizedFullMeasure G q hq0 hq1).real
        {ω | ¬ UniversalCoreEvent (tau q) ω} ≤
        Real.exp (-((tau q)^24 / 64000) * (Fintype.card G : ℝ)) ∧
      (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
        {s | ¬ OriginalAdmitsUniversalCore (tau q) s} ≤
        Real.exp (-((tau q)^24 / 64000) * (Fintype.card G : ℝ)) := by
  have hτ : 0 < tau q := by unfold tau p SamplingConstants.rho eta; positivity
  obtain ⟨Ntail,hNtail⟩ := coreFailureBound_eventually_exponential q hq0 hq1
  obtain ⟨Nlarge,hNlarge⟩ := exists_nat_gt (4000 / (tau q)^2)
  refine ⟨max 1152 (max (selectorSameSampleThreshold q) (max Ntail Nlarge)), ?_⟩
  intro G _ _ hodd hn
  have hn1152 : 1152 ≤ Fintype.card G := by omega
  have hnsel : selectorSameSampleThreshold q ≤ Fintype.card G := by omega
  have hntail : Ntail ≤ Fintype.card G := by omega
  have hnlarge : Nlarge ≤ Fintype.card G := by omega
  have hnt : (4000 : ℝ) ≤ (tau q)^2 * Fintype.card G := by
    have hnreal : (Nlarge : ℝ) ≤ Fintype.card G := by exact_mod_cast hnlarge
    have hnl := (div_lt_iff₀ (pow_pos hτ 2)).mp hNlarge
    nlinarith [mul_nonneg (sq_nonneg (tau q)) (sub_nonneg.mpr hnreal)]
  have hexp := originalCore_explicit_failure_probability q hq0 hq1 hodd hn1152 hnt hnsel
  have hfull := fullCore_explicit_failure_probability q hq0 hq1 hodd hn1152 hnt hnsel
  have hbound := hNtail (Fintype.card G) hntail
  have horig : (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
      {s | ¬ OriginalAdmitsUniversalCore (tau q) s} ≤ coreFailureBound q (Fintype.card G) := by
    simpa only [coreFailureBound] using hexp
  exact ⟨hfull.trans hbound, horig.trans hbound⟩

end
end EndpointMatching.UniversalCore
