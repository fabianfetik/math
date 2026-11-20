import CorralFormalization.EndpointProof.Matching.UniversalCore.CoreOriginalJoint

open MeasureTheory
open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFullProduct
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
open CorralFormalization.EndpointProof.Probability.ExponentialMargin
noncomputable section

/-- Both the proved core rate and the fractional-event rate have
strict room over the named ξ-based final rate. This is a deterministic
comparison, not a proof of the fractional event. -/
theorem final_rate_lt_core_and_fractional_rates
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    (xi q)^4 / 10^6 < (tau q)^24 / 64000 ∧
      (xi q)^4 / 10^6 < q^8 / (4 * 10^10) := by
  obtain ⟨_,_,_,_,_,_,hcat,_,_⟩ := samplingParameters_admissible q hq0 hq1
  have hτ : 0 < tau q := by unfold tau p rho eta; positivity
  have hp : 0 < p q := by unfold p rho eta; positivity
  have hcat' : 3 * p q + 3 * tau q ≤ 1 := by exact_mod_cast hcat
  have hp1 : p q ≤ 1 := by nlinarith
  have hτ1 : tau q ≤ 1 := by nlinarith
  have hpow : (p q)^4 ≤ p q := pow_le_of_le_one (le_of_lt hp) hp1 (by norm_num)
  have hτp : tau q ≤ p q := by unfold tau; nlinarith
  have hqpart : 0 ≤ q * (1/2-q) := mul_nonneg (le_of_lt hq0) (by linarith)
  have hpq : p q ≤ q / 10000 := by
    unfold p rho eta
    norm_num
    nlinarith
  have hτq : tau q ≤ q / 10000 := hτp.trans hpq
  have hr0 : 0 ≤ r0 q := by unfold r0 eta; positivity
  have hr1 : r0 q ≤ 1 := by unfold r0 eta; nlinarith
  have hξ0 : 0 ≤ xi q := by unfold xi kappa; positivity
  have ht9 : 0 ≤ (tau q)^9 := pow_nonneg (le_of_lt hτ) _
  have hξ9 : xi q ≤ (tau q)^9 := by
    have hc : (1 : ℝ) / 10^36 ≤ 1 := by norm_num
    have hf : (1 / (10 : ℝ)^36) * (tau q)^9 ≤ (tau q)^9 := by
      simpa using mul_le_mul_of_nonneg_right hc ht9
    have heq : xi q = (1 / (10 : ℝ)^36) * (tau q)^9 * r0 q := by
      unfold xi kappa
      ring
    rw [heq]
    simpa using mul_le_mul hf hr1 hr0 ht9
  have hξ4 : (xi q)^4 ≤ (tau q)^36 := by
    calc
      _ ≤ ((tau q)^9)^4 := pow_le_pow_left₀ hξ0 hξ9 4
      _ = _ := by rw [← pow_mul]
  have ht24 : (tau q)^36 ≤ (tau q)^24 :=
    pow_le_pow_of_le_one (le_of_lt hτ) hτ1 (by norm_num)
  have ht8 : (tau q)^36 ≤ (tau q)^8 :=
    pow_le_pow_of_le_one (le_of_lt hτ) hτ1 (by norm_num)
  have hq8 : (tau q)^8 ≤ q^8 / 10^32 := by
    calc
      _ ≤ (q / 10000)^8 := pow_le_pow_left₀ (le_of_lt hτ) hτq 8
      _ = _ := by ring
  have htpos : 0 < (tau q)^24 := pow_pos hτ _
  have hqpos : 0 < q^8 := pow_pos hq0 _
  constructor <;> nlinarith

/-- The written fractional-event tail and the proved core-event tail pay
one ξ-based error at a q-only threshold. Event existence is separate. -/
theorem core_and_fractional_bounds_pay_final (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ n ≥ N,
      Real.exp (-((tau q)^24 / 64000) * (n : ℝ)) +
        18 * (n : ℝ) * Real.exp (-(q^8 / (4*10^10)) * n) ≤
      Real.exp (-((xi q)^4 / 10^6) * n) := by
  obtain ⟨hc,hf⟩ := final_rate_lt_core_and_fractional_rates q hq0 hq1
  let C : Fin 2 → ℝ := ![1,18]
  let k : Fin 2 → ℕ := ![0,1]
  let a : Fin 2 → ℝ := ![(tau q)^24/64000,q^8/(4*10^10)]
  have hrate : ∀ i, (xi q)^4 / 10^6 < a i := by
    intro i
    fin_cases i
    · simpa [a] using hc
    · simpa [a] using hf
  obtain ⟨N,hN⟩ := finite_polynomial_tails_absorbed C a k ((xi q)^4/10^6) hrate
  refine ⟨N, ?_⟩
  intro n hn
  have hsum := hN n hn
  convert hsum using 1
  all_goals
    simp [C,k,a,Fin.sum_univ_succ]

/-- Combine the actual full-sample core and any separately established
original event with the fractional tail. The original sample admits
one good core augmentation and itself satisfies E, at the named ξ rate.
The theorem intentionally assumes E's tail, not E's desired conclusion. -/
theorem originalCore_and_fractional_event_final_rate
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [AddCommGroup G] [Fintype G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      ∀ E : OriginalSample G → Prop,
        (originalMeasure (G := G) q (le_of_lt hq0) hq1).real {s | ¬ E s} ≤
          18 * (Fintype.card G : ℝ) *
            Real.exp (-(q^8/(4*10^10)) * (Fintype.card G : ℝ)) →
        (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
          {s | ¬ OriginalCoreAndEvent q E s} ≤
          Real.exp (-((xi q)^4/10^6) * (Fintype.card G : ℝ)) := by
  have hτ : 0 < tau q := by unfold tau p rho eta; positivity
  obtain ⟨Ntail,hNtail⟩ := coreFailureBound_eventually_exponential q hq0 hq1
  obtain ⟨Nsum,hNsum⟩ := core_and_fractional_bounds_pay_final q hq0 hq1
  obtain ⟨Nlarge,hNlarge⟩ := exists_nat_gt (4000 / (tau q)^2)
  refine ⟨max 1152 (max (selectorSameSampleThreshold q) (max Ntail (max Nsum Nlarge))), ?_⟩
  intro G _ _ hodd hn E hE
  have hn1152 : 1152 ≤ Fintype.card G := by omega
  have hnsel : selectorSameSampleThreshold q ≤ Fintype.card G := by omega
  have hntail : Ntail ≤ Fintype.card G := by omega
  have hnsum : Nsum ≤ Fintype.card G := by omega
  have hnlarge : Nlarge ≤ Fintype.card G := by omega
  have hnt : (4000 : ℝ) ≤ (tau q)^2 * Fintype.card G := by
    have hnreal : (Nlarge : ℝ) ≤ Fintype.card G := by exact_mod_cast hnlarge
    have hnl := (div_lt_iff₀ (pow_pos hτ 2)).mp hNlarge
    nlinarith [mul_nonneg (sq_nonneg (tau q)) (sub_nonneg.mpr hnreal)]
  have hjoint := originalCore_and_event_failure_probability q hq0 hq1 hodd hn1152 hnt hnsel E _ hE
  have ht := hNtail (Fintype.card G) hntail
  have hs := hNsum (Fintype.card G) hnsum
  apply hjoint.trans
  linarith


end
end EndpointMatching.UniversalCore
