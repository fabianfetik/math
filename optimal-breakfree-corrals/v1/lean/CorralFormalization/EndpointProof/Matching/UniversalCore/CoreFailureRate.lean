import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.CoreTail

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
open CorralFormalization.EndpointProof.Probability.ExponentialMargin
noncomputable section

/-- The explicit core failure estimate pays the paper's stated exponential
rate, with a q-only threshold and without replacing the common sample. -/
theorem coreFailureBound_eventually_explicit_rate
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) :
    ∃ N : ℕ, ∀ n ≥ N, coreFailureBound q n ≤
      Real.exp (-((tau q)^24 / 16000) * (n : ℝ)) := by
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
  have hτ16 : (tau q)^16 ≤ tau q := by
    simpa only [pow_one] using pow_le_pow_of_le_one (le_of_lt hτ) hτone (by norm_num : 1 ≤ 16)
  have ht8pos : 0 < (tau q)^8 := pow_pos hτ _
  have hmult := mul_le_mul_of_nonneg_left hτ16 (le_of_lt ht8pos)
  have hthird : 3 * tau q ≤ 1 := by linarith
  have hthirdmul := mul_le_mul_of_nonneg_left hthird (le_of_lt ht8pos)
  have hpow24 : (tau q)^8 * (tau q)^16 = (tau q)^24 := by rw [← pow_add]
  have hτ8 : 3 * (tau q)^24 ≤ (p q)^8 := by
    have hτ8p : (tau q)^8 ≤ (p q)^8 := pow_le_pow_left₀ (le_of_lt hτ) hτp 8
    nlinarith
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
  have hrates : ∀ i, (tau q)^24 / 16000 < a i := by
    intro i
    fin_cases i <;> simp [a] <;> nlinarith
  obtain ⟨Ntail,hNtail⟩ := finite_polynomial_tails_absorbed C a k ((tau q)^24/16000) hrates
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
        Real.exp (-((tau q)^24 / 16000) * (n : ℝ)) := by
    convert hsum using 1
    all_goals
      simp [C, k, a, Fin.sum_univ_succ]
      ring_nf
  exact hbound


end
end EndpointMatching.UniversalCore
