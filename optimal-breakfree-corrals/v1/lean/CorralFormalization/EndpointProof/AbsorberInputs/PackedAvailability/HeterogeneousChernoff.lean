import CorralFormalization.EndpointProof.Router.Bernoulli

/-!
A mean-scale lower tail for independent, non-identically distributed
Bernoulli variables. This extends the homogeneous `half_mean_lower_tail`
without adding a uniform-mean premise.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace AbsorberInputs.PackedAvailability

noncomputable section

/-- The lower half-mean Chernoff bound permits different individual means. -/
theorem heterogeneous_half_mean_lower_tail {Ω I : Type*}
    [Fintype Ω] [Fintype I] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (p : I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hbool : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = p i) (hindep : iIndepFun X μ) :
    μ.real {ω | (∑ i, X i ω) ≤ (∑ i, p i)/2} ≤
      Real.exp (-(∑ i, p i)/8) := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : Real.log 2 ≤ (3/4 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  have he : Real.exp (-Real.log 2) = (1/2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hmgf (i : I) : mgf (X i) μ (-Real.log 2) = 1-p i/2 := by
    have hpoint : (fun ω => Real.exp (-Real.log 2 * X i ω)) =
        (fun ω => 1-X i ω/2) := by
      funext ω
      rcases hbool i ω with h | h <;> norm_num [h, he]
    rw [mgf, hpoint, integral_sub Integrable.of_finite Integrable.of_finite,
      integral_div, hmean]
    simp
  have hsum : mgf (fun ω => ∑ i, X i ω) μ (-Real.log 2) ≤
      Real.exp (-(∑ i, p i)/2) := by
    have hfun : (∑ i, X i) = (fun ω => ∑ i, X i ω) := by ext ω; simp
    rw [← hfun, hindep.mgf_sum (fun i => measurable_of_countable (X i)) Finset.univ]
    simp_rw [hmgf]
    calc
      (∏ i : I, (1-p i/2)) ≤ ∏ i : I, Real.exp (-p i/2) := by
        apply Finset.prod_le_prod
        · intro i hi; linarith [hp1 i]
        · intro i hi
          have hh := Real.add_one_le_exp (-p i/2)
          linarith
      _ = Real.exp (-(∑ i, p i)/2) := by
        rw [← Real.exp_sum]
        simp only [← Finset.sum_div, ← Finset.sum_neg_distrib]
  have htail := measure_le_le_exp_mul_mgf
    (μ := μ) (X := fun ω => ∑ i, X i ω)
    (t := -Real.log 2) ((∑ i, p i)/2) (by linarith) Integrable.of_finite
  calc
    _ ≤ Real.exp (-(-Real.log 2) * ((∑ i, p i)/2)) *
        mgf (fun ω => ∑ i, X i ω) μ (-Real.log 2) := htail
    _ ≤ Real.exp (-(-Real.log 2) * ((∑ i, p i)/2)) *
        Real.exp (-(∑ i, p i)/2) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm : 0 ≤ ∑ i, p i := Finset.sum_nonneg fun i _ => hp0 i
      nlinarith [mul_le_mul_of_nonneg_right hlog hm]

/-- A common lower bound on the different means gives a count-scale bound.
No identical-distribution assumption is needed. -/
theorem lower_bound_half_mean_lower_tail {Ω I : Type*}
    [Fintype Ω] [Fintype I] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (p : I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hbool : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = p i) (hindep : iIndepFun X μ)
    (s : ℝ) (hs : ∀ i, s ≤ p i) :
    μ.real {ω | (∑ i, X i ω) ≤ (Fintype.card I : ℝ)*s/2} ≤
      Real.exp (-((Fintype.card I : ℝ)*s)/8) := by
  have hsum : (Fintype.card I : ℝ)*s ≤ ∑ i, p i := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hs i)
  have hsubset : {ω | (∑ i, X i ω) ≤ (Fintype.card I : ℝ)*s/2} ⊆
      {ω | (∑ i, X i ω) ≤ (∑ i, p i)/2} := by
    intro ω hω
    change (∑ i, X i ω) ≤ _ at hω ⊢
    linarith
  exact (measureReal_mono hsubset
    (measure_ne_top μ _)).trans
    ((heterogeneous_half_mean_lower_tail μ X p hp0 hp1 hbool hmean hindep).trans
      (Real.exp_le_exp.mpr (by linarith)))

end
end AbsorberInputs.PackedAvailability
