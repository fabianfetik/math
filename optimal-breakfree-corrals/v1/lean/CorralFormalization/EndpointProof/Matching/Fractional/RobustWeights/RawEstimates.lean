import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Robust

/-!
# Paying the manuscript's unnormalized deterministic estimates

Here `X = q² n` and `d = q m`, so the size estimate supplies `X ≤ 2 d`.
The diagonal/edit row-sum bounds and raw row-sum bound are normalized by
the actual ideal inverse.  The small-square estimate is exposed separately;
it is the remaining spectral obligation.
-/

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace EndpointMatching.Fractional.RobustWeights

noncomputable section

variable {I E : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype E] [DecidableEq E]

theorem normalizeError_norm_le (d : ℝ) (hd : 0 < d)
    (T : Matrix (Fin 3 × I) (Fin 3 × I) ℝ) :
    ‖normalizeError d T‖ ≤ (d⁻¹ * (5 / 3)) * ‖T‖ := by
  unfold normalizeError
  calc
    ‖(d⁻¹ • inverseNumerator) * T‖ ≤ ‖d⁻¹ • inverseNumerator (I := I)‖ * ‖T‖ := norm_mul_le _ _
    _ ≤ (d⁻¹ * (5 / 3)) * ‖T‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left inverseNumerator_norm_le (by positivity)) (norm_nonneg _)

/-- Normalize the actual degree/edit/raw error bounds at the paper's constants.
No raw Fourier estimate is silently transferred to the edited target. -/
theorem normalized_error_bounds (d X : ℝ) (hd : 0 < d) (hX : X ≤ 2 * d)
    (D Ed N : Matrix (Fin 3 × I) (Fin 3 × I) ℝ)
    (hD : ‖D‖ ≤ 3 * X / 10000) (hEd : ‖Ed‖ ≤ X / 10000) (hN : ‖N‖ ≤ 5 * X) :
    ‖normalizeError d (D + Ed)‖ ≤ 1 / 750 ∧ ‖normalizeError d N‖ ≤ 50 / 3 := by
  have hDE : ‖D + Ed‖ ≤ d / 1250 := by linarith [norm_add_le D Ed]
  have hN' : ‖N‖ ≤ 10 * d := by linarith
  constructor
  · calc
      _ ≤ (d⁻¹ * (5 / 3)) * ‖D + Ed‖ := normalizeError_norm_le d hd _
      _ ≤ (d⁻¹ * (5 / 3)) * (d / 1250) := mul_le_mul_of_nonneg_left hDE (by positivity)
      _ = 1 / 750 := by field_simp; norm_num
  · calc
      _ ≤ (d⁻¹ * (5 / 3)) * ‖N‖ := normalizeError_norm_le d hd _
      _ ≤ (d⁻¹ * (5 / 3)) * (10 * d) := mul_le_mul_of_nonneg_left hN' (by positivity)
      _ = 50 / 3 := by field_simp; norm_num

/-- The strongest raw-scale deterministic theorem in this module chain.
For `X=q²n`, the ban condition is exactly `Δ₃(F) ≤ βn`; no restriction to
the empty ban is made.  The sole spectral input is the displayed small-square
estimate on the normalized raw matrix. -/
theorem exists_robust_weights_of_unscaled_errors (edge : E → Fin 3 → I)
    (d X : ℝ) (hd : 0 < d) (hX : X ≤ 2 * d)
    (D Ed N : Matrix (Fin 3 × I) (Fin 3 × I) ℝ)
    (hdecomp : gram edge = idealGram d + (D + Ed) + N)
    (hD : ‖D‖ ≤ 3 * X / 10000) (hEd : ‖Ed‖ ≤ X / 10000) (hN : ‖N‖ ≤ 5 * X)
    (hN2 : ‖normalizeError d N * normalizeError d N‖ ≤ 33 / 100000)
    (hdegree : ∀ v, |(familyDegree edge Finset.univ v : ℝ) - d| ≤ 3 * X / 10000) :
    ∀ F : Finset E, (∀ v, (familyDegree edge F v : ℝ) ≤ X / 2000) →
      ∃ w : ↥((Finset.univ : Finset E) \ F) → ℝ,
        (∀ e, 1 / (2 * d) ≤ w e ∧ w e ≤ 3 / (2 * d)) ∧
        ∀ v, (∑ e, if v ∈ edgeSet (fun e : ↥((Finset.univ : Finset E) \ F) => edge e) e
          then w e else 0) = 1 := by
  have hb := normalized_error_bounds d X hd hX D Ed N hD hEd hN
  have hdegree' : ∀ v, |(familyDegree edge Finset.univ v : ℝ) - d| ≤ 3 * d / 5000 := by
    intro v
    linarith [hdegree v]
  intro F hF
  apply exists_robust_weights_of_error_split edge d hd D Ed N hdecomp hb.1 hb.2 hN2 hdegree' F
  intro v
  linarith [hF v]

end
end EndpointMatching.Fractional.RobustWeights
