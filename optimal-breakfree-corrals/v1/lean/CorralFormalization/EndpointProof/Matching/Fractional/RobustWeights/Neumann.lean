import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

/-!
# Quantitative inversion from a small square

The relevant norm for matrices is the maximum absolute row sum.  The
perturbation itself may have norm larger than one: only its square is small.
These are algebraic/analytic results, not hypotheses asserting perfect weights.
-/

open scoped BigOperators Matrix.Norms.Operator

namespace EndpointMatching.Fractional.RobustWeights

noncomputable section

section BanachRing

variable {R : Type*} [NormedRing R] [NormOneClass R] [HasSummableGeomSeries R]

/-- A right inverse with the usual geometric-series bound. -/
theorem exists_right_inverse_one_sub (T : R) (hT : ‖T‖ < 1) :
    ∃ A : R, (1 - T) * A = 1 ∧ ‖A‖ ≤ 1 / (1 - ‖T‖) := by
  refine ⟨↑(Units.oneSub T hT)⁻¹, ?_, ?_⟩
  · exact (Units.oneSub T hT).val_inv
  · change ‖∑' n : ℕ, T ^ n‖ ≤ _
    simpa [norm_one, one_div] using tsum_geometric_le_of_norm_lt_one T hT

/-- Invert `1 + Z` using the small square `Z * Z`.  No smallness of `Z`
itself is required.  The displayed inverse is `(1 - Z) * (1 - Z²)⁻¹`. -/
theorem exists_right_inverse_of_square_small (Z : R) (hZ : ‖Z * Z‖ < 1) :
    ∃ A : R, (1 + Z) * A = 1 ∧
      ‖A‖ ≤ (1 + ‖Z‖) / (1 - ‖Z * Z‖) := by
  obtain ⟨S, hS, hnS⟩ := exists_right_inverse_one_sub (Z * Z) hZ
  refine ⟨(1 - Z) * S, ?_, ?_⟩
  · calc
      (1 + Z) * ((1 - Z) * S) = (1 - Z * Z) * S := by noncomm_ring
      _ = 1 := hS
  · calc
      ‖(1 - Z) * S‖ ≤ ‖1 - Z‖ * ‖S‖ := norm_mul_le _ _
      _ ≤ (1 + ‖Z‖) * (1 / (1 - ‖Z * Z‖)) :=
        mul_le_mul (by simpa using norm_sub_le (1 : R) Z) hnS
          (norm_nonneg _) (by positivity)
      _ = (1 + ‖Z‖) / (1 - ‖Z * Z‖) := by ring

/-- A later subtraction is paid for by a separate geometric series.  It is
uniform in the perturbation `F`; the hypothesis bounds `A * F`, not `F` alone. -/
theorem exists_right_inverse_sub (H A F : R) (hA : H * A = 1)
    (hF : ‖A * F‖ < 1) :
    ∃ A' : R, (H - F) * A' = 1 ∧
      ‖A'‖ ≤ ‖A‖ / (1 - ‖A * F‖) := by
  obtain ⟨S, hS, hnS⟩ := exists_right_inverse_one_sub (A * F) hF
  refine ⟨S * A, ?_, ?_⟩
  · calc
      (H - F) * (S * A) = (H * (1 - A * F)) * (S * A) := by
        rw [mul_sub, mul_one, ← mul_assoc H A F, hA, one_mul]
      _ = H * ((1 - A * F) * S) * A := by simp only [mul_assoc]
      _ = 1 := by rw [hS, mul_one, hA]
  · calc
      ‖S * A‖ ≤ ‖S‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ (1 / (1 - ‖A * F‖)) * ‖A‖ := mul_le_mul_of_nonneg_right hnS (norm_nonneg _)
      _ = ‖A‖ / (1 - ‖A * F‖) := by ring

/-- The manuscript's deliberately loose constants for the square-small step. -/
theorem square_small_bound (Z : R)
    (hZ : ‖Z‖ ≤ 17) (hZ2 : ‖Z * Z‖ ≤ 1 / 20) :
    ∃ A : R, (1 + Z) * A = 1 ∧ ‖A‖ ≤ 360 / 19 := by
  obtain ⟨A, hA, hnA⟩ := exists_right_inverse_of_square_small Z (by linarith)
  refine ⟨A, hA, hnA.trans ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < 1 - ‖Z * Z‖)).mpr
  nlinarith

end BanachRing

section Matrices

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Matrix form of the later-ban bound `32 / d → 36 / d`. -/
theorem inverse_sub_bound (H A F : Matrix V V ℝ) (d : ℝ) (hd : 0 < d)
    (hA : H * A = 1) (hnA : ‖A‖ ≤ 32 / d) (hnF : ‖F‖ ≤ 3 * d / 1000) :
    ∃ A' : Matrix V V ℝ, (H - F) * A' = 1 ∧ ‖A'‖ ≤ 36 / d := by
  have hAF : ‖A * F‖ ≤ 12 / 125 := by
    calc
      ‖A * F‖ ≤ ‖A‖ * ‖F‖ := norm_mul_le _ _
      _ ≤ (32 / d) * (3 * d / 1000) :=
        mul_le_mul hnA hnF (norm_nonneg _) (by positivity)
      _ = 12 / 125 := by field_simp; norm_num
  obtain ⟨A', hA', hnA'⟩ := exists_right_inverse_sub H A F hA (by linarith)
  refine ⟨A', hA', hnA'.trans ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < 1 - ‖A * F‖)).mpr
  have hpositive : 0 ≤ 36 / d := by positivity
  have hprod := mul_le_mul_of_nonneg_left (show 113 / 125 ≤ 1 - ‖A * F‖ by linarith) hpositive
  have h32 : 32 / d ≤ (36 / d) * (113 / 125) := by
    apply (div_le_iff₀ hd).mpr
    field_simp
    norm_num
  exact hnA.trans (h32.trans hprod)

end Matrices

end
end EndpointMatching.Fractional.RobustWeights
