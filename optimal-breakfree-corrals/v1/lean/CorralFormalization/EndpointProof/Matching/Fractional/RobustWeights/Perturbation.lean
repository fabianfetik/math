import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Ideal

/-!
# Separating the raw error from later edits

This is the deterministic matrix reduction after the raw error has been
estimated.  The raw block's square must be small; its row-sum norm may be
larger than one.  The remaining obligations are explicit bounds on matrices,
not an assumed inverse and not assumed fractional weights.
-/

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace EndpointMatching.Fractional.RobustWeights

noncomputable section

section NormedRing

variable {R : Type*} [NormedRing R]

/-- The manuscript constants really do make the combined square small. -/
theorem small_square_of_split (U V : R)
    (hU : ‖U‖ ≤ 1 / 750) (hV : ‖V‖ ≤ 50 / 3)
    (hV2 : ‖V * V‖ ≤ 33 / 100000) :
    ‖U + V‖ ≤ 17 ∧ ‖(U + V) * (U + V)‖ ≤ 1 / 20 := by
  have hUU : ‖U * U‖ ≤ (1 / 750 : ℝ) * (1 / 750) :=
    (norm_mul_le _ _).trans (mul_le_mul hU hU (norm_nonneg _) (by norm_num))
  have hUV : ‖U * V‖ ≤ (1 / 750 : ℝ) * (50 / 3) :=
    (norm_mul_le _ _).trans (mul_le_mul hU hV (norm_nonneg _) (by norm_num))
  have hVU : ‖V * U‖ ≤ (50 / 3 : ℝ) * (1 / 750) :=
    (norm_mul_le _ _).trans (mul_le_mul hV hU (norm_nonneg _) (by norm_num))
  constructor
  · linarith [norm_add_le U V]
  · have hexpand : (U + V) * (U + V) = U * U + U * V + V * U + V * V := by noncomm_ring
    rw [hexpand]
    have hnorm : ‖U * U + U * V + V * U + V * V‖ ≤
        ‖U * U‖ + ‖U * V‖ + ‖V * U‖ + ‖V * V‖ := by
      calc
        _ ≤ ‖U * U + U * V + V * U‖ + ‖V * V‖ := norm_add_le _ _
        _ ≤ (‖U * U + U * V‖ + ‖V * U‖) + ‖V * V‖ := by gcongr; apply norm_add_le
        _ ≤ _ := by gcongr; apply norm_add_le
    linarith

end NormedRing

variable {I E : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype E]

/-- Normalized perturbation by the proved ideal inverse. -/
def normalizeError (d : ℝ) (T : Matrix (Fin 3 × I) (Fin 3 × I) ℝ) :
    Matrix (Fin 3 × I) (Fin 3 × I) ℝ := (d⁻¹ • inverseNumerator) * T

/-- The factorization follows from the actual Gram decomposition. -/
theorem regularized_factorization (edge : E → Fin 3 → I) (d : ℝ) (hd : d ≠ 0)
    (D Ed N : Matrix (Fin 3 × I) (Fin 3 × I) ℝ)
    (hdecomp : gram edge = idealGram d + (D + Ed) + N) :
    gram edge + d • roleKernelProjection = idealRegularized d *
      (1 + (normalizeError d (D + Ed) + normalizeError d N)) := by
  unfold normalizeError
  rw [mul_add, mul_one, mul_add, ← mul_assoc, ← mul_assoc,
    idealRegularized_mul_inverseNumerator d hd, one_mul, one_mul]
  rw [hdecomp, ← idealGram_add_roleKernelProjection]
  abel

/-- Fully proved inversion from the explicit raw/edit split used for the quantitative remainder estimate.
The two normalized-norm estimates and the raw-square estimate are still
mathematical inputs, exposed individually for the Fourier/edit bridge. -/
theorem exists_inverse_of_error_split (edge : E → Fin 3 → I) (d : ℝ) (hd : 0 < d)
    (D Ed N : Matrix (Fin 3 × I) (Fin 3 × I) ℝ)
    (hdecomp : gram edge = idealGram d + (D + Ed) + N)
    (hU : ‖normalizeError d (D + Ed)‖ ≤ 1 / 750)
    (hV : ‖normalizeError d N‖ ≤ 50 / 3)
    (hV2 : ‖normalizeError d N * normalizeError d N‖ ≤ 33 / 100000) :
    ∃ A : Matrix (Fin 3 × I) (Fin 3 × I) ℝ,
      (gram edge + d • roleKernelProjection) * A = 1 ∧ ‖A‖ ≤ 32 / d := by
  have hsmall := small_square_of_split _ _ hU hV hV2
  exact exists_inverse_of_factorization _ _ d hd
    (regularized_factorization edge d hd.ne' D Ed N hdecomp) hsmall.1 hsmall.2

end
end EndpointMatching.Fractional.RobustWeights
