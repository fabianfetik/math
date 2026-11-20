import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.SpectralSquare
import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Ideal
import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Perturbation

/-!
# Euclidean estimates for the ideal normalization

This file distinguishes the Euclidean contraction of `Q` from its row-sum
bound `5/3`.  Both are needed: the former preserves the raw spectral error,
and the latter bounds every Euclidean row after multiplication by `Q`.
-/

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace EndpointMatching.Fractional.RobustWeights

open WithLp
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem vectorL2_sq (x : V → ℝ) : (vectorL2 x) ^ 2 = ∑ i, (x i) ^ 2 :=
  EuclideanSpace.real_norm_sq_eq (toLp 2 x)

theorem vectorL2_smul (c : ℝ) (x : V → ℝ) : vectorL2 (c • x) = |c| * vectorL2 x := by
  change ‖c • (toLp 2 x : EuclideanSpace ℝ V)‖ = _
  rw [norm_smul, Real.norm_eq_abs]
  rfl

open scoped Matrix.Norms.L2Operator in
theorem l2OperatorNorm_mul_le (A B : Matrix V V ℝ) :
    l2OperatorNorm (A * B) ≤ l2OperatorNorm A * l2OperatorNorm B := by
  exact Matrix.l2_opNorm_mul A B

theorem l2OperatorNorm_smul (c : ℝ) (A : Matrix V V ℝ) :
    l2OperatorNorm (c • A) = |c| * l2OperatorNorm A := by
  rw [l2OperatorNorm_eq_clm, l2OperatorNorm_eq_clm, map_smul, norm_smul, Real.norm_eq_abs]

/-- Multiplying rows by a matrix costs its absolute row-sum norm. -/
theorem product_row_vectorL2_le (A B : Matrix V V ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ i, vectorL2 (B i) ≤ R) (i : V) :
    vectorL2 ((A * B) i) ≤ ‖A‖ * R := by
  have heq : (toLp 2 ((A * B) i) : EuclideanSpace ℝ V) =
      ∑ k, A i k • (toLp 2 (B k) : EuclideanSpace ℝ V) := by
    ext j
    simp [Matrix.mul_apply]
  unfold vectorL2
  rw [heq]
  calc
    ‖∑ k, A i k • (toLp 2 (B k) : EuclideanSpace ℝ V)‖ ≤
        ∑ k, ‖A i k • (toLp 2 (B k) : EuclideanSpace ℝ V)‖ := norm_sum_le _ _
    _ = ∑ k, |A i k| * vectorL2 (B k) := by simp [norm_smul, vectorL2, Real.norm_eq_abs]
    _ ≤ ∑ k, |A i k| * R :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hrow k) (abs_nonneg _))
    _ = (∑ k, |A i k|) * R := (Finset.sum_mul ..).symm
    _ ≤ ‖A‖ * R := mul_le_mul_of_nonneg_right (row_sum_le_matrix_norm A i) hR

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- `Q` decreases Euclidean vector norms; its constant mode has eigenvalue
`1/3` and its zero-sum modes have eigenvalue `1`. -/
theorem inverseNumerator_vectorL2_le (x : (Fin 3 × I) → ℝ) :
    vectorL2 (inverseNumerator *ᵥ x) ≤ vectorL2 x := by
  let k : ℝ := 3 * (Fintype.card I : ℝ)
  let s : ℝ := ∑ v, x v
  let c : ℝ := (2 / 3) * (s / k)
  have hk : 0 < k := by
    dsimp [k]
    have hm : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    positivity
  have happly : inverseNumerator *ᵥ x = fun v => x v - c := by
    ext v
    simp only [inverseNumerator, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, constantProjection_apply]
    dsimp [c, s, k]
    rw [Fintype.sum_prod_type]
    rfl
  have hexpand : (∑ v, (x v - c) ^ 2) = (∑ v, (x v) ^ 2) - 2 * c * s + k * c ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
      Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [s, k]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hcor : -2 * c * s + k * c ^ 2 = -(8 / (9 * k)) * s ^ 2 := by
    dsimp [c]
    field_simp
    ring
  apply (sq_le_sq₀ (vectorL2_nonneg _) (vectorL2_nonneg _)).mp
  rw [vectorL2_sq, vectorL2_sq, happly, hexpand]
  have hnonneg : 0 ≤ (8 / (9 * k)) * s ^ 2 := by positivity
  linarith [hcor]

theorem inverseNumerator_l2OperatorNorm_le : l2OperatorNorm (inverseNumerator (I := I)) ≤ 1 := by
  rw [l2OperatorNorm_eq_clm]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change vectorL2 (inverseNumerator *ᵥ ofLp x) ≤ 1 * vectorL2 (ofLp x)
  simpa using inverseNumerator_vectorL2_le (ofLp x)

theorem normalizeError_l2OperatorNorm_le (d L : ℝ) (hd : 0 < d)
    (N : Matrix (Fin 3 × I) (Fin 3 × I) ℝ) (hN : l2OperatorNorm N ≤ L) :
    l2OperatorNorm (normalizeError d N) ≤ d⁻¹ * L := by
  have hL : 0 ≤ L := (l2OperatorNorm_nonneg N).trans hN
  unfold normalizeError
  calc
    l2OperatorNorm ((d⁻¹ • inverseNumerator) * N) ≤
        l2OperatorNorm (d⁻¹ • inverseNumerator (I := I)) * l2OperatorNorm N := l2OperatorNorm_mul_le _ _
    _ = (d⁻¹ * l2OperatorNorm (inverseNumerator (I := I))) * l2OperatorNorm N := by
      rw [l2OperatorNorm_smul, abs_of_pos (inv_pos.mpr hd)]
    _ ≤ (d⁻¹ * 1) * L := mul_le_mul
      (mul_le_mul_of_nonneg_left inverseNumerator_l2OperatorNorm_le (by positivity)) hN
      (l2OperatorNorm_nonneg N) (by positivity)
    _ = d⁻¹ * L := by ring

theorem normalizeError_row_vectorL2_le (d R : ℝ) (hd : 0 < d) (hR : 0 ≤ R)
    (N : Matrix (Fin 3 × I) (Fin 3 × I) ℝ) (hrow : ∀ i, vectorL2 (N i) ≤ R)
    (i : Fin 3 × I) :
    vectorL2 (normalizeError d N i) ≤ (d⁻¹ * (5 / 3)) * R := by
  unfold normalizeError
  rw [Matrix.smul_mul]
  change vectorL2 (d⁻¹ • ((inverseNumerator (I := I) * N) i)) ≤ _
  rw [vectorL2_smul, abs_of_pos (inv_pos.mpr hd)]
  calc
    d⁻¹ * vectorL2 ((inverseNumerator (I := I) * N) i) ≤ d⁻¹ * (‖inverseNumerator (I := I)‖ * R) :=
      mul_le_mul_of_nonneg_left (product_row_vectorL2_le _ N R hR hrow i) (by positivity)
    _ ≤ d⁻¹ * ((5 / 3) * R) := by
      gcongr
      exact inverseNumerator_norm_le
    _ = _ := by ring

/-- All mixed-norm effects of the ideal inverse are now paid.  The input
`L` is a bound on the *raw* matrix's Euclidean operator norm. -/
theorem normalizeError_square_norm_le (d R L : ℝ) (hd : 0 < d) (hR : 0 ≤ R)
    (N : Matrix (Fin 3 × I) (Fin 3 × I) ℝ) (hrow : ∀ i, vectorL2 (N i) ≤ R)
    (hN : l2OperatorNorm N ≤ L) :
    ‖normalizeError d N * normalizeError d N‖ ≤
      (5 / 3) * R * L * Real.sqrt (3 * (Fintype.card I : ℝ)) / d ^ 2 := by
  have hL : 0 ≤ L := (l2OperatorNorm_nonneg N).trans hN
  calc
    _ ≤ ((d⁻¹ * (5 / 3)) * R) * l2OperatorNorm (normalizeError d N) *
        Real.sqrt (Fintype.card (Fin 3 × I) : ℝ) :=
      matrix_square_row_sum_norm_le _ _ (by positivity)
        (normalizeError_row_vectorL2_le d R hd hR N hrow)
    _ ≤ ((d⁻¹ * (5 / 3)) * R) * (d⁻¹ * L) * Real.sqrt (Fintype.card (Fin 3 × I) : ℝ) := by
      gcongr
      exact normalizeError_l2OperatorNorm_le d L hd N hN
    _ = _ := by simp [Fintype.card_prod, Fintype.card_fin]; ring

end
end EndpointMatching.Fractional.RobustWeights
