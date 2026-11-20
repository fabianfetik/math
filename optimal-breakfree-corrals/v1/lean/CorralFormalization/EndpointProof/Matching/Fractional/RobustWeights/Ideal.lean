import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Norms

/-!
# The ideal Gram matrix and its bounded inverse

The ideal off-diagonal blocks have constant entries `d / m`; when `d = q m`
these are exactly `q J`.  The two zero role modes are regularized by `d K`.
-/

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace EndpointMatching.Fractional.RobustWeights

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

def idealGram (d : ℝ) : Matrix (Fin 3 × I) (Fin 3 × I) ℝ :=
  d • (1 + (3 : ℝ) • constantProjection - roleProjection)

def idealRegularized (d : ℝ) : Matrix (Fin 3 × I) (Fin 3 × I) ℝ :=
  d • (1 + (2 : ℝ) • constantProjection)

/-- The matrix denoted `Q` in the manuscript. -/
def inverseNumerator : Matrix (Fin 3 × I) (Fin 3 × I) ℝ :=
  1 - (2 / 3 : ℝ) • constantProjection

omit [Nonempty I] in
theorem idealGram_apply (d : ℝ) (v u : Fin 3 × I) :
    idealGram d v u = (if v = u then d else 0) +
      (if v.1 = u.1 then 0 else d / (Fintype.card I : ℝ)) := by
  by_cases hvu : v = u
  · subst u
    simp [idealGram, constantProjection, roleProjection]
    ring
  · by_cases hrole : v.1 = u.1
    · simp [idealGram, constantProjection, roleProjection, hvu, hrole]
      ring_nf
      simp
    · simp [idealGram, constantProjection, roleProjection, hvu, hrole]
      ring

omit [Nonempty I] in
/-- Adding `d K` removes exactly the two role-constant zero modes. -/
theorem idealGram_add_roleKernelProjection (d : ℝ) :
    idealGram (I := I) d + d • roleKernelProjection = idealRegularized d := by
  unfold idealGram roleKernelProjection idealRegularized
  module

theorem constantProjection_norm_le : ‖constantProjection (I := I)‖ ≤ 1 := by
  apply matrix_norm_le_of_row_sum_le _ _ zero_le_one
  intro v
  have hm : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  simp only [constantProjection, abs_of_pos (by positivity : (0 : ℝ) < 1 / (3 * (Fintype.card I : ℝ))),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_ofNat]
  exact le_of_eq (by field_simp)

theorem inverseNumerator_norm_le : ‖inverseNumerator (I := I)‖ ≤ 5 / 3 := by
  calc
    ‖inverseNumerator (I := I)‖ ≤ ‖(1 : Matrix (Fin 3 × I) (Fin 3 × I) ℝ)‖ +
        ‖(2 / 3 : ℝ) • constantProjection (I := I)‖ := norm_sub_le _ _
    _ ≤ 1 + (2 / 3 : ℝ) * 1 := by
      rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
      exact add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left
        (constantProjection_norm_le (I := I)) (by norm_num : (0 : ℝ) ≤ 2 / 3))
    _ = 5 / 3 := by norm_num

theorem idealRegularized_mul_inverseNumerator (d : ℝ) (hd : d ≠ 0) :
    idealRegularized (I := I) d * (d⁻¹ • inverseNumerator) = 1 := by
  have hbase : (1 + (2 : ℝ) • constantProjection (I := I)) * inverseNumerator = 1 := by
    unfold inverseNumerator
    rw [mul_sub, mul_one, Matrix.mul_smul, add_mul, one_mul,
      Matrix.smul_mul, constantProjection_idempotent]
    module
  unfold idealRegularized
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hbase, mul_inv_cancel₀ hd, one_smul]

/-- The paper's row-sum inverse bound before a later ban.  The hypotheses
display the factorization and both norms; no inverse is assumed. -/
theorem exists_inverse_of_factorization
    (H Z : Matrix (Fin 3 × I) (Fin 3 × I) ℝ) (d : ℝ) (hd : 0 < d)
    (hfactor : H = idealRegularized d * (1 + Z))
    (hZ : ‖Z‖ ≤ 17) (hZ2 : ‖Z * Z‖ ≤ 1 / 20) :
    ∃ A : Matrix (Fin 3 × I) (Fin 3 × I) ℝ, H * A = 1 ∧ ‖A‖ ≤ 32 / d := by
  obtain ⟨S, hS, hnS⟩ := square_small_bound Z hZ hZ2
  refine ⟨S * (d⁻¹ • inverseNumerator), ?_, ?_⟩
  · rw [hfactor, mul_assoc, ← mul_assoc (1 + Z), hS, one_mul]
    exact idealRegularized_mul_inverseNumerator d hd.ne'
  · calc
      ‖S * (d⁻¹ • inverseNumerator)‖ ≤ ‖S‖ * ‖d⁻¹ • inverseNumerator (I := I)‖ := norm_mul_le _ _
      _ ≤ (360 / 19) * (d⁻¹ * (5 / 3)) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
        exact mul_le_mul hnS
          (mul_le_mul_of_nonneg_left inverseNumerator_norm_le (by positivity))
          (by positivity) (by norm_num)
      _ ≤ 32 / d := by
        apply (le_div_iff₀ hd).mpr
        field_simp
        norm_num

end
end EndpointMatching.Fractional.RobustWeights
