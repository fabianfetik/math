import CorralFormalization.EndpointProof.Matching.Fractional.Fourier.Restriction

/-!
# A three-role zero-diagonal matrix costs two block norms

The factor two is proved in the genuine Euclidean norm.  It is independent
of the common role size, including size zero.
-/

open scoped Classical BigOperators Matrix

namespace EndpointMatching.Fractional.Fourier

noncomputable section

variable {I 𝕜 : Type*} [Fintype I] [DecidableEq I] [RCLike 𝕜]

def roleBlock (A : Matrix (Fin 3 × I) (Fin 3 × I) 𝕜) (r s : Fin 3) : Matrix I I 𝕜 :=
  fun i j => A (r, i) (s, j)

def roleVector (x : EuclideanSpace 𝕜 (Fin 3 × I)) (r : Fin 3) : EuclideanSpace 𝕜 I :=
  WithLp.toLp 2 (fun i => x (r, i))

theorem norm_sq_role_decomposition (x : EuclideanSpace 𝕜 (Fin 3 × I)) :
    ‖x‖ ^ 2 = ∑ r : Fin 3, ‖roleVector x r‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, roleVector,
    Fintype.sum_prod_type]

theorem roleVector_mul (A : Matrix (Fin 3 × I) (Fin 3 × I) 𝕜)
    (x : EuclideanSpace 𝕜 (Fin 3 × I)) (r : Fin 3) :
    roleVector (Matrix.toEuclideanCLM (𝕜 := 𝕜) A x) r =
      ∑ s : Fin 3, Matrix.toEuclideanCLM (𝕜 := 𝕜) (roleBlock A r s) (roleVector x s) := by
  ext i
  change (∑ v : Fin 3 × I, A (r, i) v * x v) =
    (∑ s : Fin 3, Matrix.toEuclideanCLM (𝕜 := 𝕜) (roleBlock A r s) (roleVector x s)).ofLp i
  simp only [WithLp.ofLp_sum, Finset.sum_apply, Matrix.ofLp_toEuclideanCLM,
    Matrix.mulVec, dotProduct, roleBlock, roleVector,
    Fintype.sum_prod_type]

theorem roleVector_mul_norm_le (A : Matrix (Fin 3 × I) (Fin 3 × I) 𝕜)
    (B : ℝ) (_hB : 0 ≤ B)
    (hzero : ∀ r, roleBlock A r r = 0)
    (hblock : ∀ r s, r ≠ s → ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (roleBlock A r s)‖ ≤ B)
    (x : EuclideanSpace 𝕜 (Fin 3 × I)) (r : Fin 3) :
    ‖roleVector (Matrix.toEuclideanCLM (𝕜 := 𝕜) A x) r‖ ≤
      B * ∑ s : Fin 3, if r = s then 0 else ‖roleVector x s‖ := by
  rw [roleVector_mul]
  calc
    _ ≤ ∑ s : Fin 3, ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (roleBlock A r s) (roleVector x s)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ s : Fin 3, B * (if r = s then 0 else ‖roleVector x s‖) := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hrs : r = s
      · subst s
        simp only [hzero, map_zero, zero_apply, norm_zero, ite_true, mul_zero, le_refl]
      · simp only [hrs, if_false]
        exact ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (roleBlock A r s)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hblock r s hrs) (norm_nonneg _))
    _ = _ := (Finset.mul_sum ..).symm

/-- A three-by-three role matrix with zero diagonal blocks and off-diagonal
L² block norm at most `B` has total L² norm at most `2B`. -/
theorem three_role_L2_operator_norm_le (A : Matrix (Fin 3 × I) (Fin 3 × I) 𝕜)
    (B : ℝ) (hB : 0 ≤ B) (hzero : ∀ r, roleBlock A r r = 0)
    (hblock : ∀ r s, r ≠ s → ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (roleBlock A r s)‖ ≤ B) :
    ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) A‖ ≤ 2 * B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  let y := Matrix.toEuclideanCLM (𝕜 := 𝕜) A x
  let a : Fin 3 → ℝ := fun r => ‖roleVector x r‖
  let b : Fin 3 → ℝ := fun r => ‖roleVector y r‖
  have hrow (r : Fin 3) : b r ≤ B * ∑ s : Fin 3, if r = s then 0 else a s :=
    roleVector_mul_norm_le A B hB hzero hblock x r
  have h0 : b 0 ≤ B * (a 1 + a 2) := by simpa [Fin.sum_univ_succ] using hrow 0
  have h1 : b 1 ≤ B * (a 0 + a 2) := by simpa [Fin.sum_univ_succ] using hrow 1
  have h2 : b 2 ≤ B * (a 0 + a 1) := by simpa [Fin.sum_univ_succ] using hrow 2
  have h0sq := pow_le_pow_left₀ (norm_nonneg _) h0 2
  have h1sq := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2sq := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hpairs : (a 1 + a 2) ^ 2 + (a 0 + a 2) ^ 2 + (a 0 + a 1) ^ 2 ≤
      4 * ((a 0) ^ 2 + (a 1) ^ 2 + (a 2) ^ 2) := by
    nlinarith [sq_nonneg (a 0 - a 1), sq_nonneg (a 0 - a 2), sq_nonneg (a 1 - a 2)]
  have hmult := mul_le_mul_of_nonneg_left hpairs (sq_nonneg B)
  have hsum : (b 0) ^ 2 + (b 1) ^ 2 + (b 2) ^ 2 ≤
      4 * B ^ 2 * ((a 0) ^ 2 + (a 1) ^ 2 + (a 2) ^ 2) := by
    nlinarith
  have hx : ‖x‖ ^ 2 = (a 0) ^ 2 + (a 1) ^ 2 + (a 2) ^ 2 := by
    simpa [Fin.sum_univ_succ, a, add_assoc] using norm_sq_role_decomposition x
  have hy : ‖y‖ ^ 2 = (b 0) ^ 2 + (b 1) ^ 2 + (b 2) ^ 2 := by
    simpa [Fin.sum_univ_succ, b, add_assoc] using norm_sq_role_decomposition y
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg x))).mp
  change ‖y‖ ^ 2 ≤ (2 * B * ‖x‖) ^ 2
  rw [hy, mul_pow, mul_pow, hx]
  norm_num
  exact hsum

end
end EndpointMatching.Fractional.Fourier
