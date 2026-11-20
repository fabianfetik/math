import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.NormalizeSpectral
import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Blocks

/-!
# The raw row estimates and the numerical square constant

Every raw off-diagonal entry has absolute value at most one and there are
two partner blocks per row.  Combining this fact with the raw Euclidean
operator estimate gives the precise small-square constant needed by the
proved robust inversion theorem.
-/

open scoped Classical BigOperators Matrix Matrix.Norms.Operator

namespace EndpointMatching.Fractional.RobustWeights

open EndpointFractionalRawEvent
noncomputable section

variable {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I] [DecidableEq I]

theorem offDiagonal_row_vectorL2_le (coord : (Fin 3 × I) → G)
    (R : Fin 3 → Finset G) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (v : Fin 3 × I) :
    vectorL2 (offDiagonal coord R q v) ≤ Real.sqrt (2 * (Fintype.card I : ℝ)) := by
  have hentry (s : Fin 3) (i : I) : (offDiagonal coord R q v (s,i)) ^ 2 ≤
      if v.1 = s then 0 else (1 : ℝ) := by
    by_cases hrole : v.1 = s
    · simp [offDiagonal, hrole]
    · simp only [offDiagonal, hrole, if_false]
      have hb : 0 ≤ setBit (R (thirdRole v.1 s)) (requiredCoordinate coord v (s,i)) ∧
          setBit (R (thirdRole v.1 s)) (requiredCoordinate coord v (s,i)) ≤ 1 := by
        unfold setBit
        split_ifs <;> norm_num
      nlinarith [mul_nonneg
        (show 0 ≤ 1 - (setBit (R (thirdRole v.1 s)) (requiredCoordinate coord v (s,i)) - q) by linarith)
        (show 0 ≤ 1 + (setBit (R (thirdRole v.1 s)) (requiredCoordinate coord v (s,i)) - q) by linarith)]
  have hsq : (∑ u, (offDiagonal coord R q v u) ^ 2) ≤ 2 * (Fintype.card I : ℝ) := by
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ s : Fin 3, ∑ _ : I, if v.1 = s then (0 : ℝ) else 1 :=
        Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun i _ => hentry s i))
      _ = _ := by
        rcases v with ⟨r,i⟩
        fin_cases r <;> simp [Fin.sum_univ_succ] <;> ring
  apply Real.le_sqrt_of_sq_le
  rw [vectorL2_sq]
  exact hsq

private theorem sqrt_two_mul_sqrt_three (m : ℝ) (hm : 0 ≤ m) :
    Real.sqrt (2 * m) * Real.sqrt (3 * m) = Real.sqrt 6 * m := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * m)]
  have heq : 2 * m * (3 * m) = 6 * m ^ 2 := by ring
  rw [heq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_sq hm]

/-- The constant `33` is checked over the reals; no decimal rounding is
used.  This result only needs the actual raw L2 estimate as analytic input. -/
theorem raw_square_constant (q n m d : ℝ) (hn : 0 ≤ n) (hm : 0 ≤ m) (hmn : m ≤ n)
    (hd : 0 < d) (hscale : q ^ 2 * n / 2 ≤ d) :
    (5 / 3) * Real.sqrt (2 * m) * (2 * (q ^ 4 / 100000) * n) *
      Real.sqrt (3 * m) / d ^ 2 ≤ 33 / 100000 := by
  have hsqrt : Real.sqrt (6 : ℝ) ≤ 99 / 40 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_nonneg (6 : ℝ)]
  have hcoef : (10 / 3 : ℝ) * Real.sqrt 6 ≤ 33 / 4 := by nlinarith
  have hscale2 : q ^ 4 * n ^ 2 / 4 ≤ d ^ 2 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ q ^ 2 * n / 2) hscale 2
    nlinarith
  have hnm : n * m ≤ n ^ 2 := by nlinarith
  calc
    _ = ((10 / 3) * Real.sqrt 6) * (q ^ 4 / 100000) * (n * m) / d ^ 2 := by
      have h := sqrt_two_mul_sqrt_three m hm
      calc
        _ = (10 / 3) * (q ^ 4 / 100000) * n *
            (Real.sqrt (2 * m) * Real.sqrt (3 * m)) / d ^ 2 := by ring
        _ = _ := by rw [h]; ring
    _ ≤ (33 / 4) * (q ^ 4 / 100000) * n ^ 2 / d ^ 2 := by
      gcongr
    _ = (33 / 100000) * (q ^ 4 * n ^ 2 / 4) / d ^ 2 := by ring
    _ ≤ (33 / 100000) * d ^ 2 / d ^ 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale2 (by norm_num)) (sq_nonneg d)
    _ = 33 / 100000 := by field_simp

variable [Nonempty I]

/-- The final small-square input is proved from the raw Euclidean operator
bound.  The target rows/columns may be arbitrary; no target Fourier bound
is requested or used. -/
theorem offDiagonal_normalized_square_le (coord : (Fin 3 × I) → G)
    (R : Fin 3 → Finset G) (q n d : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hn : 0 ≤ n) (hmn : (Fintype.card I : ℝ) ≤ n) (hd : 0 < d)
    (hscale : q ^ 2 * n / 2 ≤ d)
    (hL2 : l2OperatorNorm (offDiagonal coord R q) ≤ 2 * (q ^ 4 / 100000) * n) :
    ‖normalizeError d (offDiagonal coord R q) * normalizeError d (offDiagonal coord R q)‖ ≤ 33 / 100000 := by
  calc
    _ ≤ (5 / 3) * Real.sqrt (2 * (Fintype.card I : ℝ)) *
        (2 * (q ^ 4 / 100000) * n) * Real.sqrt (3 * (Fintype.card I : ℝ)) / d ^ 2 :=
      normalizeError_square_norm_le d _ _ hd (Real.sqrt_nonneg _) _
        (offDiagonal_row_vectorL2_le coord R q hq0 hq1) hL2
    _ ≤ _ := raw_square_constant q n (Fintype.card I : ℝ) d hn (Nat.cast_nonneg _) hmn hd hscale

end
end EndpointMatching.Fractional.RobustWeights
