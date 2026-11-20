import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Norms
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# From Euclidean estimates to a small row-sum square

The two matrix norms are kept explicit.  `l2OperatorNorm` is the Euclidean
operator norm, while the ordinary matrix norm in the final theorem is the
maximum absolute row sum.  This pays the generic mixed-norm inequality used
in the manuscript, independently of the still separate Fourier bound.
-/

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace EndpointMatching.Fractional.RobustWeights

open WithLp
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def vectorL2 (x : V → ℝ) : ℝ := ‖(toLp 2 x : EuclideanSpace ℝ V)‖

open scoped Matrix.Norms.L2Operator in
def l2OperatorNorm (A : Matrix V V ℝ) : ℝ := ‖A‖

theorem vectorL2_nonneg (x : V → ℝ) : 0 ≤ vectorL2 x := norm_nonneg _

theorem l2OperatorNorm_eq_clm (A : Matrix V V ℝ) :
    l2OperatorNorm A = ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) A‖ := rfl

theorem l2OperatorNorm_nonneg (A : Matrix V V ℝ) : 0 ≤ l2OperatorNorm A := by
  rw [l2OperatorNorm_eq_clm]
  exact norm_nonneg _

theorem vectorL2_mulVec_le (A : Matrix V V ℝ) (x : V → ℝ) :
    vectorL2 (A *ᵥ x) ≤ l2OperatorNorm A * vectorL2 x := by
  change ‖(toLp 2 (A *ᵥ x) : EuclideanSpace ℝ V)‖ ≤ _
  rw [← Matrix.toEuclideanCLM_toLp]
  exact (Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) A).le_opNorm (toLp 2 x)

open scoped Matrix.Norms.L2Operator in
theorem l2OperatorNorm_transpose (A : Matrix V V ℝ) :
    l2OperatorNorm Aᵀ = l2OperatorNorm A := by
  have hs : Aᴴ = Aᵀ := by ext i j; simp
  change ‖Aᵀ‖ = ‖A‖
  rw [← hs]
  exact Matrix.l2_opNorm_conjTranspose A

/-- Finite Cauchy--Schwarz converts a Euclidean row estimate to an absolute
row sum, paying exactly the square root of the number of columns. -/
theorem sum_abs_le_vectorL2 (x : V → ℝ) :
    (∑ i, |x i|) ≤ vectorL2 x * Real.sqrt (Fintype.card V : ℝ) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |x i|) (fun _ => (1 : ℝ))
  simpa [vectorL2, EuclideanSpace.norm_eq, Real.norm_eq_abs] using h

theorem matrix_product_row_transpose (A B : Matrix V V ℝ) (i : V) :
    (A * B) i = Bᵀ *ᵥ A i := by
  ext j
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-- The manuscript's mixed-norm square estimate.  This is proved for every
finite real matrix, without symmetry or a Fourier hypothesis. -/
theorem matrix_square_row_sum_norm_le (A : Matrix V V ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ i, vectorL2 (A i) ≤ R) :
    ‖A * A‖ ≤ R * l2OperatorNorm A * Real.sqrt (Fintype.card V : ℝ) := by
  apply matrix_norm_le_of_row_sum_le _ _
    (mul_nonneg (mul_nonneg hR (l2OperatorNorm_nonneg A)) (Real.sqrt_nonneg _))
  intro i
  calc
    (∑ j, |(A * A) i j|) ≤ vectorL2 ((A * A) i) * Real.sqrt (Fintype.card V : ℝ) :=
      sum_abs_le_vectorL2 _
    _ ≤ (l2OperatorNorm A * vectorL2 (A i)) * Real.sqrt (Fintype.card V : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      rw [matrix_product_row_transpose]
      simpa only [l2OperatorNorm_transpose] using vectorL2_mulVec_le Aᵀ (A i)
    _ ≤ (l2OperatorNorm A * R) * Real.sqrt (Fintype.card V : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hrow i) (l2OperatorNorm_nonneg A)) (Real.sqrt_nonneg _)
    _ = _ := by ring

end
end EndpointMatching.Fractional.RobustWeights
