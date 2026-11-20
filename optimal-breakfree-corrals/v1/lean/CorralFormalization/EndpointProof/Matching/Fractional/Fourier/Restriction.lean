import CorralFormalization.EndpointProof.Matching.Fractional.Fourier.Convolution

/-!
# L² restriction and real/complex coefficient transport

Restriction is proved on Euclidean spaces with their genuine L² norms.
Rows and columns may be restricted by different injections. No matrix-norm
or Fourier supplier is assumed in these deterministic transport lemmas.
-/

open scoped Classical BigOperators Matrix

namespace EndpointMatching.Fractional.Fourier

noncomputable section

variable {I J 𝕜 : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [RCLike 𝕜]

/-- Coordinate restriction along an injection is an L² contraction. -/
theorem euclidean_restrict_norm_le (f : I → J) (hf : Function.Injective f)
    (x : EuclideanSpace 𝕜 J) :
    ‖(WithLp.toLp 2 (fun i => x (f i)) : EuclideanSpace 𝕜 I)‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc
    (∑ i, ‖x (f i)‖ ^ 2) = ∑ j ∈ Finset.univ.image f, ‖x j‖ ^ 2 := by
      rw [Finset.sum_image (fun i _ k _ h => hf h)]
    _ ≤ ∑ j, ‖x j‖ ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

/-- A concrete zero extension; injectivity is needed only for its norm. -/
def zeroExtend (f : I → J) (x : I → 𝕜) : J → 𝕜 :=
  fun j => ∑ i, if f i = j then x i else 0

@[simp] theorem zeroExtend_apply (f : I → J) (hf : Function.Injective f)
    (x : I → 𝕜) (i : I) : zeroExtend f x (f i) = x i := by
  simp [zeroExtend, hf.eq_iff]

theorem zeroExtend_eq_zero (f : I → J) (x : I → 𝕜) (j : J)
    (hj : j ∉ Finset.univ.image f) : zeroExtend f x j = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (fun h => hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩))

/-- Zero extension along an injection preserves the L² norm exactly. -/
theorem euclidean_zeroExtend_norm (f : I → J) (hf : Function.Injective f)
    (x : I → 𝕜) :
    ‖(WithLp.toLp 2 (zeroExtend f x) : EuclideanSpace 𝕜 J)‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 I)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  calc
    (∑ j, ‖zeroExtend f x j‖ ^ 2) =
        ∑ j ∈ Finset.univ.image f, ‖zeroExtend f x j‖ ^ 2 := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro j _ hj
      rw [zeroExtend_eq_zero f x j hj]
      simp
    _ = ∑ i, ‖zeroExtend f x (f i)‖ ^ 2 := Finset.sum_image (fun i _ k _ h => hf h)
    _ = ∑ i, ‖x i‖ ^ 2 := by simp only [zeroExtend_apply f hf]

theorem submatrix_mulVec_zeroExtend (A : Matrix J J 𝕜) (r c : I → J) (x : I → 𝕜) :
    (A.submatrix r c) *ᵥ x = fun i => (A *ᵥ zeroExtend c x) (r i) := by
  ext i
  change (∑ k, A (r i) (c k) * x k) = ∑ j, A (r i) j * ∑ k, if c k = j then x k else 0
  symm
  calc
    _ = ∑ j, ∑ k, A (r i) j * (if c k = j then x k else 0) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ k, ∑ j, A (r i) j * (if c k = j then x k else 0) := Finset.sum_comm
    _ = _ := by simp [mul_ite]

/-- Arbitrary different row and column injections cannot increase the
genuine L² operator norm of a square matrix. -/
theorem submatrix_L2_operator_norm_le (A : Matrix J J 𝕜)
    (r c : I → J) (hr : Function.Injective r) (hc : Function.Injective c) :
    ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := I) (A.submatrix r c)‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := J) A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let y : EuclideanSpace 𝕜 J := WithLp.toLp 2 (zeroExtend c (WithLp.ofLp x))
  have hmul : Matrix.toEuclideanCLM (𝕜 := 𝕜) (A.submatrix r c) x =
      WithLp.toLp 2 (fun i => (Matrix.toEuclideanCLM (𝕜 := 𝕜) A y) (r i)) := by
    ext i
    exact congrFun (submatrix_mulVec_zeroExtend A r c (WithLp.ofLp x)) i
  rw [hmul]
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) A y‖ := euclidean_restrict_norm_le r hr _
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) A‖ * ‖y‖ :=
      (Matrix.toEuclideanCLM (𝕜 := 𝕜) A).le_opNorm y
    _ = _ := by rw [euclidean_zeroExtend_norm c hc]

/-- A real matrix with its unchanged coefficients viewed in `ℂ`. -/
def complexify (A : Matrix I I ℝ) : Matrix I I ℂ := fun i j => (A i j : ℂ)

theorem euclidean_ofReal_norm (x : I → ℝ) :
    ‖(WithLp.toLp 2 (fun i => (x i : ℂ)) : EuclideanSpace ℂ I)‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ I)‖ := by
  simp only [EuclideanSpace.norm_eq, Complex.norm_real, Real.norm_eq_abs]

/-- The direction needed to import a complex Fourier bound for a real
matrix: its real L² operator norm is no larger. -/
theorem real_L2_operator_norm_le_complex (A : Matrix I I ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (complexify A)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let z : EuclideanSpace ℂ I := WithLp.toLp 2 (fun i => (x i : ℂ))
  have hmul : Matrix.toEuclideanCLM (𝕜 := ℂ) (complexify A) z =
      WithLp.toLp 2 (fun i => ((Matrix.toEuclideanCLM (𝕜 := ℝ) A x) i : ℂ)) := by
    ext i
    change (∑ j, (A i j : ℂ) * (x j : ℂ)) = ((∑ j, A i j * x j : ℝ) : ℂ)
    simp
  have hb := (Matrix.toEuclideanCLM (𝕜 := ℂ) (complexify A)).le_opNorm z
  rw [hmul, euclidean_ofReal_norm] at hb
  have hz : ‖z‖ = ‖x‖ := euclidean_ofReal_norm _
  simpa only [hz] using hb

def realVector (z : EuclideanSpace ℂ I) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun i => (z i).re)

def imaginaryVector (z : EuclideanSpace ℂ I) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun i => (z i).im)

theorem euclidean_complex_norm_sq (z : EuclideanSpace ℂ I) :
    ‖z‖ ^ 2 = ‖realVector z‖ ^ 2 + ‖imaginaryVector z‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, realVector, imaginaryVector,
    Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs,
    ← sq, Finset.sum_add_distrib]

theorem realVector_complexify_mul (A : Matrix I I ℝ) (z : EuclideanSpace ℂ I) :
    realVector (Matrix.toEuclideanCLM (𝕜 := ℂ) (complexify A) z) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A (realVector z) := by
  ext i
  change (∑ j, (A i j : ℂ) * z j).re = ∑ j, A i j * (z j).re
  simp

theorem imaginaryVector_complexify_mul (A : Matrix I I ℝ) (z : EuclideanSpace ℂ I) :
    imaginaryVector (Matrix.toEuclideanCLM (𝕜 := ℂ) (complexify A) z) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A (imaginaryVector z) := by
  ext i
  change (∑ j, (A i j : ℂ) * z j).im = ∑ j, A i j * (z j).im
  simp

/-- Complexification also cannot enlarge the L² operator norm.  Real and
imaginary input vectors are controlled separately and their squared norms
add exactly. -/
theorem complex_L2_operator_norm_le_real (A : Matrix I I ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (complexify A)‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  have hr := T.le_opNorm (realVector z)
  have hi := T.le_opNorm (imaginaryVector z)
  have hr2 := pow_le_pow_left₀ (norm_nonneg _) hr 2
  have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc
    _ = ‖T (realVector z)‖ ^ 2 + ‖T (imaginaryVector z)‖ ^ 2 := by
      rw [euclidean_complex_norm_sq, realVector_complexify_mul, imaginaryVector_complexify_mul]
    _ ≤ (‖T‖ * ‖realVector z‖) ^ 2 + (‖T‖ * ‖imaginaryVector z‖) ^ 2 := add_le_add hr2 hi2
    _ = (‖T‖ * ‖z‖) ^ 2 := by
      rw [mul_pow, mul_pow, ← mul_add, ← euclidean_complex_norm_sq, mul_pow]

/-- The real and complex L² operator norms of unchanged real coefficients
are equal, including empty index types. -/
theorem complexify_L2_operator_norm (A : Matrix I I ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (complexify A)‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ :=
  le_antisymm (complex_L2_operator_norm_le_real A) (real_L2_operator_norm_le_complex A)

end
end EndpointMatching.Fractional.Fourier
