import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Original
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Finite-group Fourier eigenvectors for the exact raw convolution blocks. -/
open scoped Classical BigOperators Matrix ComplexConjugate InnerProductSpace
namespace EndpointMatching.Fractional.Fourier
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

def coefficient (f : G → ℂ) (χ : AddChar G ℂ) : ℂ :=
  ∑ g, f g * conj (χ g)

def convolutionMatrix (f : G → ℂ) : Matrix G G ℂ := fun x y => f (y-x)

def conjugateCharacter (χ : AddChar G ℂ) : G → ℂ := fun g => conj (χ g)

/-- Exact character orthogonality in the unnormalised finite sum. -/
theorem character_orthogonality (χ ψ : AddChar G ℂ) :
    (∑ x, conj (χ x) * ψ x) = if χ = ψ then (Fintype.card G : ℂ) else 0 := by
  have h := AddChar.sum_eq_ite (χ⁻¹ * ψ)
  have heq : χ⁻¹ * ψ = 0 ↔ χ = ψ := by
    change χ⁻¹ * ψ = 1 ↔ χ = ψ
    exact inv_mul_eq_one
  simp only [AddChar.mul_apply, AddChar.inv_apply, AddChar.map_neg_eq_inv, AddChar.inv_apply_eq_conj] at h
  simpa [heq] using h

/-- L²-normalised conjugate character, so every eigenvalue is exactly the
Fourier coefficient in `coefficient`. -/
def normalizedCharacter (χ : AddChar G ℂ) : EuclideanSpace ℂ G :=
  WithLp.toLp 2 (fun g => ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℝ) * conj (χ g))

theorem normalizedCharacters_orthonormal :
    Orthonormal ℂ (normalizedCharacter (G := G)) := by
  rw [orthonormal_iff_ite]
  intro χ ψ
  have hn : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : 0 < Real.sqrt (Fintype.card G : ℝ) := Real.sqrt_pos.2 hn
  have hs2 : (Real.sqrt (Fintype.card G : ℝ))^2 = Fintype.card G := Real.sq_sqrt hn.le
  have horth := character_orthogonality ψ χ
  simp only [PiLp.inner_apply, RCLike.inner_apply, normalizedCharacter,
    map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
  let a : ℂ := ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℝ)
  change (∑ x, a * conj (ψ x) * (a * χ x)) = _
  have hsum : (∑ x, a * conj (ψ x) * (a * χ x)) =
      (a*a) * ∑ x, conj (ψ x) * χ x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum,horth]
  by_cases heq : χ = ψ
  · subst ψ
    simp only [ite_true]
    have hs2c : ((Real.sqrt (Fintype.card G : ℝ) : ℂ))^2 = (Fintype.card G : ℂ) := by
      exact_mod_cast hs2
    have hsn : ((Real.sqrt (Fintype.card G : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
    dsimp [a]
    push_cast
    rw [← hs2c]
    field_simp
  · simp [heq,Ne.symm heq]

/-- The normalised characters form an orthonormal basis for every finite
abelian group, including noncyclic groups. -/
def characterONBasis : OrthonormalBasis (AddChar G ℂ) ℂ (EuclideanSpace ℂ G) :=
  (basisOfOrthonormalOfCardEqFinrank (normalizedCharacters_orthonormal (G := G))
    (by rw [finrank_euclideanSpace, AddChar.card_eq])).toOrthonormalBasis (by
      simpa using (normalizedCharacters_orthonormal (G := G)))

@[simp] theorem characterONBasis_apply (χ : AddChar G ℂ) :
    characterONBasis χ = normalizedCharacter χ := by
  simp [characterONBasis, Module.Basis.coe_toOrthonormalBasis]

/-- Every finite-group additive character is an eigenvector of a full
convolution block with precisely the raw Fourier coefficient as eigenvalue. -/
theorem convolution_character_eigen (f : G → ℂ) (χ : AddChar G ℂ) :
    (convolutionMatrix f) *ᵥ conjugateCharacter χ = coefficient f χ • conjugateCharacter χ := by
  ext x
  change (∑ y : G, f (y-x) * conj (χ y)) =
    (∑ g : G, f g * conj (χ g)) * conj (χ x)
  calc
    _ = ∑ g : G, f ((x+g)-x) * conj (χ (x+g)) := by
      symm
      apply Fintype.sum_equiv (Equiv.addLeft x)
        (fun g => f ((x+g)-x) * conj (χ (x+g)))
        (fun y => f (y-x) * conj (χ y))
      intro g
      rfl
    _ = ∑ g : G, (f g * conj (χ g)) * conj (χ x) := by
      apply Finset.sum_congr rfl
      intro g _
      simp only [add_sub_cancel_left, χ.map_add_eq_mul, map_mul]
      ring
    _ = (∑ g : G, f g * conj (χ g)) * conj (χ x) := (Finset.sum_mul ..).symm

/-- The same eigenvalue identity in the Euclidean space used by the
matrix L² operator norm. -/
theorem normalized_convolution_eigen (f : G → ℂ) (χ : AddChar G ℂ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G) (convolutionMatrix f)) (normalizedCharacter χ) =
      coefficient f χ • normalizedCharacter χ := by
  ext x
  change (∑ y : G, f (y-x) * (((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℝ) * conj (χ y))) =
    coefficient f χ * (((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℝ) * conj (χ x))
  have he := congrFun (convolution_character_eigen f χ) x
  change (∑ y : G, f (y-x) * conj (χ y)) = coefficient f χ * conj (χ x) at he
  let a : ℂ := ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℝ)
  change (∑ y : G, f (y-x) * (a * conj (χ y))) = coefficient f χ * (a * conj (χ x))
  calc
    _ = a * ∑ y : G, f (y-x) * conj (χ y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by rw [he]; ring

/-- Fourier coordinates of a convolution are multiplied by the exact
coefficient of the corresponding character. -/
theorem characterONBasis_convolution_coordinate (f : G → ℂ)
    (v : EuclideanSpace ℂ G) (χ : AddChar G ℂ) :
    (characterONBasis.repr
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G) (convolutionMatrix f) v)).ofLp χ =
        coefficient f χ * (characterONBasis.repr v).ofLp χ := by
  let b : OrthonormalBasis (AddChar G ℂ) ℂ (EuclideanSpace ℂ G) := characterONBasis
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G) (convolutionMatrix f)
  have he (ψ : AddChar G ℂ) : T (b ψ) = coefficient f ψ • b ψ := by
    simpa [T,b] using normalized_convolution_eigen f ψ
  have hTsum : T v = ∑ ψ, (b.repr v).ofLp ψ • (coefficient f ψ • b ψ) := by
    calc
      T v = T (∑ ψ, (b.repr v).ofLp ψ • b ψ) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, he]
  change (b.repr (T v)).ofLp χ = _
  rw [hTsum]
  simp only [map_sum, map_smul, b.repr_self, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [b, mul_comm]

/-- Fourier controls the genuine L² operator norm of the full convolution
block, with no cyclicity assumption and no factor depending on the group
order. -/
theorem convolution_L2_operator_norm_le (f : G → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hcoeff : ∀ χ : AddChar G ℂ, ‖coefficient f χ‖ ≤ B) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G) (convolutionMatrix f)‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro v
  let b : OrthonormalBasis (AddChar G ℂ) ℂ (EuclideanSpace ℂ G) := characterONBasis
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G) (convolutionMatrix f)
  have hsq : (∑ χ, ‖(b.repr (T v)).ofLp χ‖^2) ≤
      B^2 * ∑ χ, ‖(b.repr v).ofLp χ‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ _
    rw [characterONBasis_convolution_coordinate, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hcoeff χ) 2) (sq_nonneg _)
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq_eq_abs, abs_of_nonneg hB] at hsqrt
  simpa only [← EuclideanSpace.norm_eq, LinearIsometryEquiv.norm_map] using hsqrt

/-- Reflecting a raw mask corresponds to inversion of the character; thus
its uniform Fourier bound is unchanged, also in noncyclic abelian groups. -/
theorem coefficient_reflection (f : G → ℂ) (χ : AddChar G ℂ) :
    coefficient (fun g => f (-g)) χ = coefficient f χ⁻¹ := by
  unfold coefficient
  calc
    _ = ∑ g : G, f (-(-g)) * conj (χ (-g)) := by
      symm
      apply Fintype.sum_equiv (Equiv.neg G)
        (fun g => f (-(-g)) * conj (χ (-g)))
        (fun g => f (-g) * conj (χ g))
      intro g
      rfl
    _ = ∑ g : G, f g * conj ((χ⁻¹) g) := by
      apply Finset.sum_congr rfl
      intro g _
      simp [AddChar.map_neg_eq_inv]

end
end EndpointMatching.Fractional.Fourier
