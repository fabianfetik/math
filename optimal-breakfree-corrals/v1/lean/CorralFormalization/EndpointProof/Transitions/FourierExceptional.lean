import CorralFormalization.EndpointProof.Matching.Fractional.Fourier.Convolution
import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Adaptive

/-!
# The deterministic Fourier step of the ordinary transition lemma

The set `U` is arbitrary, including a set chosen after every raw role has
been observed.  No independence of roles is used in this file.
-/

open scoped Classical BigOperators ComplexConjugate Matrix

namespace EndpointTransitions

noncomputable section

open EndpointMatching.Fractional.Fourier
open EndpointFractionalRawEvent

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The literal unnormalised Fourier hypothesis for one arbitrary raw set. -/
def FourierGood (R : Finset G) (a η : ℝ) : Prop :=
  ∀ χ : AddChar G ℂ,
    ‖coefficient (fun g => ((setBit R g - a : ℝ) : ℂ)) χ‖ ≤
      η ^ 2 * (Fintype.card G : ℝ)

/-- Number of ordered pairs with sum `x`. -/
def pairCount (R U : Finset G) (x : G) : ℝ :=
  ∑ y, setBit R (x - y) * setBit U y

/-- The centred mixed convolution, with the convention of the manuscript. -/
def mixedError (R U : Finset G) (a : ℝ) (x : G) : ℝ :=
  pairCount R U x - a * (U.card : ℝ)

theorem sum_setBit (U : Finset G) : ∑ y, setBit U y = (U.card : ℝ) := by
  simp [setBit]

theorem mixedError_eq_sum (R U : Finset G) (a : ℝ) (x : G) :
    mixedError R U a x = ∑ y, (setBit R (x-y)-a)*setBit U y := by
  simp only [mixedError, pairCount, sub_mul, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, sum_setBit]

/-- The trivial character gives the required raw cardinality accuracy. -/
theorem FourierGood.rawSize {R : Finset G} {a η : ℝ} (h : FourierGood R a η) :
    |(R.card : ℝ)-a*(Fintype.card G : ℝ)| ≤ η^2*(Fintype.card G : ℝ) := by
  have hre : (coefficient (fun g => ((setBit R g-a : ℝ) : ℂ)) 0).re =
      (R.card : ℝ)-a*(Fintype.card G : ℝ) := by
    simp [coefficient, Finset.sum_sub_distrib, sum_setBit, mul_comm]
  rw [← hre]
  exact (Complex.abs_re_le_norm _).trans (h 0)

/-- Parseval/operator-norm form of J5, with the sharper factor `|U|`.
This is valid for every realised `U`, without a probability premise. -/
theorem FourierGood.mixed_l2 {R : Finset G} {a η : ℝ} (h : FourierGood R a η)
    (U : Finset G) :
    (∑ x, mixedError R U a x ^ 2) ≤
      η ^ 4 * (Fintype.card G : ℝ) ^ 2 * (U.card : ℝ) := by
  let f : G → ℂ := fun g => ((setBit R (-g)-a : ℝ) : ℂ)
  let u : EuclideanSpace ℂ G := WithLp.toLp 2 (fun g => (setBit U g : ℂ))
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G) (convolutionMatrix f)
  have hf : ∀ χ, ‖coefficient f χ‖ ≤ η^2*(Fintype.card G : ℝ) := by
    intro χ
    have hc := coefficient_reflection (fun g => ((setBit R g-a : ℝ) : ℂ)) χ
    change coefficient f χ = _ at hc
    rw [hc]
    exact h χ⁻¹
  have hT := convolution_L2_operator_norm_le f
    (η^2*(Fintype.card G : ℝ)) (by positivity) hf
  have hTu : ‖T u‖ ≤ (η^2*(Fintype.card G : ℝ))*‖u‖ :=
    (T.le_opNorm u).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have hnormu : ‖u‖^2 = (U.card : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [u, setBit]
  have hcoord (x : G) : (T u) x = (mixedError R U a x : ℂ) := by
    rw [mixedError_eq_sum]
    change (∑ y, ((setBit R (-(y-x))-a : ℝ) : ℂ) * (setBit U y : ℂ)) = _
    simp only [neg_sub]
    push_cast
    rfl
  have hnormT : ‖T u‖^2 = ∑ x, mixedError R U a x ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hcoord, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hs := pow_le_pow_left₀ (norm_nonneg (T u)) hTu 2
  rw [mul_pow, mul_pow, hnormu, hnormT] at hs
  simpa only [← pow_mul, show 2*2=4 from rfl] using hs

theorem FourierGood.mixed_l2_group {R : Finset G} {a η : ℝ}
    (h : FourierGood R a η) (U : Finset G) :
    (∑ x, mixedError R U a x ^ 2) ≤ η^4*(Fintype.card G : ℝ)^3 := by
  apply (h.mixed_l2 U).trans
  have hc : (U.card : ℝ) ≤ Fintype.card G := by exact_mod_cast Finset.card_le_univ U
  calc
    η^4*(Fintype.card G : ℝ)^2*(U.card : ℝ) ≤
      η^4*(Fintype.card G : ℝ)^2*(Fintype.card G : ℝ) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

/-- Numerical labels where the mixed convolution has error greater than `ηn`. -/
def exceptional (R U : Finset G) (a η : ℝ) : Finset G :=
  Finset.univ.filter (fun x => η*(Fintype.card G : ℝ) < |mixedError R U a x|)

/-- Chebyshev counting pays at most `η² n` exceptional labels, for each
arbitrary later partner set. -/
theorem FourierGood.exceptional_card {R : Finset G} {a η : ℝ}
    (h : FourierGood R a η) (hη : 0 < η) (U : Finset G) :
    ((exceptional R U a η).card : ℝ) ≤ η^2*(Fintype.card G : ℝ) := by
  have hn : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hthreshold : 0 < η*(Fintype.card G : ℝ) := mul_pos hη hn
  have hsum : ((exceptional R U a η).card : ℝ) *
      (η*(Fintype.card G : ℝ))^2 ≤ ∑ x, mixedError R U a x ^ 2 := by
    calc
      _ = ∑ x ∈ exceptional R U a η, (η*(Fintype.card G : ℝ))^2 := by simp
      _ ≤ ∑ x ∈ exceptional R U a η, mixedError R U a x ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        have he := (Finset.mem_filter.mp hx).2
        have hs := pow_le_pow_left₀ hthreshold.le he.le 2
        simpa only [sq_abs] using hs
      _ ≤ ∑ x, mixedError R U a x ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun x => sq_nonneg _)
  have hall := h.mixed_l2_group U
  have hmul : ((exceptional R U a η).card : ℝ)*(η*(Fintype.card G : ℝ))^2 ≤
      (η^2*(Fintype.card G : ℝ))*(η*(Fintype.card G : ℝ))^2 := by
    calc
      _ ≤ η^4*(Fintype.card G : ℝ)^3 := hsum.trans hall
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hthreshold)).mp hmul

theorem mixedError_le_of_not_exceptional (R U : Finset G) (a η : ℝ) (x : G)
    (hx : x ∉ exceptional R U a η) :
    |mixedError R U a x| ≤ η*(Fintype.card G : ℝ) := by
  simpa only [exceptional, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hx

end
end EndpointTransitions
