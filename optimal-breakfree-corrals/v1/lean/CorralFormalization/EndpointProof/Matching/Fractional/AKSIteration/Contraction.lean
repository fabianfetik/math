import Mathlib

/-!
# One-sided source-step contraction

The displayed statement of AKS Theorem 2.1 bounds the next vertex count
from above. It does not require a lower contraction bound. This file proves
the numerical consequence of that one-sided bound and the displayed
degree/vertex relation, without assuming the resulting degree contraction.
It does not prove that a hypergraph bite exists.
-/

open Filter

namespace AKSSourceContraction
noncomputable section

/-- A single source-shaped step contracts degree by a fixed factor derived
from the source's one-sided vertex bound and its two-sided relative error.
The next degree and vertex count may be zero. -/
theorem one_sided_step
    (α η D Dnext N Nnext eV eD : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (_hη0 : 0 ≤ η) (hη : η ≤ (1-α)/4)
    (hD : 0 < D) (hN : 0 < N) (hNnext : 0 ≤ Nnext)
    (heV : |eV| ≤ η) (heD : |eD| ≤ η)
    (hvertices : Nnext ≤ α * N * (1+eV))
    (hdegree : Dnext * N^2 = D * Nnext^2 * (1+eD)) :
    0 ≤ Dnext ∧ Dnext ≤ ((1+α)/2) * D ∧ Nnext ≤ ((1+α)/2) * N := by
  let β : ℝ := (1+α)/2
  have hβ0 : 0 < β := by dsimp [β]; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  have hv : eV ≤ η := (abs_le.mp heV).2
  have hdlo : -η ≤ eD := (abs_le.mp heD).1
  have hdhi : eD ≤ η := (abs_le.mp heD).2
  have hDfactor : 0 ≤ 1+eD := by linarith
  have hαη : α * (1+η) ≤ β := by
    have h := mul_nonneg (le_of_lt hα0) (sub_nonneg.mpr hα1.le)
    dsimp [β]
    nlinarith
  have hβη : β * (1+η) ≤ 1 := by
    have h := mul_nonneg (sub_nonneg.mpr hα1.le) (show 0 ≤ 3-α by linarith)
    have ht := mul_le_mul_of_nonneg_left hη (le_of_lt hβ0)
    dsimp [β] at *
    nlinarith
  have hvertex : Nnext ≤ β*N := by
    calc
      Nnext ≤ α*N*(1+eV) := hvertices
      _ ≤ α*N*(1+η) := by gcongr
      _ = (α*(1+η))*N := by ring
      _ ≤ β*N := mul_le_mul_of_nonneg_right hαη hN.le
  have hsq : Nnext^2 ≤ (β*N)^2 :=
    (sq_le_sq₀ hNnext (mul_nonneg hβ0.le hN.le)).2 hvertex
  have hdegprod : 0 ≤ Dnext*N^2 := by
    rw [hdegree]
    positivity
  have hN2 : 0 < N^2 := sq_pos_of_pos hN
  have hdeg0 : 0 ≤ Dnext := by
    by_contra h
    have hn : Dnext < 0 := lt_of_not_ge h
    have hneg : Dnext*N^2 < 0 := mul_neg_of_neg_of_pos hn hN2
    linarith
  have hβsquare : β^2*(1+η) ≤ β := by
    have h := mul_le_mul_of_nonneg_left hβη hβ0.le
    nlinarith
  have hupper : Dnext*N^2 ≤ (β*D)*N^2 := by
    calc
      Dnext*N^2 = D*Nnext^2*(1+eD) := hdegree
      _ ≤ D*(β*N)^2*(1+eD) := by gcongr
      _ ≤ D*(β*N)^2*(1+η) := by gcongr
      _ = (D*N^2)*(β^2*(1+η)) := by ring
      _ ≤ (D*N^2)*β := mul_le_mul_of_nonneg_left hβsquare (by positivity)
      _ = (β*D)*N^2 := by ring
  refine ⟨hdeg0, ?_, ?_⟩
  · change Dnext ≤ β*D
    exact le_of_mul_le_mul_right hupper hN2
  · exact hvertex

/-- For a fixed positive error exponent and source constant, choose one
threshold before the hypergraph and all later steps. Above it, the two
source-shaped relative errors imply the fixed degree contraction. -/
theorem exists_uniform_step_threshold (α a C : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (ha : 0 < a) (_hC : 0 ≤ C) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ (D Dnext N Nnext eV eD : ℝ), L ≤ D → 0 < N → 0 ≤ Nnext →
        |eV| ≤ C / D^a → |eD| ≤ C / D^a →
        Nnext ≤ α*N*(1+eV) →
        Dnext*N^2 = D*Nnext^2*(1+eD) →
        0 ≤ Dnext ∧ Dnext ≤ ((1+α)/2)*D ∧ Nnext ≤ ((1+α)/2)*N := by
  let η : ℝ := (1-α)/4
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨x,hx⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop ha)) (C/η)
  let L : ℝ := max x 1
  have hL : 1 ≤ L := le_max_right _ _
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLpow : 0 < L^a := Real.rpow_pos_of_pos hLpos a
  have hlarge : C/η ≤ L^a := hx L (le_max_left _ _)
  have hboundL : C / L^a ≤ η := by
    apply (div_le_iff₀ hLpow).2
    have := (div_le_iff₀ hη).1 hlarge
    nlinarith
  refine ⟨L,hL,?_⟩
  intro D Dnext N Nnext eV eD hDL hN hNnext heV heD hvertices hdegree
  have hD : 0 < D := lt_of_lt_of_le hLpos hDL
  have hDpow : 0 < D^a := Real.rpow_pos_of_pos hD a
  have hpower : L^a ≤ D^a := Real.rpow_le_rpow hLpos.le hDL ha.le
  have hbound : C / D^a ≤ η := by
    apply (div_le_iff₀ hDpow).2
    have h := (div_le_iff₀ hLpow).1 hboundL
    have hp := mul_le_mul_of_nonneg_left hpower hη.le
    nlinarith
  exact one_sided_step α η D Dnext N Nnext eV eD hα0 hα1 hη.le
    (by dsimp [η]; exact le_rfl) hD hN hNnext (heV.trans hbound) (heD.trans hbound)
    hvertices hdegree

/-- The numerical source constant for 3-uniform hypergraphs lies in (0,1). -/
theorem three_uniform_alpha_bounds :
    0 < 1 - Real.exp (-3) ∧ 1 - Real.exp (-3) < 1 := by
  have hpositive : 0 < Real.exp (-3) := Real.exp_pos _
  have hsmall : Real.exp (-3) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  constructor <;> linarith

/-- Explicit three-uniform source specialization; the two error bounds are
those furnished by unpacking the source's `O(D^(-2/5))` at one step. -/
theorem three_uniform_source_step (C : ℝ) (hC : 0 ≤ C) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ (D Dnext N Nnext eV eD : ℝ), L ≤ D → 0 < N → 0 ≤ Nnext →
        |eV| ≤ C / D^((2:ℝ)/5) → |eD| ≤ C / D^((2:ℝ)/5) →
        Nnext ≤ (1-Real.exp (-3))*N*(1+eV) →
        Dnext*N^2 = D*Nnext^2*(1+eD) →
        0 ≤ Dnext ∧ Dnext ≤ ((2-Real.exp (-3))/2)*D ∧
          Nnext ≤ ((2-Real.exp (-3))/2)*N := by
  obtain ⟨h0,h1⟩ := three_uniform_alpha_bounds
  obtain ⟨L,hL,h⟩ := exists_uniform_step_threshold
    (1-Real.exp (-3)) ((2:ℝ)/5) C h0 h1 (by norm_num) hC
  refine ⟨L,hL,?_⟩
  intro D Dnext N Nnext eV eD hDL hN hNnext heV heD hvertices hdegree
  have hr := h D Dnext N Nnext eV eD hDL hN hNnext heV heD hvertices hdegree
  refine ⟨hr.1, ?_, ?_⟩
  · convert hr.2.1 using 1
    ring
  · convert hr.2.2 using 1
    ring

end
end AKSSourceContraction
