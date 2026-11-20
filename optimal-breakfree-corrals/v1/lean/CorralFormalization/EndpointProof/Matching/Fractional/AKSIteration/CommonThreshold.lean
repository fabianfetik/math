import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.Contraction
import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.DegreeVertexRatio
/-! Choose the source-step and accumulated-error thresholds together,
before any graph is chosen. No bite-existence claim is made here. -/

open scoped Classical

namespace AKSSourceIteration
noncomputable section

def theta : ℝ := (2-Real.exp (-3))/2
def exponent : ℝ := (2:ℝ)/5

theorem theta_bounds : 0 < theta ∧ theta < 1 := by
  obtain ⟨h0,h1⟩ := AKSSourceContraction.three_uniform_alpha_bounds
  dsimp [theta]
  constructor <;> linarith

/-- One threshold simultaneously pays for the published step's domain,
the uniform contraction, and the geometric relative-error budget. -/
theorem exists_common_threshold (C Dmin : ℝ) (hC : 0 ≤ C) :
    ∃ L : ℝ, 1 ≤ L ∧ Dmin ≤ L ∧ Real.exp 1 ≤ L ∧
      (C/L^exponent)/(1-theta^exponent) ≤ 1/2 ∧
      ∀ (D Dnext N Nnext eV eD : ℝ), L ≤ D → 0 < N → 0 ≤ Nnext →
        |eV| ≤ C / D^exponent → |eD| ≤ C / D^exponent →
        Nnext ≤ (1-Real.exp (-3))*N*(1+eV) →
        Dnext*N^2 = D*Nnext^2*(1+eD) →
        0 ≤ Dnext ∧ Dnext ≤ theta*D ∧ Nnext ≤ theta*N := by
  obtain ⟨htheta0,htheta1⟩ := theta_bounds
  have ha : 0 < exponent := by norm_num [exponent]
  obtain ⟨L1,hL1,hcontract⟩ := AKSSourceContraction.three_uniform_source_step C hC
  obtain ⟨L2,hL2,hbudget⟩ :=
    AKSDegreeVertexRatio.exists_terminal_threshold theta exponent C htheta0 htheta1 ha hC
  let L : ℝ := max (max L1 L2) (max Dmin (Real.exp 1))
  have hL1L : L1 ≤ L := (le_max_left _ _).trans (le_max_left _ _)
  have hL2L : L2 ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  have hminL : Dmin ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hexpL : Real.exp 1 ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hL : 1 ≤ L := hL2.trans hL2L
  have hL2pos : 0 < L2 := lt_of_lt_of_le (by norm_num) hL2
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hp2 : 0 < L2^exponent := Real.rpow_pos_of_pos hL2pos exponent
  have hp : 0 < L^exponent := Real.rpow_pos_of_pos hLpos exponent
  have hpow : L2^exponent ≤ L^exponent := Real.rpow_le_rpow hL2pos.le hL2L ha.le
  have hfrac : C/L^exponent ≤ C/L2^exponent := by
    apply (div_le_div_iff₀ hp hp2).2
    have hh := mul_nonneg hC (sub_nonneg.mpr hpow)
    nlinarith
  have hden : 0 ≤ 1-theta^exponent := by
    have h := Real.rpow_lt_one htheta0.le htheta1 ha
    linarith
  refine ⟨L,hL,hminL,hexpL,(div_le_div_of_nonneg_right hfrac hden).trans hbudget,?_⟩
  intro D Dnext N Nnext eV eD hDL hN hNnext heV heD hvertices hdegree
  have h := hcontract D Dnext N Nnext eV eD (hL1L.trans hDL)
    hN hNnext (by simpa [exponent] using heV) (by simpa [exponent] using heD)
    hvertices hdegree
  simpa [theta] using h

end
end AKSSourceIteration
