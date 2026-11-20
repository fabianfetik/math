import CorralFormalization.EndpointProof.Factor.CommonFactorSample
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform eventual layer-size budgets -/

open Filter
namespace EndpointFactor.Allocation
open EndpointLayeredSample
noncomputable section

/-- The common sample's literal `n^(2/3)` size tolerance plus any fixed
constant is eventually at most `ε n`, with one group-independent threshold. -/
theorem explicitSizeTolerance_add_const_eventually (ε C : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, explicitSizeTolerance n + C ≤ ε * n := by
  have hlim := tendsto_rpow_neg_atTop (y := (1/3 : ℝ)) (by norm_num)
  have hevent : ∀ᶠ x : ℝ in atTop, x ^ (-(1/3 : ℝ)) < ε/2 :=
    hlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε/2))
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hevent
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max R 1) (2*C/ε))
  refine ⟨N, ?_⟩
  intro n hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : R ≤ (n : ℝ) := by
    have := le_max_left R (1 : ℝ)
    have := le_max_left (max R 1) (2*C/ε)
    linarith
  have hn1 : (1 : ℝ) ≤ n := by
    have := le_max_right R (1 : ℝ)
    have := le_max_left (max R 1) (2*C/ε)
    linarith
  have hn0 : 0 < (n : ℝ) := by linarith
  have hratio := hR (n : ℝ) hnR
  have heq : (n : ℝ)^(-(1/3 : ℝ)) = (n : ℝ)^((2 : ℝ)/3) / n := by
    have h := Real.rpow_sub hn0 ((2 : ℝ)/3) 1
    norm_num at h ⊢
    exact h
  rw [heq] at hratio
  have hsize : explicitSizeTolerance n ≤ ε/2 * n := by
    have h := (div_lt_iff₀ hn0).mp hratio
    simpa [explicitSizeTolerance] using h.le
  have hCdiv : 2*C/ε ≤ (n : ℝ) := by
    have := le_max_right (max R 1) (2*C/ε)
    linarith
  have hC : C ≤ ε/2 * n := by
    have h := (div_le_iff₀ hε).mp hCdiv
    nlinarith
  linarith

end
end EndpointFactor.Allocation
