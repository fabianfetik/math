import CorralFormalization.EndpointProof.Matching.Fractional.RoundingHypergraph
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Quantitative comparisons for the AKS application

These are elementary proved estimates. The matching theorem itself is kept
as an explicit premise in `RoundingAKSBridge`.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.Rounding

noncomputable section

/-- The `D^{-1/2} log^{3/2} D` rate, written using square roots. -/
def aksRate (D : ℝ) : ℝ :=
  (Real.log D * Real.sqrt (Real.log D)) / Real.sqrt D

/-- The manuscript's `D^{-1/2} log^{3/2}(eD)` rate. -/
def diffuseRate (D : ℝ) : ℝ :=
  ((1 + Real.log D) * Real.sqrt (1 + Real.log D)) / Real.sqrt D

/-- For positive `D`, the logarithm in `diffuseRate` is literally `log(eD)`. -/
theorem diffuseRate_eq_log_exp (D : ℝ) (hD : 0 < D) :
    diffuseRate D = (Real.log (Real.exp 1 * D) *
      Real.sqrt (Real.log (Real.exp 1 * D))) / Real.sqrt D := by
  rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hD), Real.log_exp]
  rfl


/-- The square-root rate is exactly the conventional fractional-power rate. -/
theorem sqrt_rate_eq_rpow (D L : ℝ) (hD : 0 < D) (hL : 0 < L) :
    (L * Real.sqrt L) / Real.sqrt D =
      D ^ (-1 / 2 : ℝ) * L ^ (3 / 2 : ℝ) := by
  have hhalf : D ^ (-1 / 2 : ℝ) = (Real.sqrt D)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hD.le, ← Real.sqrt_eq_rpow]
  have hthree : L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add hL,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hhalf, hthree]
  ring

/-- Exact notation match with the AKS remainder term. -/
theorem aksRate_eq_rpow (D : ℝ) (hD : 1 < D) :
    aksRate D = D ^ (-1 / 2 : ℝ) * (Real.log D) ^ (3 / 2 : ℝ) := by
  exact sqrt_rate_eq_rpow D (Real.log D) (by linarith) (Real.log_pos hD)

/-- Exact notation match with the manuscript's `D^{-1/2} log^{3/2}(eD)`. -/
theorem diffuseRate_eq_rpow (D : ℝ) (hD : 1 ≤ D) :
    diffuseRate D = D ^ (-1 / 2 : ℝ) *
      (Real.log (Real.exp 1 * D)) ^ (3 / 2 : ℝ) := by
  have hDpos : 0 < D := by linarith
  rw [diffuseRate_eq_log_exp D hDpos]
  apply sqrt_rate_eq_rpow D (Real.log (Real.exp 1 * D)) hDpos
  rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hDpos), Real.log_exp]
  linarith [Real.log_nonneg hD]

/-- Passing from the rounded degree parameter `D + 3` to the original `D`
loses no multiplicative constant once `D ≥ 3`. -/
theorem aksRate_add_three_le_diffuseRate (D : ℝ) (hD : 3 ≤ D) :
    aksRate (D + 3) ≤ diffuseRate D := by
  have hDpos : 0 < D := by linarith
  have hshiftpos : 0 < D + 3 := by linarith
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hshift : D + 3 ≤ Real.exp 1 * D := by
    calc
      D + 3 ≤ 2 * D := by linarith
      _ ≤ Real.exp 1 * D := mul_le_mul_of_nonneg_right he hDpos.le
  have hlog : Real.log (D + 3) ≤ 1 + Real.log D := by
    calc
      Real.log (D + 3) ≤ Real.log (Real.exp 1 * D) := Real.log_le_log hshiftpos hshift
      _ = 1 + Real.log D := by
        rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hDpos), Real.log_exp]
  have hlognonneg : 0 ≤ Real.log (D + 3) := Real.log_nonneg (by linarith)
  have hregularnonneg : 0 ≤ 1 + Real.log D := le_trans hlognonneg hlog
  have hnum : Real.log (D + 3) * Real.sqrt (Real.log (D + 3)) ≤
      (1 + Real.log D) * Real.sqrt (1 + Real.log D) :=
    mul_le_mul hlog (Real.sqrt_le_sqrt hlog) (Real.sqrt_nonneg _) hregularnonneg
  unfold aksRate diffuseRate
  calc
    _ ≤ ((1 + Real.log D) * Real.sqrt (1 + Real.log D)) / Real.sqrt (D + 3) :=
      div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left
      (mul_nonneg hregularnonneg (Real.sqrt_nonneg _))
      (Real.sqrt_pos.mpr hDpos) (Real.sqrt_le_sqrt (by linarith))

/-- An explicit sufficient domain for the six-unit rounded degree window to
fit inside the near-regular AKS window. -/
theorem six_le_aks_window (K D : ℝ) (hK : 0 < K)
    (hexp : Real.exp 1 ≤ D) (hsquare : (6 / K) ^ 2 ≤ D) :
    6 ≤ K * Real.sqrt D * Real.sqrt (Real.log D) := by
  have hsqrtD : 6 / K ≤ Real.sqrt D := by
    calc
      6 / K = Real.sqrt ((6 / K) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt D := Real.sqrt_le_sqrt hsquare
  have hlog : 1 ≤ Real.log D := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log D := Real.log_le_log (Real.exp_pos 1) hexp
  have hsqrtlog : 1 ≤ Real.sqrt (Real.log D) := Real.one_le_sqrt.mpr hlog
  have hbase : 6 ≤ K * Real.sqrt D := by
    calc
      6 = K * (6 / K) := by field_simp
      _ ≤ K * Real.sqrt D := mul_le_mul_of_nonneg_left hsqrtD hK.le
  calc
    6 ≤ K * Real.sqrt D := hbase
    _ = (K * Real.sqrt D) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsqrtlog (by positivity)

/-- A natural threshold depending only on the external constants makes all
AKS degree hypotheses and the elementary rate comparison available. -/
theorem exists_aks_rounding_threshold (K D₀ : ℝ) (hK : 0 < K) :
    ∃ Dstar : ℕ, 3 ≤ Dstar ∧ ∀ D : ℕ, Dstar ≤ D →
      D₀ ≤ (D : ℝ) + 3 ∧ Real.exp 1 ≤ (D : ℝ) + 3 ∧
      6 ≤ K * Real.sqrt ((D : ℝ) + 3) * Real.sqrt (Real.log ((D : ℝ) + 3)) := by
  let T : ℝ := max 3 (max D₀ (max (Real.exp 1) ((6 / K) ^ 2)))
  obtain ⟨n, hn⟩ := exists_nat_gt T
  have h3 : (3 : ℝ) ≤ n := (le_max_left _ _).trans hn.le
  have hD₀ : D₀ ≤ (n : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn.le
  have he : Real.exp 1 ≤ (n : ℝ) :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hn.le
  have hs : (6 / K) ^ 2 ≤ (n : ℝ) :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hn.le
  refine ⟨n, by exact_mod_cast h3, ?_⟩
  intro D hD
  have hnD : (n : ℝ) ≤ D := Nat.cast_le.mpr hD
  refine ⟨by linarith, by linarith, ?_⟩
  exact six_le_aks_window K ((D : ℝ) + 3) hK (by linarith) (by linarith)

end
end EndpointMatching.Fractional.Rounding
