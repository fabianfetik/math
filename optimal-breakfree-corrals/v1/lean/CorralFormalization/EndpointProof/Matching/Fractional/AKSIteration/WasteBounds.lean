import Mathlib

/-!
A quantitative fragment of the deterministic iteration following the
AKS bite theorem. This file alone does not prove the complete iteration. The
per-step waste estimate and the geometric degree decrease remain explicit
hypotheses; no existence of a bite is assumed implicitly.
-/

open scoped BigOperators

namespace AKSNumericalIteration

noncomputable section

/-- A uniform geometric contraction bounds each iterate in the actual finite
sequence. The hypothesis only covers steps before `m`. -/
theorem iterate_le_geometric (d : ℕ → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (m : ℕ) (hstep : ∀ i < m, d (i+1) ≤ θ * d i) :
    d m ≤ d 0 * θ ^ m := by
  have aux : ∀ j ≤ m, d j ≤ d 0 * θ ^ j := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hjm : j < m := by omega
      have hprev := ih (by omega)
      have hs := hstep j hjm
      have hm := mul_le_mul_of_nonneg_left hprev hθ
      rw [pow_succ]
      nlinarith
  exact aux m le_rfl

/-- If the stopping degree is still at least one, geometric decay bounds
the number of steps by the logarithm of the initial degree. -/
theorem step_count_le_log (d : ℕ → ℝ) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (m : ℕ)
    (hstep : ∀ i < m, d (i+1) ≤ θ * d i) (hstop : 1 ≤ d m) :
    (m : ℝ) ≤ Real.log (d 0) / (- Real.log θ) := by
  have hgeo := iterate_le_geometric d θ hθ0.le m hstep
  have hpos0 : 0 < d 0 := by
    have hp : 0 < θ ^ m := pow_pos hθ0 _
    have : 0 < d 0 * θ ^ m := by linarith
    exact pos_of_mul_pos_left this (le_of_lt hp)
  have hprod : 1 ≤ d 0 * θ ^ m := hstop.trans hgeo
  have hlog : 0 ≤ Real.log (d 0 * θ ^ m) := Real.log_nonneg hprod
  rw [Real.log_mul (ne_of_gt hpos0) (ne_of_gt (pow_pos hθ0 _)), Real.log_pow] at hlog
  have hneg : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  apply (le_div_iff₀ (neg_pos.mpr hneg)).2
  nlinarith

/-- Once a per-round waste bound is available with the initial degree
normalization, the total waste has the expected `log D * sqrt(log D)`
shape. This proves the summation, not the source of the per-round bound. -/
theorem total_waste_le (d : ℕ → ℝ) (θ B : ℝ) (w : ℕ → ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hB : 0 ≤ B) (m : ℕ)
    (hstep : ∀ i < m, d (i+1) ≤ θ * d i) (hstop : 1 ≤ d m)
    (hw : ∀ i < m, w i ≤ B * Real.sqrt (Real.log (d 0))) :
    (∑ i ∈ Finset.range m, w i) ≤
      B * (Real.log (d 0) / (- Real.log θ)) * Real.sqrt (Real.log (d 0)) := by
  have hcount := step_count_le_log d θ hθ0 hθ1 m hstep hstop
  have hweight : 0 ≤ B * Real.sqrt (Real.log (d 0)) :=
    mul_nonneg hB (Real.sqrt_nonneg _)
  calc
    (∑ i ∈ Finset.range m, w i) ≤
        ∑ _i ∈ Finset.range m, B * Real.sqrt (Real.log (d 0)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hw i (Finset.mem_range.mp hi)
    _ = (m : ℝ) * (B * Real.sqrt (Real.log (d 0))) := by simp
    _ ≤ (Real.log (d 0) / (- Real.log θ)) *
        (B * Real.sqrt (Real.log (d 0))) := mul_le_mul_of_nonneg_right hcount hweight
    _ = B * (Real.log (d 0) / (- Real.log θ)) * Real.sqrt (Real.log (d 0)) := by ring

/-- The AKS-shaped per-round waste estimate implies the normalized bound
used in the summation, provided the separate scale ratio `N_i/√D_i ≤ B`
is supplied. `DegreeVertexRatio` derives this bound from the
source-shaped per-step relation. -/
theorem total_waste_from_local_scales (d n w : ℕ → ℝ) (θ C B : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C) (hB : 0 ≤ B) (m : ℕ)
    (hstep : ∀ i < m, d (i+1) ≤ θ * d i) (hstop : 1 ≤ d m)
    (hd : ∀ i < m, 1 ≤ d i) (hn : ∀ i < m, 0 ≤ n i)
    (hscale : ∀ i < m, n i / Real.sqrt (d i) ≤ B)
    (hw : ∀ i < m,
      w i ≤ C * (n i / Real.sqrt (d i)) * Real.sqrt (Real.log (d i))) :
    (∑ i ∈ Finset.range m, w i) ≤
      (C*B) * (Real.log (d 0) / (- Real.log θ)) * Real.sqrt (Real.log (d 0)) := by
  apply total_waste_le d θ (C*B) w hθ0 hθ1 (mul_nonneg hC hB) m hstep hstop
  intro i hi
  have hdi : 0 < d i := lt_of_lt_of_le (by norm_num) (hd i hi)
  have hgeo := iterate_le_geometric d θ hθ0.le i (fun j hj => hstep j (lt_trans hj hi))
  have h0pos : 0 < d 0 := by
    have hp := pow_pos hθ0 i
    have : 0 < d 0 * θ ^ i := lt_of_lt_of_le hdi hgeo
    exact pos_of_mul_pos_left this (le_of_lt hp)
  have hpow : θ ^ i ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
  have hdi0 : d i ≤ d 0 := by nlinarith
  have hlog : Real.log (d i) ≤ Real.log (d 0) := Real.log_le_log hdi hdi0
  have hsqrt : Real.sqrt (Real.log (d i)) ≤ Real.sqrt (Real.log (d 0)) :=
    Real.sqrt_le_sqrt hlog
  have hratio : 0 ≤ n i / Real.sqrt (d i) := div_nonneg (hn i hi) (Real.sqrt_nonneg _)
  calc
    w i ≤ C * (n i / Real.sqrt (d i)) * Real.sqrt (Real.log (d i)) := hw i hi
    _ ≤ (C * B) * Real.sqrt (Real.log (d 0)) := by
      gcongr
      exact hscale i hi

end
end AKSNumericalIteration
