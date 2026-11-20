import CorralFormalization.Results.SwitchFamily.LayoutCountAsymptotic

/-!
# Turning an asymptotic orbit count into the paper's logarithmic bound

The statement isolates a general analytic consequence. Its inputs must be
supplied by the concrete physical orbit count and its injection into the
physical census; no such physical assertion is postulated globally here.
-/

open Filter Topology
open scoped Topology

namespace CorralFormalization.Results.SwitchFamily.OrbitLogarithmic

noncomputable section

/-- A normalized asymptotic count yields the logarithmic lower bound with a
specified error tending to zero, for a height-varying bit count `m`. -/
theorem logarithmic_lower_from_asymptotic (A P m : ℕ → ℕ) {lam : ℝ}
    (hlam : 1 < lam)
    (hasym : Tendsto (fun h : ℕ => ((P h : ℝ)*h)/(lam*(2:ℝ)^(m h))^h) atTop (𝓝 1))
    (hbound : ∀ᶠ h in atTop, P h ≤ A h) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ (h : ℕ) in atTop, (h : ℝ)*(m h : ℝ) + (h : ℝ)*Real.logb 2 lam -
        Real.logb 2 (h : ℝ) - err h ≤ Real.logb 2 (A h : ℝ) := by
  let ratio : ℕ → ℝ := fun h => ((P h : ℝ)*h)/(lam*(2:ℝ)^(m h))^h
  let err : ℕ → ℝ := fun h => -Real.logb 2 (ratio h)
  refine ⟨err,?_,?_⟩
  · have ht := (Real.continuousAt_logb (b:=2) (show (1:ℝ) ≠ 0 by norm_num)).tendsto.comp hasym
    simpa [err,ratio] using ht.neg
  · have hratio : ∀ᶠ h in atTop, 0 < ratio h :=
      hasym.eventually (lt_mem_nhds (show (0:ℝ) < 1 by norm_num))
    filter_upwards [hratio,hbound,Filter.eventually_ge_atTop 1] with h hr hb hh
    have hlam0 : 0 < lam := by linarith
    have hhp : 0 < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
    have hbpos : 0 < lam*(2:ℝ)^(m h) := by positivity
    have hdpos : 0 < (lam*(2:ℝ)^(m h))^h := pow_pos hbpos _
    have hprod : 0 < (P h : ℝ)*h := (div_pos_iff_of_pos_right hdpos).mp hr
    have hP : 0 < (P h : ℝ) := pos_of_mul_pos_left hprod hhp.le
    have hPA : (P h : ℝ) ≤ A h := by exact_mod_cast hb
    have hlog := Real.logb_le_logb_of_le (b:=2) (by norm_num) hP hPA
    have hreal : Real.logb 2 (ratio h) = Real.logb 2 (P h : ℝ) + Real.logb 2 (h : ℝ) -
        (h : ℝ)*(Real.logb 2 lam + (m h : ℝ)) := by
      dsimp only [ratio]
      rw [Real.logb_div (ne_of_gt hprod) (ne_of_gt hdpos),
        Real.logb_mul (ne_of_gt hP) (ne_of_gt hhp), Real.logb_pow,
        Real.logb_mul (ne_of_gt hlam0) (ne_of_gt (by positivity : 0 < (2:ℝ)^(m h))),
        Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      ring
    dsimp only [err]
    linarith

end
end CorralFormalization.Results.SwitchFamily.OrbitLogarithmic
