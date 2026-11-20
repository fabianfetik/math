import CorralFormalization.Results.SwitchFamily.Prefix.Colors

namespace CorralFormalization.Results.SwitchFamily.Prefix

open CorralFormalization.LatinCompletion.TerraceCompletion

/-- The literal floor parameter fits in the printed square-root budget. -/
theorem count_bound {n : ℕ} (hn : 64 ≤ n) : 5*count n+8 ≤ Nat.sqrt n := by
  have hs : 8 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hd := Nat.div_mul_le_self (Nat.sqrt n-8) 5
  dsimp [count]
  omega

theorem count_square_bound {n : ℕ} (hn : 64 ≤ n) : (5*count n+8)^2 ≤ n :=
  (Nat.pow_le_pow_left (count_bound hn) 2).trans (Nat.sqrt_le' n)

theorem count_real_sqrt_bound {n : ℕ} (hn : 64 ≤ n) :
    ((5*count n+8 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hh : ((5*count n+8 : ℕ) : ℝ) ≤ (Nat.sqrt n : ℝ) := by
    exact_mod_cast count_bound hn
  exact hh.trans Real.nat_sqrt_le_real_sqrt

/-- A positive tolerance dominates the square-root path budget eventually,
without replacing that tolerance by a newly selected witness. -/
theorem sqrt_budget_eventually {ε0 : ℝ} (hε0 : 0 < ε0) :
    ∃ N : ℕ, 65 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      Real.sqrt (n : ℝ) ≤ ε0*(n : ℝ) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ((1/ε0)^2)
  refine ⟨max 65 N, le_max_left _ _, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_right 65 N) hn
  have hsq : (1/ε0)^2 ≤ (n : ℝ) := hN.trans hNn
  have hr : 1/ε0 ≤ Real.sqrt (n : ℝ) :=
    Real.le_sqrt_of_sq_le hsq
  have hprod : (1 : ℝ) ≤ ε0*Real.sqrt (n : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hε0).mp hr
  have hmul := mul_le_mul_of_nonneg_right hprod (Real.sqrt_nonneg (n : ℝ))
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]

theorem path_budget_eventually {ε0 : ℝ} (hε0 : 0 < ε0) :
    ∃ N : ℕ, 65 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ((vertices n (count n)).length-1 : ℕ) ≤ Nat.sqrt n ∧
      (((vertices n (count n)).length-1 : ℕ) : ℝ) ≤ ε0*(n : ℝ) := by
  obtain ⟨N,hN,hbudget⟩ := sqrt_budget_eventually hε0
  refine ⟨N,hN,?_⟩
  intro n hn
  have hn64 : 64 ≤ n := by omega
  have hnat : (vertices n (count n)).length-1 ≤ Nat.sqrt n := by
    rw [vertices_length]
    have := count_bound hn64
    omega
  refine ⟨hnat,?_⟩
  have hreal : (((vertices n (count n)).length-1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hcast : (((vertices n (count n)).length-1 : ℕ) : ℝ) ≤ (Nat.sqrt n : ℝ) := by
      exact_mod_cast hnat
    exact hcast.trans Real.nat_sqrt_le_real_sqrt
  exact hreal.trans (hbudget n hn)

end CorralFormalization.Results.SwitchFamily.Prefix
