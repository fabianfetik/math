import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-!
# The exact product in the global upper bound

This file proves the analytic estimate of Theorem 8 for the literal finite
product. It contains no corral-counting hypothesis.
-/

namespace CorralFormalization.Results.SharpUpper

open Finset

/-- The falling-factorial correction after `j` disjoint rows. -/
noncomputable def avoidanceFactor (n j : ℕ) : ℝ :=
  ((n - j : ℕ) : ℝ) ^ j / (n.descFactorial j : ℝ)

/-- The product called `B_h` in Theorem 8. -/
noncomputable def correctionProduct (h : ℕ) : ℝ :=
  ∏ i ∈ range (h - 2), avoidanceFactor (2 * h - 1) (i + 1)

@[simp] lemma avoidanceFactor_zero (n : ℕ) : avoidanceFactor n 0 = 1 := by
  simp [avoidanceFactor]

@[simp] lemma correctionProduct_two : correctionProduct 2 = 1 := by
  norm_num [correctionProduct]

/-- Including the zeroth factor does not alter the manuscript product. -/
lemma correctionProduct_eq_prod_range (h : ℕ) (hh : 2 ≤ h) :
    correctionProduct h = ∏ j ∈ range (h-1), avoidanceFactor (2*h-1) j := by
  have he : h-1 = (h-2)+1 := by omega
  rw [he,prod_range_succ']
  simp only [avoidanceFactor_zero,mul_one]
  rfl

/-- Every falling-factorial denominator used by Theorem 8 is strictly
positive, including the empty product at height two. -/
lemma countingDenominators_positive (h : ℕ) (hh : 2 ≤ h) :
    0 < ((2*h-1 : ℕ) : ℝ) ∧ 0 < ((h*(2*h-1) : ℕ) : ℝ) ∧
      0 < (6 * ((2*h-1 : ℕ) : ℝ)) ∧
      ∀ j ≤ h-2, 0 < ((2*h-1).descFactorial j : ℝ) := by
  have hn : 0 < 2*h-1 := by omega
  have hM : 0 < h*(2*h-1) := Nat.mul_pos (by omega) hn
  refine ⟨by exact_mod_cast hn, by exact_mod_cast hM, by positivity, ?_⟩
  intro j hj
  exact_mod_cast (Nat.descFactorial_pos.mpr (show j ≤ 2*h-1 by omega))

lemma descFactorial_cast_eq_prod (n j : ℕ) :
    (n.descFactorial j : ℝ) = ∏ t ∈ range j, ((n - t : ℕ) : ℝ) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]

lemma avoidanceFactor_eq_prod (n j : ℕ) :
    avoidanceFactor n j =
      ∏ t ∈ range j, (((n - j : ℕ) : ℝ) / ((n - t : ℕ) : ℝ)) := by
  simp only [avoidanceFactor, prod_div_distrib, prod_const, card_range,
    ← descFactorial_cast_eq_prod]

lemma avoidanceFactor_nonneg (n j : ℕ) : 0 ≤ avoidanceFactor n j := by
  unfold avoidanceFactor
  positivity

/-- The exact one-step ratio is at most the exponential with denominator
`n`. This proof does not require independence of any events. -/
lemma stepRatio_le_exp {n j t : ℕ} (hjn : j < n) (htj : t < j) :
    (((n - j : ℕ) : ℝ) / ((n - t : ℕ) : ℝ)) ≤
      Real.exp (-(((j - t : ℕ) : ℝ) / (n : ℝ))) := by
  have hn : 0 < n := by omega
  have htn : t < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hntR : 0 < ((n - t : ℕ) : ℝ) := by exact_mod_cast (show 0 < n-t by omega)
  have hntle : ((n - t : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.sub_le n t)
  have hnum : 0 ≤ ((j - t : ℕ) : ℝ) := by positivity
  have hfrac : (((j - t : ℕ) : ℝ) / (n : ℝ)) ≤
      (((j - t : ℕ) : ℝ) / ((n - t : ℕ) : ℝ)) :=
    div_le_div_of_nonneg_left hnum hntR hntle
  have heq : (((n - j : ℕ) : ℝ) / ((n - t : ℕ) : ℝ)) =
      1 - (((j - t : ℕ) : ℝ) / ((n - t : ℕ) : ℝ)) := by
    rw [Nat.cast_sub (by omega : j ≤ n), Nat.cast_sub (by omega : t ≤ n),
      Nat.cast_sub (by omega : t ≤ j)]
    have hdenom : (n : ℝ) - t ≠ 0 := by
      rw [← Nat.cast_sub (by omega : t ≤ n)]
      exact ne_of_gt hntR
    field_simp [hdenom]
    ring
  rw [heq]
  exact (by linarith : 1 - (((j - t : ℕ) : ℝ) / ((n - t : ℕ) : ℝ)) ≤
    1 - (((j - t : ℕ) : ℝ) / (n : ℝ))).trans (Real.one_sub_le_exp_neg _)

lemma sum_reverse_range (j : ℕ) :
    (∑ t ∈ range j, ((j - t : ℕ) : ℝ)) = (j : ℝ) * ((j : ℝ) + 1) / 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ]
    have hs : (∑ t ∈ range j, ((j + 1 - t : ℕ) : ℝ)) =
        (∑ t ∈ range j, ((j - t : ℕ) : ℝ)) + (j : ℝ) := by
      calc
        _ = ∑ t ∈ range j, (((j - t : ℕ) : ℝ) + 1) := by
          apply sum_congr rfl
          intro t ht
          have htj : t ≤ j := by simpa using (mem_range.mp ht).le
          rw [show j + 1 - t = (j - t) + 1 by omega]
          push_cast
          rfl
        _ = _ := by simp [sum_add_distrib]
    rw [hs, ih]
    have hj : j + 1 - j = 1 := by omega
    rw [hj]
    push_cast
    ring

/-- The logarithmic factor estimate from Theorem 8, stated directly in
exponential form, with the same constant. -/
theorem avoidanceFactor_le_exp {n j : ℕ} (hjn : j < n) :
    avoidanceFactor n j ≤ Real.exp (-((j : ℝ) * ((j : ℝ) + 1) / (2 * n))) := by
  rw [avoidanceFactor_eq_prod]
  calc
    _ ≤ ∏ t ∈ range j, Real.exp (-(((j - t : ℕ) : ℝ) / (n : ℝ))) := by
      apply prod_le_prod
      · intro t ht
        positivity
      · intro t ht
        exact stepRatio_le_exp hjn (mem_range.mp ht)
    _ = Real.exp (∑ t ∈ range j, -(((j - t : ℕ) : ℝ) / (n : ℝ))) :=
      (Real.exp_sum _ _).symm
    _ = _ := by
      rw [sum_neg_distrib, ← sum_div, sum_reverse_range]
      congr 1
      ring

lemma avoidanceFactor_pos {n j : ℕ} (hjn : j < n) : 0 < avoidanceFactor n j := by
  unfold avoidanceFactor
  have hbase : 0 < ((n-j : ℕ) : ℝ) := by exact_mod_cast (show 0 < n-j by omega)
  have hden : 0 < (n.descFactorial j : ℝ) := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (show j ≤ n by omega))
  positivity

/-- The factor's exact logarithmic estimate stated in the manuscript. -/
theorem log_avoidanceFactor_le {n j : ℕ} (hjn : j < n) :
    Real.log (avoidanceFactor n j) ≤ -((j : ℝ) * ((j : ℝ)+1) / (2*n)) := by
  have hh := Real.log_le_log (avoidanceFactor_pos hjn) (avoidanceFactor_le_exp hjn)
  simpa only [Real.log_exp] using hh

lemma sum_triangular_range (m : ℕ) :
    (∑ i ∈ range m, ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1)) =
      (m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2) / 3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- The exact exponential bound on `B_h` displayed in Theorem 8. -/
theorem correctionProduct_le_exp (h : ℕ) (hh : 2 ≤ h) :
    correctionProduct h ≤
      Real.exp (-(((h - 2 : ℕ) : ℝ) * ((h - 1 : ℕ) : ℝ) * (h : ℝ) /
        (6 * ((2 * h - 1 : ℕ) : ℝ)))) := by
  unfold correctionProduct
  calc
    _ ≤ ∏ i ∈ range (h - 2),
        Real.exp (-(((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1) /
          (2 * ((2 * h - 1 : ℕ) : ℝ)))) := by
      apply prod_le_prod
      · intro i hi
        exact avoidanceFactor_nonneg _ _
      · intro i hi
        exact avoidanceFactor_le_exp (by have := mem_range.mp hi; omega)
    _ = Real.exp (∑ i ∈ range (h - 2),
        -(((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1) /
          (2 * ((2 * h - 1 : ℕ) : ℝ)))) := (Real.exp_sum _ _).symm
    _ = _ := by
      rw [sum_neg_distrib, ← sum_div, sum_triangular_range]
      congr 1
      have hhm1 : ((h - 2 : ℕ) : ℝ) + 1 = ((h - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hh, Nat.cast_sub (by omega : 1 ≤ h)]
        push_cast
        ring
      have hhm0 : ((h - 2 : ℕ) : ℝ) + 2 = (h : ℝ) := by
        rw [Nat.cast_sub hh]
        push_cast
        ring
      rw [hhm1, hhm0]
      ring

end CorralFormalization.Results.SharpUpper
