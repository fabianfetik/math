import CorralFormalization.EndpointProof.Matching.Fractional.RoundingStep
import Mathlib.Data.Matrix.Mul

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.Rounding

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- If all coordinates outside `J` agree, the entire row error is carried by
its incidences in `J`. -/
theorem rowSum_sub_eq_sum (A : V → E → Prop) (x y : E → ℝ) (J : Finset E)
    (hfrozen : ∀ e, e ∉ J → y e = x e) (v : V) :
    rowSum A y v - rowSum A x v = ∑ e ∈ rowSupport A J v, (y e - x e) := by
  calc
    rowSum A y v - rowSum A x v =
        ∑ e, if A v e then y e - x e else 0 := by
      unfold rowSum
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    _ = ∑ e ∈ J, if A v e then y e - x e else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ J)
      intro e _ he
      simp [hfrozen e he]
    _ = ∑ e ∈ rowSupport A J v, (y e - x e) := by
      simp only [rowSupport, Finset.sum_filter]

omit [Fintype V] in
/-- A released row has at most `r` fractional incidences. Each changes by
strictly less than one, which gives the strict final error bound. -/
theorem inactive_row_error_lt (A : V → E → Prop) (x y : E → ℝ) (r : ℕ)
    (hr : 0 < r) (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (hfrozen : ∀ e, e ∉ fractional x → y e = x e) (v : V)
    (hinactive : (rowSupport A (fractional x) v).card ≤ r) :
    |rowSum A y v - rowSum A x v| < r := by
  rw [rowSum_sub_eq_sum A x y (fractional x) hfrozen]
  by_cases hnonempty : (rowSupport A (fractional x) v).Nonempty
  · calc
      |∑ e ∈ rowSupport A (fractional x) v, (y e - x e)| ≤
          ∑ e ∈ rowSupport A (fractional x) v, |y e - x e| :=
        Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _e ∈ rowSupport A (fractional x) v, (1 : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty hnonempty
        intro e he
        have hxe := (mem_fractional x e).mp ((mem_rowSupport A (fractional x) v e).mp he).1
        exact abs_lt.mpr ⟨by linarith [(hy e).1], by linarith [(hy e).2]⟩
      _ = ((rowSupport A (fractional x) v).card : ℝ) := by simp
      _ ≤ r := Nat.cast_le.mpr hinactive
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [hempty, Finset.sum_empty, abs_zero]
    exact Nat.cast_pos.mpr hr

/-- Freezing previously integral coordinates makes the fractional support
monotone under every later unit-box movement. -/
theorem fractional_subset_of_frozen (x y : E → ℝ)
    (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    (hfrozen : ∀ e, e ∉ fractional x → y e = x e) :
    fractional y ⊆ fractional x := by
  intro e he
  by_contra hn
  have hy := (mem_fractional y e).mp he
  rw [hfrozen e hn] at hy
  rcases integral_of_not_mem_fractional x hx hn with h | h <;> simp [h] at hy

/-- Bounded-error rounding for an arbitrary finite incidence relation with at
most `r` incidences per column. The positivity of `r` is essential for the
strict bound. Integral input coordinates stay fixed. -/
theorem exists_rounding (A : V → E → Prop) (r : ℕ) (hr : 0 < r)
    (hcol : ∀ e, (columnSupport A e).card ≤ r)
    (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) :
    ∃ z : E → ℝ, (∀ e, z e = 0 ∨ z e = 1) ∧
      (∀ e, e ∉ fractional x → z e = x e) ∧
      ∀ v, |rowSum A z v - rowSum A x v| < r := by
  suffices h : ∀ n : ℕ, ∀ a : E → ℝ, (fractional a).card = n →
      (∀ e, 0 ≤ a e ∧ a e ≤ 1) →
      ∃ z : E → ℝ, (∀ e, z e = 0 ∨ z e = 1) ∧
        (∀ e, e ∉ fractional a → z e = a e) ∧
        ∀ v, |rowSum A z v - rowSum A a v| < r from
    h (fractional x).card x rfl hx
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a hcard ha
    by_cases hfrac : (fractional a).Nonempty
    · obtain ⟨b, hb, hfrozen, hlt, hactive⟩ :=
        exists_rounding_step A a r hcol ha hfrac
      obtain ⟨z, hz, hzfrozen, hzerr⟩ :=
        ih (fractional b).card (by omega) b rfl hb
      have hsub := fractional_subset_of_frozen a b ha hfrozen
      have hfixed : ∀ e, e ∉ fractional a → z e = a e := by
        intro e he
        rw [hzfrozen e (fun h => he (hsub h)), hfrozen e he]
      refine ⟨z, hz, hfixed, ?_⟩
      intro v
      by_cases hv : v ∈ activeRows A (fractional a) r
      · rw [← hactive v hv]
        exact hzerr v
      · exact inactive_row_error_lt A a z r hr (by
          intro e
          rcases hz e with h | h <;> simp [h]) hfixed v
          (Nat.le_of_not_gt (by simpa only [mem_activeRows] using hv))
    · refine ⟨a, ?_, fun _ _ => rfl, ?_⟩
      · intro e
        exact integral_of_not_mem_fractional a ha (fun he => hfrac ⟨e, he⟩)
      · intro v
        simpa only [sub_self, abs_zero] using (Nat.cast_pos.mpr hr : (0 : ℝ) < r)

/-- Literal finite zero-one matrix formulation of the bounded-error rounding
lemma. There is no external rounding or matching assumption. -/
theorem exists_matrix_rounding (B : Matrix V E ℝ) (r : ℕ) (hr : 0 < r)
    (hzeroone : ∀ v e, B v e = 0 ∨ B v e = 1)
    (hcol : ∀ e, (Finset.univ.filter (fun v => B v e = 1)).card ≤ r)
    (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) :
    ∃ z : E → ℝ, (∀ e, z e = 0 ∨ z e = 1) ∧
      ∀ v, |(B.mulVec z) v - (B.mulVec x) v| < r := by
  let A : V → E → Prop := fun v e => B v e = 1
  obtain ⟨z, hz, _, herr⟩ := exists_rounding A r hr (by simpa [A, columnSupport] using hcol) x hx
  have hsum (y : E → ℝ) (v : V) : rowSum A y v = (B.mulVec y) v := by
    unfold rowSum Matrix.mulVec dotProduct
    apply Finset.sum_congr rfl
    intro e _
    rcases hzeroone v e with h | h <;> simp [A, h]
  exact ⟨z, hz, fun v => by simpa only [hsum] using herr v⟩


/-- The positive-`r` hypothesis cannot be omitted, even for a one-by-one zero
matrix and the all-zero input point. -/
theorem zero_matrix_strict_zero_rounding_impossible :
    ¬ ∃ z : Unit → ℝ, (∀ e, z e = 0 ∨ z e = 1) ∧
      ∀ v : Unit, |((0 : Matrix Unit Unit ℝ).mulVec z) v -
        ((0 : Matrix Unit Unit ℝ).mulVec (fun _ => 0)) v| < (0 : ℝ) := by
  rintro ⟨z, _, hz⟩
  exact not_lt_of_ge (abs_nonneg _) (hz ())

end
end EndpointMatching.Fractional.Rounding
