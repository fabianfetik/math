import CorralFormalization.EndpointProof.Matching.Fractional.Rounding
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.Rounding

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The coordinates still in the open unit interval. -/
def fractional (x : E → ℝ) : Finset E :=
  Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)

@[simp] theorem mem_fractional (x : E → ℝ) (e : E) :
    e ∈ fractional x ↔ 0 < x e ∧ x e < 1 := by
  simp [fractional]

/-- Sum of the selected coordinates at an actual row of the incidence matrix. -/
def rowSum (A : V → E → Prop) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e, if A v e then x e else 0

/-- Coordinates outside the fractional support of a unit-box point are integral. -/
theorem integral_of_not_mem_fractional (x : E → ℝ)
    (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) {e : E} (he : e ∉ fractional x) :
    x e = 0 ∨ x e = 1 := by
  simp only [mem_fractional, not_and_or, not_lt] at he
  rcases he with h | h
  · exact Or.inl (le_antisymm h (hx e).1)
  · exact Or.inr (le_antisymm (hx e).2 h)

/-- First positive time at which a nonzero coordinate of `d` meets a box face. -/
def boundaryTime (x d : E → ℝ) (e : E) : ℝ :=
  if 0 < d e then (1 - x e) / d e else -x e / d e

/-- A nonzero direction supported on fractional coordinates has a positive
first boundary time. No coordinate leaves the unit interval at that time. -/
theorem exists_box_boundary (x d : E → ℝ)
    (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (hd : d ≠ 0)
    (hsupp : ∀ e, d e ≠ 0 → 0 < x e ∧ x e < 1) :
    ∃ t : ℝ, 0 < t ∧
      (∀ e, 0 ≤ x e + t * d e ∧ x e + t * d e ≤ 1) ∧
      ∃ e, d e ≠ 0 ∧ (x e + t * d e = 0 ∨ x e + t * d e = 1) := by
  let S := Finset.univ.filter (fun e => d e ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨e, he⟩ : ∃ e, d e ≠ 0 := Function.ne_iff.mp hd
    exact ⟨e, by simpa [S] using he⟩
  obtain ⟨e₀, he₀, hmin⟩ := S.exists_min_image (boundaryTime x d) hS
  have hd₀ : d e₀ ≠ 0 := (Finset.mem_filter.mp he₀).2
  have htpos : 0 < boundaryTime x d e₀ := by
    unfold boundaryTime
    split_ifs with hpos
    · exact div_pos (sub_pos.mpr (hsupp e₀ hd₀).2) hpos
    · exact div_pos_of_neg_of_neg (neg_neg_of_pos (hsupp e₀ hd₀).1)
        (lt_of_le_of_ne (le_of_not_gt hpos) hd₀)
  refine ⟨boundaryTime x d e₀, htpos, ?_, e₀, hd₀, ?_⟩
  · intro e
    by_cases hde : d e = 0
    · simpa [hde] using hx e
    have hle := hmin e (by simpa [S] using hde)
    by_cases hpos : 0 < d e
    · have ht : boundaryTime x d e₀ * d e ≤ 1 - x e := by
        exact (le_div_iff₀ hpos).mp (by simpa [boundaryTime, hpos] using hle)
      constructor
      · exact add_nonneg (hx e).1 (le_of_lt (mul_pos htpos hpos))
      · linarith
    · have hneg : d e < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hde
      have ht : -x e ≤ boundaryTime x d e₀ * d e := by
        exact (le_div_iff_of_neg hneg).mp (by simpa [boundaryTime, hpos] using hle)
      constructor
      · linarith
      · have hmul : boundaryTime x d e₀ * d e ≤ 0 := le_of_lt (mul_neg_of_pos_of_neg htpos hneg)
        linarith [(hx e).2]
  · unfold boundaryTime
    split_ifs with hpos
    · right
      field_simp; ring
    · left
      field_simp; ring


/-- Extend the active-row kernel direction by zero outside `J`. -/
theorem exists_supported_active_direction (A : V → E → Prop) (J : Finset E) (r : ℕ)
    (hcol : ∀ e, (columnSupport A e).card ≤ r) (hJ : J.Nonempty) :
    ∃ d : E → ℝ, d ≠ 0 ∧ (∀ e, e ∉ J → d e = 0) ∧
      ∀ v ∈ activeRows A J r, rowSum A d v = 0 := by
  obtain ⟨d, hd, hsum⟩ := exists_active_kernel_direction A J r hcol hJ
  let d' : E → ℝ := fun e => if h : e ∈ J then d ⟨e, h⟩ else 0
  have hne : d' ≠ 0 := by
    obtain ⟨e, he⟩ : ∃ e, d e ≠ 0 := Function.ne_iff.mp hd
    intro hzero
    have := congrFun hzero e.1
    exact he (by simpa [d', e.2] using this)
  refine ⟨d', hne, ?_, ?_⟩
  · intro e he
    simp [d', he]
  · intro v hv
    calc
      rowSum A d' v = ∑ e ∈ J, if A v e then d' e else 0 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ J)
        intro e _ he
        simp [d', he]
      _ = ∑ e : J, if A v e.1 then d e else 0 := by
        rw [← Finset.sum_coe_sort]
        apply Finset.sum_congr rfl
        intro e _
        simp [d', e.2]
      _ = 0 := hsum ⟨v, hv⟩

/-- One floating-variable step freezes at least one new coordinate, preserves
all currently active row sums, and never unfreezes an integral coordinate. -/
theorem exists_rounding_step (A : V → E → Prop) (x : E → ℝ) (r : ℕ)
    (hcol : ∀ e, (columnSupport A e).card ≤ r)
    (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (hfrac : (fractional x).Nonempty) :
    ∃ y : E → ℝ, (∀ e, 0 ≤ y e ∧ y e ≤ 1) ∧
      (∀ e, e ∉ fractional x → y e = x e) ∧
      (fractional y).card < (fractional x).card ∧
      ∀ v ∈ activeRows A (fractional x) r, rowSum A y v = rowSum A x v := by
  obtain ⟨d, hd, hsupp, hsum⟩ :=
    exists_supported_active_direction A (fractional x) r hcol hfrac
  have hdfrac : ∀ e, d e ≠ 0 → 0 < x e ∧ x e < 1 := by
    intro e he
    by_contra hn
    exact he (hsupp e (by simpa only [mem_fractional] using hn))
  obtain ⟨t, ht, hybox, e₀, hd₀, he₀⟩ := exists_box_boundary x d hx hd hdfrac
  let y : E → ℝ := fun e => x e + t * d e
  have hfrozen : ∀ e, e ∉ fractional x → y e = x e := by
    intro e he
    simp [y, hsupp e he]
  have hsub : fractional y ⊆ fractional x := by
    intro e he
    by_contra hn
    have hy := (mem_fractional y e).mp he
    rw [hfrozen e hn] at hy
    rcases integral_of_not_mem_fractional x hx hn with h | h <;> simp [h] at hy
  have he₀x : e₀ ∈ fractional x := (mem_fractional x e₀).mpr (hdfrac e₀ hd₀)
  have he₀y : e₀ ∉ fractional y := by
    simp only [mem_fractional]
    change ¬ (0 < x e₀ + t * d e₀ ∧ x e₀ + t * d e₀ < 1)
    rcases he₀ with h | h <;> simp [h]
  refine ⟨y, hybox, hfrozen, ?_, ?_⟩
  · exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub, fun heq => he₀y (heq.symm ▸ he₀x)⟩)
  · intro v hv
    change (∑ e, if A v e then x e + t * d e else 0) = rowSum A x v
    have heq : (∑ e, if A v e then x e + t * d e else 0) =
        rowSum A x v + t * rowSum A d v := by
      unfold rowSum
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    rw [heq, hsum v hv, mul_zero, add_zero]

end
end EndpointMatching.Fractional.Rounding
