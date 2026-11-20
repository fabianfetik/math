import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith

/-!
# Bounded-error rounding for column-sparse incidence matrices

This file develops the elementary rounding argument from `fractional-matching.md`.
The natural sparsity parameter is positive; a strict error bound is false for
`r = 0`, even for a zero matrix. No matching existence theorem is imported here.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.Rounding

noncomputable section

variable {V E : Type*} [Fintype V]

omit [Fintype V] in
/-- The incidences in row `v` among a currently floating set of columns. -/
def rowSupport (A : V → E → Prop) (J : Finset E) (v : V) : Finset E := by
  classical
  exact J.filter (A v)

/-- All incidences in a fixed column. -/
def columnSupport (A : V → E → Prop) (e : E) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => A v e)

/-- Rows with more than `r` currently floating incidences. -/
def activeRows (A : V → E → Prop) (J : Finset E) (r : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => r < (rowSupport A J v).card)

omit [Fintype V] in
@[simp] theorem mem_rowSupport (A : V → E → Prop) (J : Finset E) (v : V) (e : E) :
    e ∈ rowSupport A J v ↔ e ∈ J ∧ A v e := by
  classical
  simp [rowSupport]

@[simp] theorem mem_columnSupport (A : V → E → Prop) (v : V) (e : E) :
    v ∈ columnSupport A e ↔ A v e := by
  classical
  simp [columnSupport]

@[simp] theorem mem_activeRows (A : V → E → Prop) (J : Finset E) (r : ℕ) (v : V) :
    v ∈ activeRows A J r ↔ r < (rowSupport A J v).card := by
  classical
  simp [activeRows]

/-- Count the same restricted incidences by rows and by columns. -/
theorem sum_rowSupport_card (A : V → E → Prop) (J : Finset E) :
    (∑ v, (rowSupport A J v).card) = ∑ e ∈ J, (columnSupport A e).card := by
  classical
  simp only [rowSupport, columnSupport, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- The incidence-counting inequality underlying the floating-variable step. -/
theorem activeRows_card_bound (A : V → E → Prop) (J : Finset E) (r : ℕ)
    (hcol : ∀ e, (columnSupport A e).card ≤ r) :
    (r + 1) * (activeRows A J r).card ≤ r * J.card := by
  classical
  calc
    (r + 1) * (activeRows A J r).card =
        ∑ _v ∈ activeRows A J r, (r + 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ activeRows A J r, (rowSupport A J v).card := by
      apply Finset.sum_le_sum
      intro v hv
      exact Nat.succ_le_iff.mpr ((mem_activeRows A J r v).mp hv)
    _ ≤ ∑ v, (rowSupport A J v).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ e ∈ J, (columnSupport A e).card := sum_rowSupport_card A J
    _ ≤ ∑ _e ∈ J, r := Finset.sum_le_sum (fun e _ => hcol e)
    _ = r * J.card := by simp [Nat.mul_comm]

/-- There are strictly fewer active rows than floating columns whenever any
floating column remains. This counting fact itself also holds at `r = 0`. -/
theorem activeRows_card_lt (A : V → E → Prop) (J : Finset E) (r : ℕ)
    (hcol : ∀ e, (columnSupport A e).card ≤ r) (hJ : J.Nonempty) :
    (activeRows A J r).card < J.card := by
  have h := activeRows_card_bound A J r hcol
  have hpos := hJ.card_pos
  by_contra hn
  have hle : J.card ≤ (activeRows A J r).card := Nat.le_of_not_gt hn
  nlinarith

/-- The linear row-sum map on the floating columns, restricted to active rows. -/
def activeRowMap (A : V → E → Prop) (J : Finset E) (r : ℕ) :
    (J → ℝ) →ₗ[ℝ] (activeRows A J r → ℝ) := by
  classical
  exact
    { toFun := fun d v => ∑ e : J, if A v.1 e.1 then d e else 0
      map_add' := by
        intro d f
        ext v
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> simp
      map_smul' := by
        intro c d
        ext v
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> simp }

/-- More floating variables than active constraints give a nonzero real kernel
direction, using Mathlib's finite-dimensional rank inequality. -/
theorem exists_active_kernel_direction (A : V → E → Prop) (J : Finset E) (r : ℕ)
    (hcol : ∀ e, (columnSupport A e).card ≤ r) (hJ : J.Nonempty) :
    ∃ d : J → ℝ, d ≠ 0 ∧ ∀ v : activeRows A J r,
      (∑ e : J, if A v.1 e.1 then d e else 0) = 0 := by
  classical
  let f := activeRowMap A J r
  have hninj : ¬ Function.Injective f := by
    intro hinj
    have hdim := LinearMap.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hdim
    exact (Nat.not_le_of_gt (activeRows_card_lt A J r hcol hJ)) hdim
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro hk
    exact hninj (LinearMap.ker_eq_bot.mp hk)
  obtain ⟨d, hdmem, hd⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨d, hd, ?_⟩
  have hf : f d = 0 := LinearMap.mem_ker.mp hdmem
  intro v
  exact congrFun hf v

end
end EndpointMatching.Fractional.Rounding
