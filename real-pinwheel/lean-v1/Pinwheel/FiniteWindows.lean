import Pinwheel.Rates
import Mathlib.Order.Interval.Set.OrdConnectedComponent
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Combinatorics.Compactness

/-! Finite collections of the original service-window demands. -/

namespace RealPinwheel

open Finset
open scoped BigOperators

abbrev WindowFamily (α : Type*) := α → Finset (Finset ℤ)

def IsWindow (W : Finset ℤ) : Prop := Set.OrdConnected (W : Set ℤ)

def WindowFamily.Proper {α : Type*} (F : WindowFamily α) : Prop :=
  ∀ i, ∀ W ∈ F i, W.Nonempty ∧ IsWindow W

noncomputable def finiteService {α : Type*} (S : ℤ → α) (i : α) (W : Finset ℤ) : ℕ := by
  classical
  exact (W.filter fun t => S t = i).card

theorem finiteService_eq_filter {α : Type*} (S : ℤ → α) (i : α) (W : Finset ℤ)
    [DecidablePred (fun t => S t = i)] :
    finiteService S i W = (W.filter fun t => S t = i).card := by
  unfold finiteService
  congr 1
  exact Finset.filter_congr_decidable _ _ _

def FiniteValid {α : Type*} (F : WindowFamily α) (r : α → ℝ) (S : ℤ → α) : Prop :=
  ∀ i, ∀ W ∈ F i, ⌊(W.card : ℝ) * r i⌋₊ ≤ finiteService S i W

def FiniteFeasible {α : Type*} (F : WindowFamily α) (r : α → ℝ) : Prop :=
  ∃ S : ℤ → α, FiniteValid F r S

theorem isWindow_Ico (m : ℤ) (L : ℕ) : IsWindow (Ico m (m + L)) := by
  simpa only [IsWindow, coe_Ico] using
    (inferInstance : Set.OrdConnected (Set.Ico m (m + L)))

theorem IsWindow.eq_Ico {W : Finset ℤ} (h : IsWindow W) (hne : W.Nonempty) :
    ∃ m : ℤ, W = Ico m (m + (W.card : ℤ)) := by
  let a := W.min' hne
  let b := W.max' hne
  have hab : a ≤ b := Finset.min'_le W _ (Finset.max'_mem W hne)
  have he : W = Ico a (b + 1) := by
    ext t
    simp only [mem_Ico]
    constructor
    · intro ht
      have ha := Finset.min'_le W t ht
      have hb := Finset.le_max' W t ht
      change a ≤ t ∧ t < b + 1
      omega
    · intro ht
      have ht' : t ∈ Set.Icc a b := ⟨ht.1, by omega⟩
      exact h.out (Finset.min'_mem W hne) (Finset.max'_mem W hne) ht'
  have hc : (W.card : ℤ) = b + 1 - a := by
    rw [he, Int.card_Ico]
    exact Int.toNat_of_nonneg (by omega)
  refine ⟨a, ?_⟩
  have heq : a + (W.card : ℤ) = b + 1 := by omega
  rwa [heq]

theorem ValidRates.windowDemand {α : Type*} {r : α → ℝ} {S : ℤ → α}
    (hS : ValidRates r S) (i : α) {W : Finset ℤ} (hW : IsWindow W)
    (hne : W.Nonempty) : ⌊(W.card : ℝ) * r i⌋₊ ≤ finiteService S i W := by
  classical
  obtain ⟨m, hm⟩ := hW.eq_Ico hne
  have h := hS i m W.card
  have he : serviceCount S i m (W.card : ℤ) = finiteService S i W := by
    simp only [serviceCount, windowCount, finiteService, ← hm]
  rw [he] at h
  apply Nat.le_of_lt_succ
  exact (Nat.floor_lt' (Nat.succ_ne_zero _)).mpr (by simpa using h)

theorem ValidRates.finiteValid {α : Type*} {r : α → ℝ} {S : ℤ → α}
    (hS : ValidRates r S) {F : WindowFamily α} (hF : F.Proper) :
    FiniteValid F r S := by
  intro i W hW
  exact hS.windowDemand i (hF i W hW).2 (hF i W hW).1

/-- Finite original windows are an exact obstruction language for the
bilateral all-window problem; finite solutions need not be compatible. -/
theorem schedulableRates_iff_finite_windows {α : Type*} [Fintype α]
    (r : α → ℝ) : SchedulableRates r ↔
      ∀ F : WindowFamily α, F.Proper → FiniteFeasible F r := by
  classical
  constructor
  · rintro ⟨S, hS⟩ F hF
    exact ⟨S, hS.finiteValid hF⟩
  · intro hfinite
    let F : Finset ℤ → WindowFamily α := fun U _ =>
      U.powerset.filter fun W => W.Nonempty ∧ IsWindow W
    have hF : ∀ U, (F U).Proper := by
      intro U i W hW
      exact (mem_filter.mp hW).2
    choose g hg using (fun U => hfinite (F U) (hF U))
    obtain ⟨S, hS⟩ := Finset.rado_selection g
    refine ⟨S, ?_⟩
    intro i m L
    by_cases hL : L = 0
    · subst L
      simp [serviceCount, windowCount]
    let W := Ico m (m + (L : ℤ))
    have hwne : W.Nonempty := by
      refine ⟨m, ?_⟩
      simp only [W, mem_Ico]
      constructor
      · exact le_rfl
      · have : 0 < (L : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hL
        omega
    have hwint : IsWindow W := isWindow_Ico m L
    obtain ⟨U, hWU, hagree⟩ := hS W
    have hWU' : W ∈ F U i := mem_filter.mpr
      ⟨mem_powerset.mpr hWU, hwne, hwint⟩
    have hquota := hg U i W hWU'
    have hcount : finiteService (g U) i W = finiteService S i W := by
      unfold finiteService
      congr 1
      apply filter_congr
      intro t ht
      rw [hagree t ht]
    rw [hcount] at hquota
    have hcard : W.card = L := by simp [W, Int.card_Ico]
    have hqR : (⌊(W.card : ℝ) * r i⌋₊ : ℝ) ≤ (finiteService S i W : ℝ) :=
      by exact_mod_cast hquota
    have hb := lt_of_lt_of_le (Nat.lt_floor_add_one ((W.card : ℝ) * r i))
      (show (⌊(W.card : ℝ) * r i⌋₊ : ℝ) + 1 ≤ (finiteService S i W : ℝ) + 1 by linarith)
    simpa only [hcard, finiteService, W, serviceCount, windowCount] using hb

theorem exists_finite_conflict {α : Type*} [Fintype α] {r : α → ℝ}
    (h : ¬SchedulableRates r) :
    ∃ F : WindowFamily α, F.Proper ∧ ¬FiniteFeasible F r := by
  classical
  simpa only [schedulableRates_iff_finite_windows, not_forall, exists_prop] using h

end RealPinwheel
