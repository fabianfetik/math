import Pinwheel.Rates
import Mathlib.Tactic.Linarith

/-!
# Weak service on the seven-role simplex

The weak quota is `ceil (L * r) - 1` in every translated integer window.
This is the boundary quota obtained by taking limits of ordinary schedules.
The distinguished role at index zero in `weakSevenRates` is the doubled
marked slack `2 * delta`.
-/

namespace RealPinwheel

open scoped BigOperators

/-- The weak all-window service contract.  At length zero the signed quota is
`-1`, so the condition is automatic; this lets the definition use natural
window lengths without a separate positivity case. -/
def WeakValidRates {α : Type*} [DecidableEq α]
    (r : α → ℝ) (S : ℤ → α) : Prop :=
  ∀ (i : α) (m : ℤ) (L : ℕ),
    Int.ceil ((L : ℝ) * r i) - 1 ≤
      (serviceCount S i m (L : ℤ) : ℤ)

/-- A strict rate increase turns weak service into ordinary service. -/
theorem WeakValidRates.toValidRates_of_strictly_smaller
    {α : Type*} [DecidableEq α] {r q : α → ℝ} {S : ℤ → α}
    (hweak : WeakValidRates q S) (hstrict : ∀ i, r i < q i) :
    ValidRates r S := by
  intro i m L
  by_cases hL : L = 0
  · subst L
    have hcount : (0 : ℝ) < (serviceCount S i m 0 : ℝ) + 1 := by
      positivity
    simpa using hcount
  · have hLpos : 0 < (L : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hL
    let x : ℝ := (L : ℝ) * r i
    let y : ℝ := (L : ℝ) * q i
    have hxy : x < y := by
      dsimp [x, y]
      exact mul_lt_mul_of_pos_left (hstrict i) hLpos
    have hyceil : y ≤ (Int.ceil y : ℝ) := Int.le_ceil y
    have hquota := hweak i m L
    have hquotaR : (Int.ceil y : ℝ) - 1 ≤
        (serviceCount S i m (L : ℤ) : ℝ) := by
      dsimp [y] at hquota ⊢
      exact_mod_cast hquota
    have hupper : (Int.ceil y : ℝ) ≤
        (serviceCount S i m (L : ℤ) : ℝ) + 1 := by
      linarith
    change (L : ℝ) * r i <
      (serviceCount S i m (L : ℤ) : ℝ) + 1
    exact lt_of_lt_of_le hxy (le_trans hyceil hupper)

/-- The seven rates associated with six heads and a doubled slack role. -/
def weakSevenRates (h : Fin 6 → ℝ) (delta : ℝ) : Fin 7 → ℝ :=
  Fin.cases (2 * delta) h

@[simp]
theorem weakSevenRates_zero (h : Fin 6 → ℝ) (delta : ℝ) :
    weakSevenRates h delta 0 = 2 * delta := by
  simp [weakSevenRates]

@[simp]
theorem weakSevenRates_succ (h : Fin 6 → ℝ) (delta : ℝ) (i : Fin 6) :
    weakSevenRates h delta i.succ = h i := by
  simp [weakSevenRates]

/-- WS7: every point of the six-head doubled-slack simplex has one common
weak all-window source.  Zero-rate roles impose only the vacuous signed quota
`-1` and may be left unused. -/
def WS7 : Prop :=
  ∀ (delta : ℝ) (h : Fin 6 → ℝ),
    0 ≤ delta →
    (∀ i, delta ≤ h i) →
    (∑ i, h i) + delta = (5 : ℝ) / 6 →
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S

/-- The ordinary H7 scheduling premise: all positive rate vectors on at most
seven roles and total at most `5/6` have an all-window source. -/
def H7Rates : Prop :=
  ∀ (n : ℕ), 0 < n → n ≤ 7 →
    ∀ r : Fin n → ℝ, (∀ i, 0 < r i) →
      (∑ i, r i) ≤ (5 : ℝ) / 6 → SchedulableRates r

end RealPinwheel
