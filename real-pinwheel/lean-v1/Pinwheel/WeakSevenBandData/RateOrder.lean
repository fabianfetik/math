import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace RealPinwheel.WeakSevenBandData

/-- A cap plateau is controlled by its first position.  If the target and cap
vectors are descending, representative bounds imply every coordinate bound. -/
theorem caps_of_representatives {r cap : Fin 7 → ℝ} (rep : Fin 7 → Fin 7)
    (hrep_le : ∀ i, (rep i).val ≤ i.val)
    (hcap_eq : ∀ i, cap (rep i) = cap i)
    (hrate_order : ∀ i j : Fin 7, i.val ≤ j.val → r j ≤ r i)
    (hfit : ∀ i, r (rep i) ≤ cap (rep i)) :
    ∀ i, r i ≤ cap i := by
  intro i
  calc
    r i ≤ r (rep i) := hrate_order (rep i) i (hrep_le i)
    _ ≤ cap (rep i) := hfit i
    _ = cap i := hcap_eq i

/-- Adjacent comparisons telescope to the descending order needed by the
reduced-cap word certificates. -/
theorem weakSeven_rate_order_of_adjacent (r : Fin 7 → ℝ)
    (hadj : ∀ i : Fin 6, r i.succ ≤ r i.castSucc) :
    ∀ i j : Fin 7, i ≤ j → r j ≤ r i := by
  intro i j hij
  have h0 := hadj (0 : Fin 6)
  have h1 := hadj (1 : Fin 6)
  have h2 := hadj (2 : Fin 6)
  have h3 := hadj (3 : Fin 6)
  have h4 := hadj (4 : Fin 6)
  have h5 := hadj (5 : Fin 6)
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals linarith [h0, h1, h2, h3, h4, h5]

/-- The rank-zero rates are descending when the distinguished doubled slack
is at least the largest head. -/
theorem weakSeven_rates_order_m0 {h : Fin 6 → ℝ} {delta : ℝ}
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (hmark : h 0 ≤ 2 * delta) :
    ∀ i j : Fin 7, i.val ≤ j.val → weakSevenRates h delta j ≤ weakSevenRates h delta i := by
  apply weakSeven_rate_order_of_adjacent
  intro i
  fin_cases i
  · change h 0 ≤ 2 * delta
    exact hmark
  · change h 1 ≤ h 0
    exact horder 0 1 (by norm_num)
  · change h 2 ≤ h 1
    exact horder 1 2 (by norm_num)
  · change h 3 ≤ h 2
    exact horder 2 3 (by norm_num)
  · change h 4 ≤ h 3
    exact horder 3 4 (by norm_num)
  · change h 5 ≤ h 4
    exact horder 4 5 (by norm_num)

/-- The second-rank marked-rate vector: `h₀, 2δ, h₁, …, h₅`. -/
def secondRankRates (h : Fin 6 → ℝ) (delta : ℝ) : Fin 7 → ℝ :=
  Fin.cases (h 0) (Fin.cases (2 * delta) (fun i : Fin 5 => h i.succ))

theorem secondRankRates_order {h : Fin 6 → ℝ} {delta : ℝ}
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (hmarkL : 2 * delta ≤ h 0) (hmarkR : h 1 ≤ 2 * delta) :
    ∀ i j : Fin 7, i.val ≤ j.val → secondRankRates h delta j ≤ secondRankRates h delta i := by
  apply weakSeven_rate_order_of_adjacent
  intro i
  fin_cases i
  · change 2 * delta ≤ h 0
    exact hmarkL
  · change h 1 ≤ 2 * delta
    exact hmarkR
  · change h 2 ≤ h 1
    exact horder 1 2 (by norm_num)
  · change h 3 ≤ h 2
    exact horder 2 3 (by norm_num)
  · change h 4 ≤ h 3
    exact horder 3 4 (by norm_num)
  · change h 5 ≤ h 4
    exact horder 4 5 (by norm_num)

end RealPinwheel.WeakSevenBandData
