import Pinwheel.Rates
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace RealPinwheel

theorem NormalizedFive.positive {r : Fin 5 → ℝ} (h : NormalizedFive r) :
    ∀ i, 0 < r i := by
  obtain ⟨⟨h10, h21, h32, h43⟩, hp, _⟩ := h
  intro i
  have h3 := lt_of_lt_of_le hp h43
  have h2 := lt_of_lt_of_le h3 h32
  have h1 := lt_of_lt_of_le h2 h21
  have h0 := lt_of_lt_of_le h1 h10
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- Sorting and density normalization transport a theorem on the closed
density boundary to every positive five-rate input below the threshold. -/
theorem schedulable_five_of_normalized
    (solve : ∀ r : Fin 5 → ℝ, NormalizedFive r → SchedulableRates r)
    (r : Fin 5 → ℝ) (hr : ∀ i, 0 < r i)
    (hd : (∑ i, r i) ≤ (5 : ℝ) / 6) : SchedulableRates r := by
  classical
  let D : ℝ := ∑ i, r i
  have hD : 0 < D := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  let c : ℝ := ((5 : ℝ) / 6) / D
  have hc : 1 ≤ c := by
    apply (le_div_iff₀ hD).mpr
    simpa [D] using hd
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  let q : Fin 5 → ℝ := fun i => c * r i
  have hqpos : ∀ i, 0 < q i := fun i => mul_pos hcpos (hr i)
  have hqsum : (∑ i, q i) = (5 : ℝ) / 6 := by
    simp only [q, ← Finset.mul_sum]
    exact div_mul_cancel₀ _ (ne_of_gt hD)
  let e : Equiv.Perm (Fin 5) := Tuple.sort (fun i => OrderDual.toDual (q i))
  have he : Antitone (fun i => q (e i)) := by
    exact Tuple.monotone_sort (fun i => OrderDual.toDual (q i))
  have hnorm : NormalizedFive (fun i => q (e i)) := by
    refine ⟨⟨he (by decide : (0 : Fin 5) ≤ 1), he (by decide : (1 : Fin 5) ≤ 2),
      he (by decide : (2 : Fin 5) ≤ 3), he (by decide : (3 : Fin 5) ≤ 4)⟩,
      hqpos (e 4), ?_⟩
    rw [Equiv.sum_comp e q]
    exact hqsum
  have hq : SchedulableRates q := SchedulableRates.relabel e (solve _ hnorm)
  exact hq.mono (fun i => by
    dsimp [q]
    nlinarith [hr i])

/-- The exact original five-period conclusion follows from the normalized
rate theorem, without any rationality or strict-order assumption. -/
theorem five_periods_of_normalized
    (solve : ∀ r : Fin 5 → ℝ, NormalizedFive r → SchedulableRates r)
    (a : Fin 5 → ℝ) (ha : ∀ i, 1 ≤ a i)
    (hd : (∑ i, 1 / a i) ≤ (5 : ℝ) / 6) :
    ∃ S : ℤ → Fin 5, ValidPeriods a S := by
  have ha0 : ∀ i, 0 < a i := fun i => lt_of_lt_of_le zero_lt_one (ha i)
  obtain ⟨S, hS⟩ := schedulable_five_of_normalized solve (fun i => (a i)⁻¹)
    (fun i => inv_pos.mpr (ha0 i)) (by simpa only [one_div] using hd)
  exact ⟨S, (validPeriods_iff_validRates_inv ha0 S).mpr hS⟩

end RealPinwheel
