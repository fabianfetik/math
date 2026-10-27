import Pinwheel.Normalization
import Pinwheel.PeriodicCatalogue
import Pinwheel.StreamCatalogue
import Pinwheel.Coverage

/-!
# The complete five-task real-period pinwheel theorem

The finite construction certificates and the exact real-domain cover discharge
all obligations of the normalization theorem. The final declaration states the
original half-open window condition explicitly, for every positive scale and
every integer start, with no ordering or rationality restriction on periods.
-/

namespace RealPinwheel

theorem normalized_five_schedulable (r : Fin 5 → ℝ)
    (hr : NormalizedFive r) : SchedulableRates r := by
  rcases five_task_cover r hr with ⟨j, hcaps⟩ | ⟨j, hloads⟩
  · exact periodic_catalogue_schedulable j r hcaps
  · exact stream_catalogue_schedulable j r hr.1 hr.positive hloads

/-- Every positive real five-rate input of density at most `5/6` is schedulable. -/
theorem five_task_rates (r : Fin 5 → ℝ) (hr : ∀ i, 0 < r i)
    (hd : (∑ i, r i) ≤ (5 : ℝ) / 6) : SchedulableRates r :=
  schedulable_five_of_normalized normalized_five_schedulable r hr hd

/-- The original five-period existence theorem, using the shared definition. -/
theorem five_task_periods (a : Fin 5 → ℝ) (ha : ∀ i, 1 ≤ a i)
    (hd : (∑ i, 1 / a i) ≤ (5 : ℝ) / 6) :
    ∃ S : ℤ → Fin 5, ValidPeriods a S :=
  five_periods_of_normalized normalized_five_schedulable a ha hd

/-- The original service-window statement with its finite count made explicit.
This includes irrational periods, ties, density equality and negative time. -/
theorem five_task_real_period_pinwheel (a : Fin 5 → ℝ) (ha : ∀ i, 1 ≤ a i)
    (hd : (∑ i, 1 / a i) ≤ (5 : ℝ) / 6) :
    ∃ S : ℤ → Fin 5, ∀ (i : Fin 5) (m : ℤ) (ell : ℕ), 0 < ell →
      ell ≤ ((Finset.Ico m (m + ⌈(ell : ℝ) * a i⌉)).filter
        (fun t => S t = i)).card := by
  obtain ⟨S, hS⟩ := five_task_periods a ha hd
  refine ⟨S, ?_⟩
  intro i m ell hell
  have hcount : ((Finset.Ico m (m + ⌈(ell : ℝ) * a i⌉)).filter
      (fun t => S t = i)).card = serviceCount S i m ⌈(ell : ℝ) * a i⌉ := by
    unfold serviceCount windowCount
    congr 1
    ext t
    simp
  rw [hcount]
  exact hS i m ell hell

end RealPinwheel
