import Pinwheel.WeakSeven

/-! Monotonicity and ordinary-to-weak service transport on the same trace. -/
namespace RealPinwheel

theorem ValidRates.toWeakValidRates {α : Type*} [DecidableEq α]
    {r : α → ℝ} {S : ℤ → α} (h : ValidRates r S) : WeakValidRates r S := by
  intro i m L
  have hh := h i m L
  have hc : Int.ceil ((L : ℝ)*r i) ≤ (serviceCount S i m (L : ℤ) : ℤ)+1 := by
    apply Int.ceil_le.mpr
    exact le_of_lt (by simpa using hh)
  omega

theorem WeakValidRates.mono {α : Type*} [DecidableEq α]
    {r q : α → ℝ} {S : ℤ → α} (h : WeakValidRates q S)
    (hle : ∀ i, r i ≤ q i) : WeakValidRates r S := by
  intro i m L
  have hh := h i m L
  have hm := Int.ceil_mono (mul_le_mul_of_nonneg_left (hle i) (Nat.cast_nonneg L))
  omega

theorem WeakValidRates.relabel {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) {r : β → ℝ} {S : ℤ → α}
    (h : WeakValidRates (fun i => r (e i)) S) :
    WeakValidRates r (fun t => e (S t)) := by
  intro i m L
  have hc := serviceCount_relabel e S (e.symm i) m (L : ℤ)
  simp only [e.apply_symm_apply] at hc
  rw [hc]
  simpa only [e.apply_symm_apply] using h (e.symm i) m L

end RealPinwheel
