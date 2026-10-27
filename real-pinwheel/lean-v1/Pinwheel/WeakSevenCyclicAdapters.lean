import Pinwheel.WeakSevenCyclicSources
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.SecondSourceCaps

/-! Bridges from the exact reduced inherited-profile fit predicates to the
cyclic schedulers in `WeakSevenCyclicSources`. -/

namespace RealPinwheel

open WeakSevenBandData

private theorem ws7_rate_one (h : Fin 6 → ℝ) (delta : ℝ) :
    weakSevenRates h delta (1 : Fin 7) = h 0 := by
  have heq : (1 : Fin 7) = Fin.succ (0 : Fin 6) := by decide
  rw [heq, weakSevenRates_succ]

private theorem ws7_rate_two (h : Fin 6 → ℝ) (delta : ℝ) :
    weakSevenRates h delta (2 : Fin 7) = h 1 := by
  have heq : (2 : Fin 7) = Fin.succ (1 : Fin 6) := by decide
  rw [heq, weakSevenRates_succ]

private theorem ws7_rate_three (h : Fin 6 → ℝ) (delta : ℝ) :
    weakSevenRates h delta (3 : Fin 7) = h 2 := by
  have heq : (3 : Fin 7) = Fin.succ (2 : Fin 6) := by decide
  rw [heq, weakSevenRates_succ]

private theorem ws7_rate_four (h : Fin 6 → ℝ) (delta : ℝ) :
    weakSevenRates h delta (4 : Fin 7) = h 3 := by
  have heq : (4 : Fin 7) = Fin.succ (3 : Fin 6) := by decide
  rw [heq, weakSevenRates_succ]

private theorem ws7_rate_five (h : Fin 6 → ℝ) (delta : ℝ) :
    weakSevenRates h delta (5 : Fin 7) = h 4 := by
  have heq : (5 : Fin 7) = Fin.succ (4 : Fin 6) := by decide
  rw [heq, weakSevenRates_succ]

private theorem ws7_rate_six (h : Fin 6 → ℝ) (delta : ℝ) :
    weakSevenRates h delta (6 : Fin 7) = h 5 := by
  have heq : (6 : Fin 7) = Fin.succ (5 : Fin 6) := by decide
  rw [heq, weakSevenRates_succ]

theorem ws7UpperCyclic30 {h : Fin 6 → ℝ} {delta : ℝ}
    (hr : ∀ i, 0 < weakSevenRates h delta i)
    (hfit : UpperSourceFits (30 : Fin 157) h delta) :
    SchedulableRates (weakSevenRates h delta) := by
  rcases hfit with ⟨h1d, h2d, h5d, h01, h02, h05,
      h13, h23, h35, h14, h24, h45⟩
  apply ws7CyclicProfile49.schedulable_of_pair_loads hr
  intro i j hi hj
  fin_cases i <;> fin_cases j <;>
    simp_all [ws7CyclicProfile49, ws7CyclicSide49, ws7CyclicPeriod49,
      ws7_rate_one, ws7_rate_two, ws7_rate_three,
      ws7_rate_four, ws7_rate_five, ws7_rate_six] <;>
    linarith

theorem ws7UpperCyclic31 {h : Fin 6 → ℝ} {delta : ℝ}
    (hr : ∀ i, 0 < weakSevenRates h delta i)
    (hfit : UpperSourceFits (31 : Fin 157) h delta) :
    SchedulableRates (weakSevenRates h delta) := by
  rcases hfit with ⟨h0d, h01, h02, h03, h04, h05⟩
  apply ws7CyclicProfile50.schedulable_of_pair_loads hr
  intro i j hi hj
  fin_cases i <;> fin_cases j <;>
    simp_all [ws7CyclicProfile50, ws7CyclicSide50, ws7CyclicPeriod50,
      ws7_rate_one, ws7_rate_two, ws7_rate_three, ws7_rate_four,
      ws7_rate_five, ws7_rate_six] <;>
    linarith

theorem ws7UpperCyclic32 {h : Fin 6 → ℝ} {delta : ℝ}
    (hr : ∀ i, 0 < weakSevenRates h delta i)
    (hfit : UpperSourceFits (32 : Fin 157) h delta) :
    SchedulableRates (weakSevenRates h delta) := by
  rcases hfit with ⟨h5d, h05, h15, h25, h35, h45⟩
  apply ws7CyclicProfile51.schedulable_of_pair_loads hr
  intro i j hi hj
  fin_cases i <;> fin_cases j <;>
    simp_all [ws7CyclicProfile51, ws7CyclicSide51, ws7CyclicPeriod51,
      ws7_rate_one, ws7_rate_two, ws7_rate_three, ws7_rate_four,
      ws7_rate_five, ws7_rate_six]
  all_goals linarith

theorem ws7UpperCyclic50 {h : Fin 6 → ℝ} {delta : ℝ}
    (hr : ∀ i, 0 < weakSevenRates h delta i)
    (hfit : UpperSourceFits (50 : Fin 157) h delta) :
    SchedulableRates (weakSevenRates h delta) := by
  rcases hfit with ⟨h1d, h01, h12, h13, h14, h15⟩
  apply ws7CyclicProfile69.schedulable_of_pair_loads hr
  intro i j hi hj
  fin_cases i <;> fin_cases j <;>
    simp_all [ws7CyclicProfile69, ws7CyclicSide69, ws7CyclicPeriod69,
      ws7_rate_one, ws7_rate_two, ws7_rate_three, ws7_rate_four,
      ws7_rate_five, ws7_rate_six] <;>
    linarith

theorem ws7UpperCyclic90 {h : Fin 6 → ℝ} {delta : ℝ}
    (hr : ∀ i, 0 < weakSevenRates h delta i)
    (hfit : UpperSourceFits (90 : Fin 157) h delta) :
    SchedulableRates (weakSevenRates h delta) := by
  rcases hfit with ⟨h3d, h03, h13, h23, h34, h35⟩
  apply ws7CyclicProfile109.schedulable_of_pair_loads hr
  intro i j hi hj
  fin_cases i <;> fin_cases j <;>
    simp_all [ws7CyclicProfile109, ws7CyclicSide109, ws7CyclicPeriod109,
      ws7_rate_one, ws7_rate_two, ws7_rate_three, ws7_rate_four,
      ws7_rate_five, ws7_rate_six] <;>
    linarith

theorem ws7UpperCyclic151 {h : Fin 6 → ℝ} {delta : ℝ}
    (hr : ∀ i, 0 < weakSevenRates h delta i)
    (hfit : UpperSourceFits (151 : Fin 157) h delta) :
    SchedulableRates (weakSevenRates h delta) := by
  rcases hfit with ⟨h1d, h2d, h3d, h01, h02, h03,
    h14, h24, h34, h15, h25, h35⟩
  apply ws7CyclicProfile170.schedulable_of_pair_loads hr
  intro i j hi hj
  fin_cases i <;> fin_cases j <;>
    simp_all [ws7CyclicProfile170, ws7CyclicSide170, ws7CyclicPeriod170,
      ws7_rate_one, ws7_rate_two, ws7_rate_three, ws7_rate_four,
      ws7_rate_five, ws7_rate_six] <;>
    linarith

theorem ws7UpperCyclic152 {h : Fin 6 → ℝ} {delta : ℝ}
    (hr : ∀ i, 0 < weakSevenRates h delta i)
    (hfit : UpperSourceFits (152 : Fin 157) h delta) :
    SchedulableRates (weakSevenRates h delta) := by
  rcases hfit with ⟨h1d, h2d, h3d, h4d, h5d,
    h01, h02, h03, h04, h05⟩
  apply ws7CyclicProfile171.schedulable_of_pair_loads hr
  intro i j hi hj
  fin_cases i <;> fin_cases j <;>
    simp_all [ws7CyclicProfile171, ws7CyclicSide171, ws7CyclicPeriod171,
      ws7_rate_one, ws7_rate_two, ws7_rate_three, ws7_rate_four,
      ws7_rate_five, ws7_rate_six] <;>
    linarith

/-- Dispatch the seven inherited no-cap cyclic source leaves in the upper
largest-mark band. -/
theorem ws7UpperCyclicSource_schedulable {sid : Fin 157}
    {h : Fin 6 → ℝ} {delta : ℝ}
    (hsid : sid.val = 30 ∨ sid.val = 31 ∨ sid.val = 32 ∨
      sid.val = 50 ∨ sid.val = 90 ∨ sid.val = 151 ∨ sid.val = 152)
    (hr : ∀ i, 0 < weakSevenRates h delta i)
    (hfit : UpperSourceFits sid h delta) :
    SchedulableRates (weakSevenRates h delta) := by
  rcases hsid with hsid | hsid | hsid | hsid | hsid | hsid | hsid
  · have hs : sid = (30 : Fin 157) := Fin.ext hsid
    subst sid
    exact ws7UpperCyclic30 hr hfit
  · have hs : sid = (31 : Fin 157) := Fin.ext hsid
    subst sid
    exact ws7UpperCyclic31 hr hfit
  · have hs : sid = (32 : Fin 157) := Fin.ext hsid
    subst sid
    exact ws7UpperCyclic32 hr hfit
  · have hs : sid = (50 : Fin 157) := Fin.ext hsid
    subst sid
    exact ws7UpperCyclic50 hr hfit
  · have hs : sid = (90 : Fin 157) := Fin.ext hsid
    subst sid
    exact ws7UpperCyclic90 hr hfit
  · have hs : sid = (151 : Fin 157) := Fin.ext hsid
    subst sid
    exact ws7UpperCyclic151 hr hfit
  · have hs : sid = (152 : Fin 157) := Fin.ext hsid
    subst sid
    exact ws7UpperCyclic152 hr hfit

/-- Weak-service form of the cyclic upper-source dispatcher. -/
theorem ws7UpperCyclicSource_weak {sid : Fin 157}
    {h : Fin 6 → ℝ} {delta : ℝ}
    (hsid : sid.val = 30 ∨ sid.val = 31 ∨ sid.val = 32 ∨
      sid.val = 50 ∨ sid.val = 90 ∨ sid.val = 151 ∨ sid.val = 152)
    (hr : ∀ i, 0 < weakSevenRates h delta i)
    (hfit : UpperSourceFits sid h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  obtain ⟨S, hS⟩ := ws7UpperCyclicSource_schedulable hsid hr hfit
  exact ⟨S, hS.toWeakValidRates⟩

/-- The checked reduced cap rows for a marked-second cyclic leaf lift to all
seven descending rates, after which its exact inherited profile supplies an
ordinary source. -/
theorem ws7SecondCyclicSource_schedulable {sid : Fin 15}
    {h : Fin 6 → ℝ} {delta : ℝ}
    (hsid : 4 ≤ sid.val)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (hmarkL : 2 * delta ≤ h 0) (hmarkR : h 1 ≤ 2 * delta)
    (hr : ∀ i, 0 < secondRankRates h delta i)
    (hfit : SecondSourceFits sid h delta) :
    SchedulableRates (secondRankRates h delta) := by
  exact ws7SecondCycleSchedulable sid hsid hr
    (secondSourceCapsOfFit sid hsid horder hmarkL hmarkR hfit)

/-- Weak-service form of the marked-second cyclic leaf adapter. -/
theorem ws7SecondCyclicSource_weak {sid : Fin 15}
    {h : Fin 6 → ℝ} {delta : ℝ}
    (hsid : 4 ≤ sid.val)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (hmarkL : 2 * delta ≤ h 0) (hmarkR : h 1 ≤ 2 * delta)
    (hr : ∀ i, 0 < secondRankRates h delta i)
    (hfit : SecondSourceFits sid h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (secondRankRates h delta) S := by
  obtain ⟨S, hS⟩ :=
    ws7SecondCyclicSource_schedulable hsid horder hmarkL hmarkR hr hfit
  exact ⟨S, hS.toWeakValidRates⟩

end RealPinwheel
