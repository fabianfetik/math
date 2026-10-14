import Pinwheel.WeakSevenBandData.NewInputs
import Pinwheel.WeakSevenBandData.UpperInputs
import Pinwheel.WeakSevenBandData.SecondInputs
import Mathlib.Algebra.BigOperators.Fin

/-! Derive exact certificate contexts from the analytic band hypotheses. -/
namespace RealPinwheel.WeakSevenBandData
open scoped BigOperators

theorem NewLargestCtx.of_rates (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (hheads : ∀ i, delta ≤ h i)
    (hsum : (∑ i : Fin 6, h i) + delta = (5 : ℝ)/6)
    (hlower : (1/10 : ℝ) ≤ delta) (hupper : delta ≤ (5/48 : ℝ))
    (hfail0 : 1 < 8*h 0) (hfail1 : 1 < 2*h 0+6*h 2)
    (hfail2 : 1 < 4*h 0+4*h 4) (hfail3 : 1 < 6*h 0+2*delta)
    (hmarkR : h 0 ≤ 2*delta)
    : NewLargestCtx h delta := by
  have hs : h 0+h 1+h 2+h 3+h 4+h 5+delta = (5 : ℝ)/6 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  exact {
    order0 := by have ho := horder 0 1 (by decide); linarith
    order1 := by have ho := horder 1 2 (by decide); linarith
    order2 := by have ho := horder 2 3 (by decide); linarith
    order3 := by have ho := horder 3 4 (by decide); linarith
    order4 := by have ho := horder 4 5 (by decide); linarith
    min := by have hm := hheads 5; linarith
    lower := by linarith only [hlower]
    upper := hupper
    fail0 := by linarith only [hfail0]
    fail1 := by linarith only [hfail1]
    fail2 := by linarith only [hfail2]
    fail3 := by linarith only [hfail3]
    markR := by linarith only [hmarkR]
    simplex := hs }

theorem UpperLargestCtx.of_rates (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (hheads : ∀ i, delta ≤ h i)
    (hsum : (∑ i : Fin 6, h i) + delta = (5 : ℝ)/6)
    (hlower : (5/48 : ℝ) ≤ delta) (hupper : delta ≤ (5/44 : ℝ))
    (hfail0 : 1 < 8*h 0) (hfail1 : 1 < 2*h 0+6*h 2)
    (hfail2 : 1 < 4*h 0+4*h 4) (hfail3 : 1 < 6*h 0+2*delta)
    : UpperLargestCtx h delta := by
  have hs : h 0+h 1+h 2+h 3+h 4+h 5+delta = (5 : ℝ)/6 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hmarkR : h 0 ≤ 2*delta := by
    have hb1 := hheads 1
    have hb2 := hheads 2
    have hb3 := hheads 3
    have hb4 := hheads 4
    have hb5 := hheads 5
    linarith
  exact {
    order0 := by have ho := horder 0 1 (by decide); linarith
    order1 := by have ho := horder 1 2 (by decide); linarith
    order2 := by have ho := horder 2 3 (by decide); linarith
    order3 := by have ho := horder 3 4 (by decide); linarith
    order4 := by have ho := horder 4 5 (by decide); linarith
    min := by have hm := hheads 5; linarith
    lower := by linarith only [hlower]
    upper := hupper
    fail0 := by linarith only [hfail0]
    fail1 := by linarith only [hfail1]
    fail2 := by linarith only [hfail2]
    fail3 := by linarith only [hfail3]
    markR := by linarith only [hmarkR]
    simplex := hs }

theorem SecondCtx.of_rates (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (hheads : ∀ i, delta ≤ h i)
    (hsum : (∑ i : Fin 6, h i) + delta = (5 : ℝ)/6)
    (hlower : (1/10 : ℝ) ≤ delta) (hupper : delta ≤ (5/44 : ℝ))
    (hfail0 : 1 < 8*h 0) (hfail1 : 1 < 2*h 0+6*h 2)
    (hfail2 : 1 < 4*h 0+4*h 4) (hfail3 : 1 < 6*h 0+2*delta)
    (hmarkL : 2*delta ≤ h 0) (hmarkR : h 1 ≤ 2*delta)
    : SecondCtx h delta := by
  have hs : h 0+h 1+h 2+h 3+h 4+h 5+delta = (5 : ℝ)/6 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  exact {
    order0 := by have ho := horder 0 1 (by decide); linarith
    order1 := by have ho := horder 1 2 (by decide); linarith
    order2 := by have ho := horder 2 3 (by decide); linarith
    order3 := by have ho := horder 3 4 (by decide); linarith
    order4 := by have ho := horder 4 5 (by decide); linarith
    min := by have hm := hheads 5; linarith
    lower := by linarith only [hlower]
    upper := hupper
    fail0 := by linarith only [hfail0]
    fail1 := by linarith only [hfail1]
    fail2 := by linarith only [hfail2]
    fail3 := by linarith only [hfail3]
    markL := by linarith only [hmarkL]
    markR := by linarith only [hmarkR]
    simplex := hs }

end RealPinwheel.WeakSevenBandData
