import Pinwheel.WeakSevenBandData.SourceFits
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! Exact root hypotheses and reduced source-fit predicates. -/

namespace RealPinwheel.WeakSevenBandData

structure SecondCtx (h : Fin 6 → ℝ) (delta : ℝ) : Prop where
  order0 : -(h 0) + h 1 ≤ (0 : ℝ)
  order1 : -(h 1) + h 2 ≤ (0 : ℝ)
  order2 : -(h 2) + h 3 ≤ (0 : ℝ)
  order3 : -(h 3) + h 4 ≤ (0 : ℝ)
  order4 : -(h 4) + h 5 ≤ (0 : ℝ)
  min : -(h 5) + delta ≤ (0 : ℝ)
  lower : -(delta) ≤ (-1/10 : ℝ)
  upper : delta ≤ (5/44 : ℝ)
  fail0 : ((-8 : ℝ) * (h 0)) < (-1 : ℝ)
  fail1 : ((-2 : ℝ) * (h 0)) + ((-6 : ℝ) * (h 2)) < (-1 : ℝ)
  fail2 : ((-4 : ℝ) * (h 0)) + ((-4 : ℝ) * (h 4)) < (-1 : ℝ)
  fail3 : ((-6 : ℝ) * (h 0)) + ((-2 : ℝ) * (delta)) < (-1 : ℝ)
  markL : -(h 0) + ((2 : ℝ) * (delta)) ≤ (0 : ℝ)
  markR : h 1 + ((-2 : ℝ) * (delta)) ≤ (0 : ℝ)
  simplex : h 0 + h 1 + h 2 + h 3 + h 4 + h 5 + delta = (5/6 : ℝ)

end RealPinwheel.WeakSevenBandData
