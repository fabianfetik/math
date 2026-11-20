import CorralFormalization.EndpointProof.Probability.SelectorsAndAffineFlows
import CorralFormalization.EndpointProof.Flow.Cover.ConcreteSupplier
import Mathlib.Data.ZMod.Basic

/-!
The complete selectors and the complete six-root supplier share one
original sample and one augmentation. The iterative paired-cover theorem
is connected separately.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal Classical

namespace EndpointFullProduct

open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

/-- The same augmentation supplies every selector and every paired-cover
six-root query with the corresponding external numerical budgets. -/
def OriginalAdmitsSelectorsAndSixRoots (externalBudget qBudget : ℕ)
    (s : OriginalSample G) : Prop :=
  ∃ ω : FullSample G, originalProcess ω = s ∧
    EndpointSelector.Assembly.ColouredSelectors ω externalBudget ∧
    EndpointFlow.Cover.SixRootSupplier (EndpointFlow.QVertex ω) qBudget

/-- On the actual original law, one augmentation simultaneously supplies
complete selector and all six-root suppliers, including the 3-torsion case. -/
theorem original_selectors_and_sixRoots_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [CommRing G] [Fintype G]
      (hodd : Odd (Fintype.card G)) (hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ OriginalAdmitsSelectorsAndSixRoots
          (selectorExternalBudget (p q) (Fintype.card G))
          (flowBudget (tau q) (Fintype.card G)) s} ≤
        Real.exp (-((xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := original_selectors_and_affine_flow_probability q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  have hbound := hN G hodd hn
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hbound
  intro s hbad hgood
  obtain ⟨ω,hω,hselectors,haffine⟩ := hgood
  have hsupplier := EndpointFlow.Cover.sixRootSupplier_of_affine_event hodd (by omega)
    (flowBudget (tau q) (Fintype.card G)) ω haffine
  exact hbad ⟨ω,hω,hselectors,hsupplier⟩

/-- Literal cyclic-group instance required by the corral manuscript. -/
theorem cyclic_selectors_and_sixRoots
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (n : ℕ) [NeZero n] (hodd : Odd n) (hn : max N 2000 ≤ n),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample (ZMod n) | ¬ OriginalAdmitsSelectorsAndSixRoots
          (selectorExternalBudget (p q) n) (flowBudget (tau q) n) s} ≤
        Real.exp (-((xi q)^4 / 10^6) * n) := by
  obtain ⟨N,hN⟩ := original_selectors_and_sixRoots_probability q hq0 hq1
  refine ⟨N, ?_⟩
  intro n _ hodd hn
  have hodd' : Odd (Fintype.card (ZMod n)) := by simpa only [ZMod.card] using hodd
  have hn' : max N 2000 ≤ Fintype.card (ZMod n) := by simpa only [ZMod.card] using hn
  simpa only [ZMod.card] using hN (ZMod n) hodd' hn'

end
end EndpointFullProduct
