import CorralFormalization.EndpointProof.Selector.PrimitiveAvailability
import CorralFormalization.EndpointProof.Flow.AffineAvailability

/-!
One original sample and one augmentation for the actual P selector
primitives and the actual affine Q six-root flow candidates. The remaining paired-cover
layout-selection and exceptional matching supplier are not asserted here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

namespace EndpointFullProduct

open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

/-- Four P-primitive families and the affine Q-flow family, on the same
augmented sample; each individual event covers its own later queries. -/
def selectorAndAffineFlowEvents (hodd : Odd (Fintype.card G))
    (hn : 1000 ≤ Fintype.card G) (pBudget qBudget : ℕ) :
    Fin 5 → FullSample G → Prop :=
  ![EndpointSelector.selectorPrimitiveEvents hodd hn pBudget 0,
    EndpointSelector.selectorPrimitiveEvents hodd hn pBudget 1,
    EndpointSelector.selectorPrimitiveEvents hodd hn pBudget 2,
    EndpointSelector.selectorPrimitiveEvents hodd hn pBudget 3,
    EndpointFlow.affineFlowEvent hodd hn qBudget]

/-- The genuine switch, all rotated small stars, and every admissible
affine six-root candidate share one original-law event and one augmentation,
with the final exact-matching exponential failure bound. This is not full selector/paired-cover. -/
theorem original_selector_primitives_and_affine_flow_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [CommRing G] [Fintype G]
      (hodd : Odd (Fintype.card G)) (hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ OriginalAdmitsEvents
          (selectorAndAffineFlowEvents hodd (by omega)
            (selectorBudget (p q) (Fintype.card G))
            (flowBudget (tau q) (Fintype.card G))) s} ≤
        Real.exp (-((xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := original_finite_events_probability (T := Fin 5) q hq0 hq1
    (![6,6,6,6,18] : Fin 5 → ℝ) (![2,1,2,3,6] : Fin 5 → ℕ)
    (![true,true,true,true,false] : Fin 5 → Bool)
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  have hnN : N ≤ Fintype.card G := (le_max_left N 2000).trans hn
  have hn2000 : 2000 ≤ Fintype.card G := (le_max_right N 2000).trans hn
  have hP0 := EndpointSelector.selector_primitive_full_error q hq0 hq1 hodd hn2000 0
  have hP1 := EndpointSelector.selector_primitive_full_error q hq0 hq1 hodd hn2000 1
  have hP2 := EndpointSelector.selector_primitive_full_error q hq0 hq1 hodd hn2000 2
  have hP3 := EndpointSelector.selector_primitive_full_error q hq0 hq1 hodd hn2000 3
  have hQ := EndpointFlow.affine_flow_full_error q hq0 hq1 hodd hn2000
  apply hN G hnN
    (selectorAndAffineFlowEvents hodd (by omega)
      (selectorBudget (p q) (Fintype.card G)) (flowBudget (tau q) (Fintype.card G)))
  intro i
  fin_cases i
  · simpa [selectorAndAffineFlowEvents,pqTailRate] using hP0
  · simpa [selectorAndAffineFlowEvents,pqTailRate] using hP1
  · simpa [selectorAndAffineFlowEvents,pqTailRate] using hP2
  · simpa [selectorAndAffineFlowEvents,pqTailRate] using hP3
  · simpa [selectorAndAffineFlowEvents,pqTailRate] using hQ

end
end EndpointFullProduct
