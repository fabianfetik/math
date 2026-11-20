import CorralFormalization.EndpointProof.Selector.Assembly.ColoredSelectorAvailability
import CorralFormalization.EndpointProof.Probability.SelectorPrimitivesAndAffineFlows

/-!
The complete selector and all currently admissible affine paired-cover candidates
hold together on one original sample and one auxiliary augmentation.
General six-root layout selection and the exceptional case remain separate.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

namespace EndpointFullProduct

open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

def OriginalAdmitsSelectorsAndAffineFlow
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (externalBudget qBudget : ℕ) (s : OriginalSample G) : Prop :=
  ∃ ω : FullSample G, originalProcess ω = s ∧
    EndpointSelector.Assembly.ColouredSelectors ω externalBudget ∧
    EndpointFlow.affineFlowEvent hodd hn qBudget ω

/-- On one fixed augmentation, the concrete selectors and all
admissible affine paired-cover candidates are jointly available. The final bound uses
uniform exact-matching theorem's literal parameters and q-dependent, group-independent threshold. -/
theorem original_selectors_and_affine_flow_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [CommRing G] [Fintype G]
      (hodd : Odd (Fintype.card G)) (hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ OriginalAdmitsSelectorsAndAffineFlow
          hodd (by omega) (selectorExternalBudget (p q) (Fintype.card G))
          (flowBudget (tau q) (Fintype.card G)) s} ≤
        Real.exp (-((xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N1,hN1⟩ := original_selector_primitives_and_affine_flow_probability q hq0 hq1
  obtain ⟨N2,hN2⟩ := selector_external_budget_slack q hq0
  refine ⟨max N1 N2, ?_⟩
  intro G _ _ hodd hn
  have hmargin : selectorExternalBudget (p q) (Fintype.card G) + 3996 ≤
      selectorBudget (p q) (Fintype.card G) := by
    have hm := hN2 (Fintype.card G) (by omega)
    omega
  have hbound := hN1 G hodd (by omega)
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hbound
  intro s hbad hgood
  obtain ⟨ω,hω,hall⟩ := hgood
  have hP : ∀ i : Fin 4,
      EndpointSelector.selectorPrimitiveEvents hodd (by omega)
        (selectorBudget (p q) (Fintype.card G)) i ω := by
    intro i
    fin_cases i
    · simpa [selectorAndAffineFlowEvents] using hall (0 : Fin 5)
    · simpa [selectorAndAffineFlowEvents] using hall (1 : Fin 5)
    · simpa [selectorAndAffineFlowEvents] using hall (2 : Fin 5)
    · simpa [selectorAndAffineFlowEvents] using hall (3 : Fin 5)
  have hQ : EndpointFlow.affineFlowEvent hodd (by omega)
      (flowBudget (tau q) (Fintype.card G)) ω := by
    simpa [selectorAndAffineFlowEvents] using hall (4 : Fin 5)
  have hselectors := EndpointSelector.Assembly.coloured_selectors_of_primitives
    hodd (by omega) (selectorBudget (p q) (Fintype.card G))
    (selectorExternalBudget (p q) (Fintype.card G)) hmargin ω hP
  exact hbad ⟨ω,hω,hselectors,hQ⟩

end
end EndpointFullProduct
