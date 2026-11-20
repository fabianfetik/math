import CorralFormalization.EndpointProof.Selector.Assembly.ColoredSelectors
import CorralFormalization.EndpointProof.Selector.Stars.ConcreteSmall

/-!
Complete selector from the actual common primitive event: all tag rotations,
stars, fresh helpers, small paths, and arbitrary 1≤k≤100 target families.
The original-model event has the paper's literal parameters and exponent.
-/

open MeasureTheory
open scoped Classical

namespace EndpointSelector.Assembly

open EndpointFullProduct
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

section Finite

variable {G : Type*} [CommRing G] [Fintype G]

/-- Complete deterministic selector on the very same primitive sample ω. No
supplier premise remains: the concrete stars and switches discharge it. -/
theorem coloured_selectors_of_primitives
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget C : ℕ) (hmargin : C+3996 ≤ budget) (ω : FullSample G)
    (hprimitive : ∀ i, selectorPrimitiveEvents hodd hn budget i ω) :
    ColouredSelectors ω C := by
  exact coloured_selectors_of_small_supply hodd hn budget C hmargin ω hprimitive
    (Stars.smallSupply_of_selectorPrimitiveEvents hodd hn budget ω hprimitive)

/-- A single augmentation works before every subsequent part/root/forbidden
query. Each constructed selector has one interior shared by all targets. -/
theorem one_augmentation_all_coloured_selectors
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget C : ℕ) (hmargin : C+3996 ≤ budget) (s : OriginalSample G)
    (hgood : OriginalAdmitsEvents (selectorPrimitiveEvents hodd hn budget) s) :
    OriginalAdmitsColouredSelectors C s := by
  obtain ⟨ω,hω,hprimitive⟩ := hgood
  exact ⟨ω,hω,coloured_selectors_of_primitives hodd hn budget C hmargin ω hprimitive⟩

end Finite

/-- Literal paper-parameter coloured selectors. One q-dependent threshold
works for every finite odd commutative ring. The targets need not lie in P,
and the forbidden numerical support is chosen after the common sample.
The event's exponent is exactly ξ⁴/10⁶, with no residual polynomial factor. -/
theorem original_coloured_selector_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [CommRing G] [Fintype G]
      (hodd : Odd (Fintype.card G)) (hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ OriginalAdmitsColouredSelectors
          (selectorExternalBudget (p q) (Fintype.card G)) s} ≤
        Real.exp (-((xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := selector_primitives_with_slack q hq0 hq1
  refine ⟨N,?_⟩
  intro G _ _ hodd hn
  obtain ⟨hmargin,herror⟩ := hN G hodd hn
  have hmargin' : selectorExternalBudget (p q) (Fintype.card G)+3996 ≤
      selectorBudget (p q) (Fintype.card G) := by omega
  have htransfer := original_selector_failure_le_primitive_failure q (le_of_lt hq0) hq1
    hodd (by omega) (selectorBudget (p q) (Fintype.card G))
    (selectorExternalBudget (p q) (Fintype.card G)) hmargin'
    (fun ω hprimitive ↦ Stars.smallSupply_of_selectorPrimitiveEvents hodd (by omega)
      (selectorBudget (p q) (Fintype.card G)) ω hprimitive)
  exact htransfer.trans herror

end
end EndpointSelector.Assembly
