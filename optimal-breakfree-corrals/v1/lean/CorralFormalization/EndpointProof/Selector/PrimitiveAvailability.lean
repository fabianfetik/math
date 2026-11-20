import CorralFormalization.EndpointProof.Probability.FiniteEventAvailability
import CorralFormalization.EndpointProof.Selector.Stars.Availability
import CorralFormalization.EndpointProof.Selector.Assembly.RotatedSwitches
import CorralFormalization.EndpointProof.Probability.SelectorSlack

/-!
One actual paper-parameter event for the concrete switch and all small stars,
including every permutation of the three tagged parts.

This supplies the primitive events on one augmentation. Constructing a
complete k-selector from them is a separate deterministic obligation.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

namespace EndpointSelector

open EndpointFullProduct
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

/-- Four simultaneously required, concrete primitive families: the two-pair
switch and the stars on one, two and three target pairs. Each family
already quantifies over all six tag permutations, all legal root queries,
and all later forbidden supports within the given budget. -/
def selectorPrimitiveEvents (hodd : Odd (Fintype.card G))
    (hn : 1000 ≤ Fintype.card G) (budget : ℕ) : Fin 4 → FullSample G → Prop :=
  ![fun ω ↦ Assembly.AllRotatedSwitches hodd hn budget ω,
    fun ω ↦ FullAvailable
      (Stars.rotatedStarQueryEmbedding (k := 1) (by omega) hodd hn)
      (fun r _ ↦ Stars.rotatedStarDemand (k := 1) r.1) budget ω,
    fun ω ↦ FullAvailable
      (Stars.rotatedStarQueryEmbedding (k := 2) (by omega) hodd hn)
      (fun r _ ↦ Stars.rotatedStarDemand (k := 2) r.1) budget ω,
    fun ω ↦ FullAvailable
      (Stars.rotatedStarQueryEmbedding (k := 3) (by omega) hodd hn)
      (fun r _ ↦ Stars.rotatedStarDemand (k := 3) r.1) budget ω]

/-- Each of the four concrete P-primitive families has its actual
polynomial query bound on the common paper-parameter augmented sample. -/
theorem selector_primitive_full_error
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G) (i : Fin 4) :
    (parameterizedFullMeasure G q hq0 hq1).real
      {ω | ¬ selectorPrimitiveEvents hodd (by omega)
        (selectorBudget (p q) (Fintype.card G)) i ω} ≤
      6 * (Fintype.card G : ℝ)^(![2,1,2,3] : Fin 4 → ℕ) i *
        Real.exp (-((p q)^8 / 32000) * (Fintype.card G : ℝ)) := by
  obtain ⟨hη0,hη1,ha,hb,hab,hp,hcat,hP,hQ⟩ :=
    samplingParameters_admissible q hq0 hq1
  have hsw := Assembly.full_sample_rotated_switch_budget hodd hn q eta (1/4)
    (tau q / SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
    (pNN q) (tauNN q) hp hcat hP hQ
  have hs1 := Stars.full_sample_rotated_star_budget (k := 1) (by omega) hodd hn q eta (1/4)
    (tau q / SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
    (pNN q) (tauNN q) hp hcat hP hQ
  have hs2 := Stars.full_sample_rotated_star_budget (k := 2) (by omega) hodd hn q eta (1/4)
    (tau q / SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
    (pNN q) (tauNN q) hp hcat hP hQ
  have hs3 := Stars.full_sample_rotated_star_budget (k := 3) (by omega) hodd hn q eta (1/4)
    (tau q / SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
    (pNN q) (tauNN q) hp hcat hP hQ
  have hpNN : (pNN q : ℝ) = p q := rfl
  rw [hpNN] at hsw hs1 hs2 hs3
  fin_cases i
  · simpa [selectorPrimitiveEvents, parameterizedFullMeasure] using hsw
  · simpa [selectorPrimitiveEvents, parameterizedFullMeasure] using hs1
  · simpa [selectorPrimitiveEvents, parameterizedFullMeasure] using hs2
  · simpa [selectorPrimitiveEvents, parameterizedFullMeasure] using hs3

/-- In the actual original vertex/colour law, one augmentation supplies all
four concrete primitive families and all tag permutations, except with at
most uniform exact-matching theorem's final exponential error. This theorem does not itself assemble
the primitives into the bounded k-selector. -/
theorem original_selector_primitives_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [CommRing G] [Fintype G]
      (hodd : Odd (Fintype.card G)) (hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ OriginalAdmitsEvents
          (selectorPrimitiveEvents hodd (by omega)
            (selectorBudget (p q) (Fintype.card G))) s} ≤
        Real.exp (-((xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N, hN⟩ := original_finite_events_probability (T := Fin 4) q hq0 hq1
    (fun _ ↦ 6) (![2,1,2,3] : Fin 4 → ℕ) (fun _ ↦ true)
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  have hnN : N ≤ Fintype.card G := (le_max_left N 2000).trans hn
  have hn2000 : 2000 ≤ Fintype.card G := (le_max_right N 2000).trans hn
  apply hN G hnN
    (selectorPrimitiveEvents hodd (by omega) (selectorBudget (p q) (Fintype.card G)))
  intro i
  simpa only [pqTailRate, ↓reduceIte] using
    selector_primitive_full_error q hq0 hq1 hodd hn2000 i

/-- One q-dependent threshold simultaneously pays the true common
primitive event and the 4000-coordinate margin over coloured selector construction's external budget.
The deterministic k-selector construction remains a separate step. -/
theorem selector_primitives_with_slack
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [CommRing G] [Fintype G]
      (hodd : Odd (Fintype.card G)) (hn : max N 2000 ≤ Fintype.card G),
      selectorExternalBudget (p q) (Fintype.card G) + 4000 ≤
        selectorBudget (p q) (Fintype.card G) ∧
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ OriginalAdmitsEvents
          (selectorPrimitiveEvents hodd (by omega)
            (selectorBudget (p q) (Fintype.card G))) s} ≤
        Real.exp (-((xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N1,hN1⟩ := original_selector_primitives_probability q hq0 hq1
  obtain ⟨N2,hN2⟩ := selector_external_budget_slack q hq0
  refine ⟨max N1 N2, ?_⟩
  intro G _ _ hodd hn
  constructor
  · exact hN2 (Fintype.card G) (by omega)
  · exact hN1 G hodd (by omega)

end
end EndpointSelector
