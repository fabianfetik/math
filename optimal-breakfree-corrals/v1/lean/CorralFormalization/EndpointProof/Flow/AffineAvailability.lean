import CorralFormalization.EndpointProof.Probability.FiniteEventAvailability
import CorralFormalization.EndpointProof.Flow.UniversalSupply

/-!
Actual Q availability for every fresh nine-orbit affine flow candidate,
all three layouts, all tag permutations, and the padded exceptional query.
Whether every legal six-root input has one of these layouts remains a
separate deterministic supplier obligation.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

namespace EndpointFlow

open EndpointFullProduct EndpointOriginalReservoir EndpointBlockAvailability
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

/-- A single Q event for every admissible affine layout and every later
forbidden set within the stated numerical budget. -/
def affineFlowEvent (hodd : Odd (Fintype.card G))
    (hn : 1000 ≤ Fintype.card G) (budget : ℕ) (ω : FullSample G) : Prop :=
  FullAvailable (affineEmbedding hodd hn) (fun r _ ↦ affineDemand r) budget ω

/-- Literal exact-matching parameters and packing-budget budget for the actual affine Q packings,
including all six part permutations. The query count is at most `18 n⁶`. -/
theorem affine_flow_full_error
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G) :
    (parameterizedFullMeasure G q hq0 hq1).real
      {ω | ¬ affineFlowEvent hodd (by omega)
        (flowBudget (tau q) (Fintype.card G)) ω} ≤
      18 * (Fintype.card G : ℝ)^6 *
        Real.exp (-((tau q)^18 / 32000) * (Fintype.card G : ℝ)) := by
  obtain ⟨hη0,hη1,ha,hb,hab,_,hcat,hP,hQ⟩ :=
    samplingParameters_admissible q hq0 hq1
  have hτ0 : 0 < (tauNN q : ℝ) := by
    change 0 < tau q
    unfold tau p SamplingConstants.rho eta
    positivity
  have hh := full_sample_nine_orbit_budget hodd hn q eta (1/4)
    (tau q / SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
    (pNN q) (tauNN q) hτ0 hcat hP hQ (affineEmbedding hodd (by omega))
    (fun r _ ↦ affineDemand r) (by simp)
    (fun r _ ↦ (affineDemand_probability (pNN q) (tauNN q) r).ge)
  have hcard : (Fintype.card (AffineQuery G) : ℝ) ≤ 18*(Fintype.card G : ℝ)^6 := by
    exact_mod_cast (affineQuery_card_le (G := G))
  have hτNN : (tauNN q : ℝ) = tau q := rfl
  rw [hτNN] at hh
  have hbound := hh.trans (mul_le_mul_of_nonneg_right hcard (le_of_lt (Real.exp_pos _)))
  simpa [parameterizedFullMeasure, affineFlowEvent] using hbound

end
end EndpointFlow
