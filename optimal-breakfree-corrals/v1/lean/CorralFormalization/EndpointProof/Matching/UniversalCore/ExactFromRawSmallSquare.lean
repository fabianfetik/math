import CorralFormalization.EndpointProof.Matching.UniversalCore.ExactProbability
import CorralFormalization.EndpointProof.Matching.Fractional.ActualWeightsFromSmallSquare

open MeasureTheory
open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.ActualRemainder EndpointMatching.Fractional.Rounding
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
noncomputable section
universe u

/-- The physical exact-matching theorem, including simultaneous probability and
quantifiers, reduced to the precise raw small-square spectral estimate
and the explicit published AKS near-regular matching input. -/
theorem original_exact_probability_of_raw_smallSquare
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (∀ s : OriginalSample G, fractionalRawEvent q s → ActualRawSmallSquare q s) →
      (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
        {s | ¬ PhysicalExactEvent q s} ≤
        Real.exp (-((xi q)^4/10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := original_exact_probability_of_fractional_weights hAKS q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn hsmall
  apply hN G hodd hn
  intro s hraw
  apply actualFractionalWeights_of_raw_and_smallSquare q hq0 hq1 s hraw (hsmall s hraw) ∅
  intro z
  simp [banAt, beta]
  positivity

end
end EndpointMatching.UniversalCore
