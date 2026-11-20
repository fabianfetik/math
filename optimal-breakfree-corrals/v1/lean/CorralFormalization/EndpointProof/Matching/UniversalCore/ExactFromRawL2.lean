import CorralFormalization.EndpointProof.Matching.UniversalCore.ExactFromRawSmallSquare
import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.ActualSquare

open MeasureTheory
open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.Fractional.Rounding
open EndpointMatching.Fractional.RobustWeights
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
noncomputable section
universe u

/-- uniform exact-matching theorem's complete physical probability and quantifier statement reduces
to one Fourier/L² bound on the actual raw matrix and the external AKS input.
No fractional-perfect or integral matching is assumed. -/
theorem original_exact_probability_of_raw_L2
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (∀ s : OriginalSample G, fractionalRawEvent q s →
        ∀ (W : Finset (Vertex G)) (hW : Balanced W),
          l2OperatorNorm (actualRawMatrix W hW (signedSets (rawTarget s)) q) ≤
            2 * epsilon q * (Fintype.card G : ℝ)) →
      (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
        {s | ¬ PhysicalExactEvent q s} ≤
        Real.exp (-((xi q)^4/10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := original_exact_probability_of_raw_smallSquare hAKS q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn hL2
  apply hN G hodd hn
  intro s hraw
  exact actualRawSmallSquare_of_l2 hq0 hq1 hraw (hL2 s hraw)

end
end EndpointMatching.UniversalCore
