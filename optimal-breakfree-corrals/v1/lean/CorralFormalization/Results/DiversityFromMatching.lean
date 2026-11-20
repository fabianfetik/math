import CorralFormalization.Results.CompletionFromMatching
import CorralFormalization.Results.ConnectorPrefixDiversityBounds

/-!
# The older formal diversity estimate from the external matching inputs

This explicitly composes the endpoint proof with the previously formalized
connector-prefix count and logarithmic deduction. The cited Latin-square
estimate remains a theorem argument; the stronger connector-free prefix is
not used or established here.
-/

open EndpointTransitions EndpointMatching.Fractional.Rounding
open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.TerraceCompletion.Asymptotic
open CorralLatinTailMarker
open CorralFormalization.PhysicalCensus
noncomputable section

namespace CorralFormalization.Results

/-- The older finite floor and logarithmic order follow from the external
AKS, Pippenger and labelled Latin-square estimates, with no separate endpoint
existence assumption. -/
theorem connector_diversity_from_matching_and_latin_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) (hLatin : LatinSquareFactorialBound) :
    (∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          (ε/4)*(h : ℝ)^2*Real.log (h : ℝ) -
            radiusErrorConstant ε*(h : ℝ)^2 ≤
              Real.log (A_h h (hh0.trans hh) : ℝ)) ∧
    Asymptotics.IsTheta Filter.atTop logAsymmetricCount entropyScale :=
  oddCyclicEndpointCompletion_diversityBounds_with_latinSquareEstimate
    (cyclicCompletion_from_matching_inputs hAKS hPippenger) hLatin

end CorralFormalization.Results
end
