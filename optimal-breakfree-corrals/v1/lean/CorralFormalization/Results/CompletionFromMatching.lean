import CorralFormalization.EndpointProof.Factor.UniformPhysicalCompletion
import CorralFormalization.EndpointProof.Factor.CycleCompletion

/-!
# From the two external matching inputs to the cyclic corral receiver

The endpoint theorem's own existence is no longer a premise here.  The
two matching source statements remain visible.  The older connector-prefix
floor below is already formalized; it is not the stronger connector-free floor.
-/

open EndpointTransitions EndpointMatching.Fractional.Rounding
open CorralFormalization.LatinCompletion.TerraceCompletion
noncomputable section

namespace CorralFormalization.Results

/-- The cyclic completion required by the corral construction follows from
the physical odd-abelian theorem, with the original external inputs visible. -/
theorem cyclicCompletion_from_matching_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) : OddCyclicRainbowEndpointCompletion :=
  EndpointFactor.CycleCut.cyclicEndpointCompletion_of_uniformPhysical
    (EndpointFactor.uniformPhysicalEndpointCompletion_from_AKS_Pippenger hAKS hPippenger)

/-- The previously formalized connector-prefix count with no separate
endpoint-existence hypothesis.  This is the older, weaker floor. -/
theorem connector_floor_from_matching_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ) / 100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          CorralLatinTailMarker.latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤
            CorralFormalization.PhysicalCensus.A_h h (hh0.trans hh) :=
  oddCyclicEndpointCompletion_floor_total_lower
    (cyclicCompletion_from_matching_inputs hAKS hPippenger)

end CorralFormalization.Results
end
