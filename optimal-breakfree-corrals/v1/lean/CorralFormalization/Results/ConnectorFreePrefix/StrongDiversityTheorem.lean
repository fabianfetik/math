import CorralFormalization.Results.ConnectorFreePrefix.StrongDiversity
import CorralFormalization.Results.ConnectorFreePrefix.Construction.RainbowPrefix

/-!
# The stronger diversity theorem from explicit external matching inputs

The explicit Walecki prefix now supplies the final own existence argument of
the stronger-floor chain. The only theorem inputs of the resulting finite
count are the AKS and Pippenger matching statements; the logarithmic version
also takes the cited Latin-square estimate as an external theorem input.
-/

open EndpointTransitions EndpointMatching.Fractional.Rounding
open CorralLatinTailMarker CorralFormalization.PhysicalCensus

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix

noncomputable section

/-- The literal printed path supplies the formerly separate prefix input. -/
theorem literalRainbowPrefixSupply_proved : LiteralRainbowPrefixSupply := by
  intro n r _ _ hr _ hn
  obtain ⟨P,hpath,_,_,_⟩ := Construction.rainbowPrefix_exists hr hn
  exact ⟨P,hpath⟩

/-- The finite physical census lower bound at the exact stronger floor.
No endpoint, prefix, physical-frame or orbit-existence assumption remains. -/
theorem strong_floor_count_from_matching_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) := by
  obtain ⟨ε0,hε0,n0,_,hcount⟩ :=
    strong_floor_count_from_matching_and_prefix hAKS hPippenger literalRainbowPrefixSupply_proved
  exact ⟨ε0,hε0,hcount⟩

/-- Both finite floors share a single endpoint tolerance. The `ε/3` lower
bound is stated with an explicit quadratic error constant, and the full
Theta order follows from the cited Latin-square estimate. -/
theorem strong_diversity_from_matching_and_latin_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) (hLatin : Asymptotic.LatinSquareFactorialBound) :
    (∃ ε0 : ℝ, 0 < ε0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          (ε/3)*(h : ℝ)^2*Real.log (h : ℝ) -
            radiusErrorConstant ε*(h : ℝ)^2 ≤ Real.log (A_h h (hh0.trans hh) : ℝ)) ∧
    Asymptotics.IsTheta Filter.atTop Asymptotic.logAsymmetricCount Asymptotic.entropyScale := by
  obtain ⟨⟨ε0,hε0,n0,hbound⟩,htheta⟩ :=
    strong_floor_diversity_from_matching_latin_and_prefix
      hAKS hPippenger hLatin literalRainbowPrefixSupply_proved
  exact ⟨⟨ε0,hε0,hbound⟩,htheta⟩

end
end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix
