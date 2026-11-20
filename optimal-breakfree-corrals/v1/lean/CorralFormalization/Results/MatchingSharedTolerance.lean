import CorralFormalization.Results.PathTerraceCompletion

/-! A common tolerance for the AKS/Pippenger endpoint theorem and the
stronger and older finite diversity floors. -/

open EndpointTransitions EndpointMatching.Fractional.Rounding
open CorralLatinTailMarker CorralFormalization.PhysicalCensus
open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix
open CorralFormalization.Results.PathTerraceCompletion

namespace CorralFormalization.Results.MatchingSharedTolerance
noncomputable section

/-- The endpoint and both finite diversity floors share a tolerance without
the external asymptotic estimate for the number of Latin squares. -/
theorem endpoint_and_finite_diversity_from_matching_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) := by
  have hfull := EndpointFactor.uniformPhysicalEndpointCompletion_from_AKS_Pippenger hAKS hPippenger
  have hcyclic := EndpointFactor.CycleCut.cyclicEndpointCompletion_of_uniformPhysical hfull
  obtain ⟨εpath, hεpath, Nphysical, hphysical⟩ := hfull
  have hphysical' : UniformPhysicalEndpointCompletionAt εpath Nphysical := hphysical
  obtain ⟨εdiv, hεdiv, _, hendpoint, hstrong⟩ :=
    strong_floor_count_from_cyclic_and_prefix hcyclic literalRainbowPrefixSupply_proved
  refine ⟨min εpath εdiv, lt_min hεpath hεdiv, Nphysical,
    uniformPhysicalAt_of_smaller_tolerance hphysical' (min_le_left _ _), ?_⟩
  intro ε hε hbound
  have hdivbound : ε ≤ min εdiv ((1 : ℝ)/100) :=
    le_min ((le_min_iff.mp hbound).1.trans (min_le_right _ _)) (le_min_iff.mp hbound).2
  obtain ⟨h1, hh1, hfirst⟩ := hstrong ε hε hdivbound
  obtain ⟨h2, hh2, hsecond⟩ := oddCyclicEndpointCompletionAt_floor_total_lower hendpoint hε hdivbound
  refine ⟨max h1 h2, by omega, ?_⟩
  intro h hh
  exact ⟨hfirst h (by omega), hsecond h (by omega)⟩

/-- The same shared endpoint and floors, with the logarithmic and Theta
conclusions from the separately stated Latin-square lower bound. -/
theorem endpoint_and_diversity_from_matching_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) (hLatin : Asymptotic.LatinSquareFactorialBound) :
    (∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          (ε/3)*(h : ℝ)^2*Real.log (h : ℝ) - radiusErrorConstant ε*(h : ℝ)^2 ≤
            Real.log (A_h h (hh0.trans hh) : ℝ)) ∧
      Asymptotics.IsTheta Filter.atTop Asymptotic.logAsymmetricCount Asymptotic.entropyScale := by
  have hfull := EndpointFactor.uniformPhysicalEndpointCompletion_from_AKS_Pippenger hAKS hPippenger
  have hcyclic := EndpointFactor.CycleCut.cyclicEndpointCompletion_of_uniformPhysical hfull
  obtain ⟨εpath, hεpath, Nphysical, hphysical⟩ := hfull
  have hphysical' : UniformPhysicalEndpointCompletionAt εpath Nphysical := hphysical
  obtain ⟨⟨εdiv, hεdiv, _, hdiv⟩, htheta⟩ :=
    strong_floor_diversity_from_cyclic_latin_and_prefix hcyclic hLatin literalRainbowPrefixSupply_proved
  refine ⟨⟨min εpath εdiv, lt_min hεpath hεdiv, Nphysical,
    uniformPhysicalAt_of_smaller_tolerance hphysical' (min_le_left _ _), ?_⟩, htheta⟩
  intro ε hε hbound
  apply hdiv ε hε
  exact le_min ((le_min_iff.mp hbound).1.trans (min_le_right _ _)) (le_min_iff.mp hbound).2

end
end CorralFormalization.Results.MatchingSharedTolerance
