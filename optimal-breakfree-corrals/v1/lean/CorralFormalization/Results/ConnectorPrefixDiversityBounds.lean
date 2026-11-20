import CorralFormalization.Results.ConnectorPrefixAsymptotics

/-! A single paper-shaped theorem, with the cited Latin-square bound retained
as an explicit hypothesis alongside the cyclic endpoint-completion hypothesis. -/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.Asymptotic

open CorralLatinTailMarker PhysicalCensus

theorem oddCyclicEndpointCompletion_diversityBounds_with_latinSquareEstimate
    (H9 : OddCyclicRainbowEndpointCompletion) (HLatin : LatinSquareFactorialBound) :
    (∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          (ε/4)*(h : ℝ)^2*Real.log (h : ℝ) -
            radiusErrorConstant ε*(h : ℝ)^2 ≤
              Real.log (A_h h (hh0.trans hh) : ℝ)) ∧
    Asymptotics.IsTheta Filter.atTop logAsymmetricCount entropyScale := by
  constructor
  · obtain ⟨ε0,he0,n0,H0,Hlog⟩ := oddCyclicEndpointCompletion_floor_log_lower H9 HLatin
    refine ⟨ε0,he0,n0,H0,?_⟩
    intro ε hε0 hε1
    obtain ⟨h1,hh1,Hcount⟩ := oddCyclicEndpointCompletionAt_floor_total_lower H0 hε0 hε1
    obtain ⟨h2,hh2,Hlower⟩ := Hlog ε hε0 hε1
    refine ⟨max h1 h2, by omega, ?_⟩
    intro h hh
    exact ⟨Hcount h (by omega), Hlower h (by omega)⟩
  · exact oddCyclicEndpointCompletion_log_isTheta H9 HLatin

end CorralFormalization.LatinCompletion.TerraceCompletion.Asymptotic
