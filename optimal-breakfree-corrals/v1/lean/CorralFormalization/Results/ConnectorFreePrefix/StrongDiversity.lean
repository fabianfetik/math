import CorralFormalization.Results.ConnectorFreePrefix.PrefixToOrbits
import CorralFormalization.Results.ConnectorFreePrefix.MatchingCompletion
import CorralFormalization.Results.ConnectorFreePrefix.LogarithmicBound
import CorralFormalization.Results.ConnectorPrefixAsymptotics

/-!
# Strong-floor diversity from endpoint completion and a literal prefix

The shared reductions use a cyclic endpoint theorem and a supplier for the
literal rainbow prefix. The matching-specific entry points obtain the former
from their explicit external inputs.
-/

open EndpointTransitions EndpointMatching.Fractional.Rounding
open CorralLatinTailMarker CorralFormalization.PhysicalCensus

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix

noncomputable section

/-- The only remaining own existence input in this reduction: the actual
printed `3*r^2+8` path is simple, nonzero and rainbow. -/
def LiteralRainbowPrefixSupply : Prop :=
  ∀ (n r : ℕ) [NeZero n] [NeZero r],
    3 ≤ r → Odd n → 200*r*r ≤ n →
      ∃ P : RainbowPrefix n, P.path = Construction.prefixPath n r

/-- At the literal stronger floor, the full physical census lower bound
follows from cyclic endpoint completion and the actual prefix supplier. No
physical-family or orbit-count premise is used. -/
theorem strong_floor_count_from_cyclic_and_prefix
    (hcyclic : OddCyclicRainbowEndpointCompletion)
    (hprefix : LiteralRainbowPrefixSupply) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) := by
  obtain ⟨ε0, hε0, n0, hendpoint⟩ := oddCyclicEndpointCompletion_iff.mp hcyclic
  refine ⟨ε0, hε0, n0, hendpoint, ?_⟩
  intro ε hεpos hε
  refine ⟨max 2 (max n0 ⌈34 / ε⌉₊), by omega, ?_⟩
  intro h hh
  let n := 2*h-1
  let r := radius ε n
  have hh2 : 2 ≤ h := by omega
  have hn0 : n0 ≤ n := by dsimp [n]; omega
  have hnN : ⌈34 / ε⌉₊ ≤ n := by dsimp [n]; omega
  have : NeZero h := ⟨by omega⟩
  have : NeZero n := ⟨by dsimp [n]; omega⟩
  have h34 : 34 ≤ ε * (n : ℝ) := by
    have hc : 34 / ε ≤ (⌈34 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hcast : (⌈34 / ε⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    have ht := (div_le_iff₀ hεpos).mp (hc.trans hcast)
    nlinarith
  obtain ⟨hr, hlarge300, _⟩ := radius_bounds (hε.trans (min_le_right _ _)) h34
  have hlarge : 200*r*r ≤ n := by dsimp [r]; nlinarith
  have : NeZero r := ⟨by dsimp [r]; omega⟩
  have : NeZero (h*n) := ⟨Nat.mul_ne_zero (NeZero.ne h) (NeZero.ne n)⟩
  have hodd : Odd n := by
    refine ⟨h-1, ?_⟩
    dsimp [n]
    omega
  obtain ⟨P,hpath⟩ := hprefix n r hr hodd hlarge
  have hlen : P.path.length = 3*radius ε n*radius ε n+8 := by
    rw [hpath, Construction.prefixPath_length]
  obtain ⟨Q⟩ := prefix_complementaryPath hendpoint hodd hn0 hε h34 P hlen
  have hcount := literal_prefix_census_of_completion hr (show n=2*h-1 from rfl) hlarge P Q hpath
  simpa only [n, r] using hcount

/-- The existing AKS/Pippenger entry point reuses the cyclic reduction. -/
theorem strong_floor_count_from_matching_and_prefix
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) (hprefix : LiteralRainbowPrefixSupply) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) := by
  exact strong_floor_count_from_cyclic_and_prefix
    (CorralFormalization.Results.cyclicCompletion_from_matching_inputs hAKS hPippenger) hprefix

/-- The stronger and older finite floors share one endpoint tolerance.
The `ε/3` logarithmic bound and Theta order additionally use the separately
stated published Latin-square estimate. -/
theorem strong_floor_diversity_from_cyclic_latin_and_prefix
    (hcyclic : OddCyclicRainbowEndpointCompletion)
    (hLatin : Asymptotic.LatinSquareFactorialBound) (hprefix : LiteralRainbowPrefixSupply) :
    (∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ,
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          (ε/3)*(h : ℝ)^2*Real.log (h : ℝ) -
            radiusErrorConstant ε*(h : ℝ)^2 ≤ Real.log (A_h h (hh0.trans hh) : ℝ)) ∧
    Asymptotics.IsTheta Filter.atTop Asymptotic.logAsymmetricCount Asymptotic.entropyScale := by
  obtain ⟨ε0,hε0,n0,hendpoint,hcount⟩ :=
    strong_floor_count_from_cyclic_and_prefix hcyclic hprefix
  constructor
  · refine ⟨ε0,hε0,n0,?_⟩
    intro ε hεpos hε
    obtain ⟨h1,hh1,hcount1⟩ := hcount ε hεpos hε
    obtain ⟨h2,hh2,hlog⟩ := radius_eventual_log_lower_of_count hLatin hεpos
      (hε.trans (min_le_right _ _)) ⟨h1,hh1,hcount1⟩
    obtain ⟨h3,hh3,hold⟩ := oddCyclicEndpointCompletionAt_floor_total_lower hendpoint hεpos hε
    refine ⟨max h1 (max h2 h3), by omega, ?_⟩
    intro h hh
    exact ⟨hcount1 h (by omega), hold h (by omega), hlog h (by omega)⟩
  · exact Asymptotic.oddCyclicEndpointCompletion_log_isTheta
      (oddCyclicEndpointCompletion_iff.mpr ⟨ε0,hε0,n0,hendpoint⟩) hLatin

/-- The existing AKS/Pippenger entry point reuses the cyclic reduction. -/
theorem strong_floor_diversity_from_matching_latin_and_prefix
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) (hLatin : Asymptotic.LatinSquareFactorialBound)
    (hprefix : LiteralRainbowPrefixSupply) :
    (∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ,
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          (ε/3)*(h : ℝ)^2*Real.log (h : ℝ) -
            radiusErrorConstant ε*(h : ℝ)^2 ≤ Real.log (A_h h (hh0.trans hh) : ℝ)) ∧
    Asymptotics.IsTheta Filter.atTop Asymptotic.logAsymmetricCount Asymptotic.entropyScale := by
  exact strong_floor_diversity_from_cyclic_latin_and_prefix
    (CorralFormalization.Results.cyclicCompletion_from_matching_inputs hAKS hPippenger)
    hLatin hprefix

end
end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix
