import CorralFormalization.EndpointProof.Factor.PippengerCompletion
import CorralFormalization.Results.ConnectorFreePrefix.StrongDiversityTheorem
import CorralFormalization.Results.PathTerraceCompletion

/-! Consequences of the Pippenger-only endpoint theorem for the exact physical
finite diversity and its Latin-square-conditional logarithmic order. -/

open EndpointTransitions EndpointMatching.Fractional.Rounding
open CorralLatinTailMarker CorralFormalization.PhysicalCensus
open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix
open CorralFormalization.Results.PathTerraceCompletion

namespace EndpointPippenger
noncomputable section

theorem strong_floor_count_from_pippenger
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) := by
  have hcyclic := EndpointFactor.CycleCut.cyclicEndpointCompletion_of_uniformPhysical
    (uniformPhysicalEndpointCompletion_from_pippenger hPippenger)
  exact strong_floor_count_from_cyclic_and_prefix hcyclic literalRainbowPrefixSupply_proved

/-- The stronger finite floor, with no Latin-square-count assumption. -/
theorem strong_floor_main_pippenger
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) := by
  obtain ⟨ε0,hε0,n0,_,hcount⟩ := strong_floor_count_from_pippenger hPippenger
  exact ⟨ε0,hε0,hcount⟩

theorem strong_floor_diversity_from_pippenger_and_latin
    (hPippenger : PippengerTheorem.{0}) (hLatin : Asymptotic.LatinSquareFactorialBound) :
    (∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ,
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
          (ε/3)*(h : ℝ)^2*Real.log (h : ℝ) -
            radiusErrorConstant ε*(h : ℝ)^2 ≤ Real.log (A_h h (hh0.trans hh) : ℝ)) ∧
    Asymptotics.IsTheta Filter.atTop Asymptotic.logAsymmetricCount Asymptotic.entropyScale := by
  have hcyclic := EndpointFactor.CycleCut.cyclicEndpointCompletion_of_uniformPhysical
    (uniformPhysicalEndpointCompletion_from_pippenger hPippenger)
  exact strong_floor_diversity_from_cyclic_latin_and_prefix hcyclic hLatin literalRainbowPrefixSupply_proved

theorem uniform_endpoint_and_path_terrace_from_pippenger
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∃ Npath : ℕ,
        OddCyclicRainbowEndpointCompletionAt ε0 Npath ∧
        ∀ (n : ℕ), Odd n → Npath ≤ n →
          ∀ p : List (ZMod n),
            2 ≤ p.length → p.Nodup → (∀ x ∈ p, x ≠ 0) →
            (directedDifferences p).Nodup → (∀ d ∈ directedDifferences p, d ≠ 0) →
            ((p.length - 1 : ℕ) : ℝ) ≤ ε0 * (n : ℝ) →
            ∃ D : DirectedTerrace n,
              p <+: List.ofFn (fun i : Fin (n-1) => (D.vertices i).val) ∧
              pathGaps p <+: D.word := by
  obtain ⟨ε0, hε0, Nphysical, hphysical⟩ :=
    uniformPhysicalEndpointCompletion_from_pippenger hPippenger
  have hphysical' : UniformPhysicalEndpointCompletionAt ε0 Nphysical := hphysical
  obtain ⟨Npath, H⟩ := cyclicCompletionAt_of_uniformPhysicalAt hε0 hphysical'
  refine ⟨ε0, hε0, Nphysical, hphysical', Npath, H, ?_⟩
  intro n hodd hn0 p hlen hsimple hnonzero hrainbow hcolors hbudget
  have hnz : n ≠ 0 := by intro hn; subst n; norm_num at hodd
  have : NeZero n := ⟨hnz⟩
  exact path_terrace_of_cyclicCompletionAt H hodd hn0 p hlen hsimple hnonzero
    ((pathGaps_nodup_iff_directedDifferences p).mpr hrainbow)
    ((pathGaps_nonzero_iff_directedDifferences p).mpr hcolors) hbudget

theorem shared_tolerance_endpoint_path_and_finite_diversity_pippenger
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∃ Npath : ℕ,
        (∀ (n : ℕ), Odd n → Npath ≤ n →
          ∀ p : List (ZMod n),
            2 ≤ p.length → p.Nodup → (∀ x ∈ p, x ≠ 0) →
            (directedDifferences p).Nodup → (∀ d ∈ directedDifferences p, d ≠ 0) →
            ((p.length - 1 : ℕ) : ℝ) ≤ ε0 * (n : ℝ) →
            ∃ D : DirectedTerrace n,
              p <+: List.ofFn (fun i : Fin (n-1) => (D.vertices i).val) ∧
              pathGaps p <+: D.word) ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
          ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
            latinSquareCount
                (ConnectorFreePrefix.radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
            latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) := by
  obtain ⟨εpath, hεpath, Nphysical, hphysical, Npath, hcyclic, hpath⟩ :=
    uniform_endpoint_and_path_terrace_from_pippenger hPippenger
  obtain ⟨εcount, hεcount, _, _, hcount⟩ :=
    strong_floor_count_from_pippenger hPippenger
  refine ⟨min εpath εcount, lt_min hεpath hεcount, Nphysical,
    uniformPhysicalAt_of_smaller_tolerance hphysical (min_le_left _ _), Npath, ?_, ?_⟩
  · intro n hodd hn0 p hlen hsimple hnonzero hrainbow hcolors hbudget
    apply hpath n hodd hn0 p hlen hsimple hnonzero hrainbow hcolors
    exact hbudget.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  · intro ε hε hbound
    have hpathbound : ε ≤ min εpath ((1 : ℝ)/100) :=
      le_min ((le_min_iff.mp hbound).1.trans (min_le_left _ _)) (le_min_iff.mp hbound).2
    have hcountbound : ε ≤ min εcount ((1 : ℝ)/100) :=
      le_min ((le_min_iff.mp hbound).1.trans (min_le_right _ _)) (le_min_iff.mp hbound).2
    obtain ⟨h1, hh1, hstrong⟩ := hcount ε hε hcountbound
    obtain ⟨h2, hh2, hold⟩ := oddCyclicEndpointCompletionAt_floor_total_lower hcyclic hε hpathbound
    refine ⟨max h1 h2, by omega, ?_⟩
    intro h hh
    exact ⟨hstrong h (by omega), hold h (by omega)⟩

theorem shared_tolerance_endpoint_path_and_diversity_pippenger
    (hPippenger : PippengerTheorem.{0})
    (hLatin : Asymptotic.LatinSquareFactorialBound) :
    (∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∃ Npath : ℕ,
        (∀ (n : ℕ), Odd n → Npath ≤ n →
          ∀ p : List (ZMod n),
            2 ≤ p.length → p.Nodup → (∀ x ∈ p, x ≠ 0) →
            (directedDifferences p).Nodup → (∀ d ∈ directedDifferences p, d ≠ 0) →
            ((p.length - 1 : ℕ) : ℝ) ≤ ε0 * (n : ℝ) →
            ∃ D : DirectedTerrace n,
              p <+: List.ofFn (fun i : Fin (n-1) => (D.vertices i).val) ∧
              pathGaps p <+: D.word) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
          ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
            latinSquareCount
                (ConnectorFreePrefix.radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
            latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
            (ε/3)*(h : ℝ)^2*Real.log (h : ℝ) -
                ConnectorFreePrefix.radiusErrorConstant ε*(h : ℝ)^2 ≤
              Real.log (A_h h (hh0.trans hh) : ℝ))) ∧
      Asymptotics.IsTheta Filter.atTop Asymptotic.logAsymmetricCount Asymptotic.entropyScale := by
  obtain ⟨εpath, hεpath, Nphysical, hphysical, Npath, _, hpath⟩ :=
    uniform_endpoint_and_path_terrace_from_pippenger hPippenger
  obtain ⟨⟨εdiv, hεdiv, _, hdiv⟩, htheta⟩ :=
    strong_floor_diversity_from_pippenger_and_latin hPippenger hLatin
  refine ⟨⟨min εpath εdiv, lt_min hεpath hεdiv, Nphysical,
    uniformPhysicalAt_of_smaller_tolerance hphysical (min_le_left _ _), Npath, ?_, ?_⟩, htheta⟩
  · intro n hodd hn0 p hlen hsimple hnonzero hrainbow hcolors hbudget
    apply hpath n hodd hn0 p hlen hsimple hnonzero hrainbow hcolors
    exact hbudget.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  · intro ε hε hbound
    apply hdiv ε hε
    exact le_min ((le_min_iff.mp hbound).1.trans (min_le_right _ _)) (le_min_iff.mp hbound).2

end
end EndpointPippenger
