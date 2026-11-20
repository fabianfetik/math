import CorralFormalization.Results.PippengerDiversity
import CorralFormalization.Results.SwitchFamily.AsymmetricSwitchFamily
import CorralFormalization.Results.SwitchFamily.DecoratedPhysicalCounting

/-! Pippenger-only consequences for the prescribed switch terraces and their
physical orbit counts. The quantitative AKS remainder is a separate result. -/

open EndpointTransitions EndpointMatching.Fractional.Rounding
open CorralLatinTailMarker
open CorralFormalization.PhysicalCensus
open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.GeneralTiles
open CorralFormalization.Results.PathTerraceCompletion
open CorralFormalization.Results.SwitchFamily
open CorralFormalization.Results.SwitchFamily.Prefix
open CorralFormalization.Results.SwitchFamily.FamilySwitches
open CorralFormalization.Results.SwitchFamily.CanonicalLayouts
open CorralFormalization.Results.SwitchFamily.Counting
open CorralFormalization.Results.SwitchFamily.Counting.DecoratedPhysicalCode
open CorralFormalization.Results.SwitchFamily.DecoratedPhysicalOrbitCounts
open CorralFormalization.Results.SwitchFamily.DecoratedPhysicalCounting
open CorralFormalization.Results.SwitchFamily.OrbitCorrespondence
open Filter Topology Finset
open scoped Topology

namespace EndpointPippenger
noncomputable section

theorem uniform_endpoint_and_appendix_terrace_from_pippenger
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∃ Npath : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 Npath ∧
      ∃ h0 : ℕ, 33 ≤ h0 ∧ ∀ h : ℕ, h0 ≤ h →
        ∃ D : DirectedTerrace (2*h-1), PrescribedTerrace (count (2*h-1)) D := by
  obtain ⟨ε0,hε0,Nphysical,hphysical⟩ :=
    uniformPhysicalEndpointCompletion_from_pippenger hPippenger
  have hphysical' : UniformPhysicalEndpointCompletionAt ε0 Nphysical := hphysical
  obtain ⟨Npath,H⟩ := cyclicCompletionAt_of_uniformPhysicalAt hε0 hphysical'
  exact ⟨ε0,hε0,Nphysical,hphysical',Npath,H,eventual_height_terrace_of_endpointAt hε0 H⟩


theorem switch_family_from_pippenger
    (hPippenger : PippengerTheorem.{0})
    :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∃ Npath : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 Npath ∧
      ∃ h0 : ℕ, ∃ hh0 : 33 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
        2^(h * switchMultiplicity (2*h-1)) ≤ A_h h (by omega) ∧
        (Real.sqrt 2 / 5) * (h : ℝ)^((3 : ℝ)/2) - (14 / 5) * (h : ℝ) ≤
          Real.logb 2 (A_h h (by omega) : ℝ) := by
  obtain ⟨ε0,hε0,Nphysical,hphysical,Npath,H,h0,hh0,hterrace⟩ :=
    uniform_endpoint_and_appendix_terrace_from_pippenger hPippenger
  refine ⟨ε0,hε0,Nphysical,hphysical,Npath,H,h0,hh0,?_⟩
  intro h hh
  have hh33 : 33 ≤ h := hh0.trans hh
  have : NeZero h := ⟨by omega⟩
  have : NeZero (2*h-1) := ⟨by omega⟩
  have : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨D,hD⟩ := hterrace h hh
  obtain ⟨a,b,htotal,p,hthree⟩ := fixed_layout_exists h (by omega)
  exact count_and_log_from_actual_row_modifications hh33 D hD.1 (fromBlocks htotal) p hthree
    (canonical_row_modification_supply_proved h hh33 D hD a b htotal)


theorem eventual_switch_terraces_from_pippenger
    (hPippenger : PippengerTheorem.{0}) :
    ∃ h0 : ℕ, 33 ≤ h0 ∧ ∀ h ≥ h0,
      ∃ D : CorralFormalization.LatinCompletion.TerraceCompletion.DirectedTerrace (2*h-1),
        Prefix.PrescribedTerrace (DecoratedPhysicalCounting.multiplicity h) D := by
  obtain ⟨ε,hε,Np,hp,Nq,hq,h0,hh0,hD⟩ :=
    uniform_endpoint_and_appendix_terrace_from_pippenger hPippenger
  exact ⟨h0,hh0,hD⟩


theorem eventual_physical_representatives_from_pippenger
    (hPippenger : PippengerTheorem.{0}) :
    ∃ h0 : ℕ, ∃ hh0 : 33 ≤ h0, ∀ h (hh : h0 ≤ h),
      PhysicalRepresentativeAt h (le_trans hh0 hh) := by
  obtain ⟨h0,hh0,hD⟩ := eventual_switch_terraces_from_pippenger hPippenger
  refine ⟨h0,hh0,?_⟩
  intro h hh
  letI : NeZero h := ⟨by omega⟩
  letI : NeZero (2*h-1) := ⟨by omega⟩
  letI : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨D,hpre⟩ := hD h hh
  refine ⟨D,hpre,?_⟩
  simpa [primitiveOrbits,alphabet,DecoratedPhysicalCounting.multiplicity] using
    (physical_count_identification (le_trans hh0 hh) D hpre).2


theorem eventual_exact_physical_counts_from_pippenger
    (hPippenger : PippengerTheorem.{0}) :
    ∃ h0 : ℕ, ∃ hh0 : 33 ≤ h0, ∀ h (hh : h0 ≤ h),
      PhysicalExactAt h (le_trans hh0 hh) := by
  obtain ⟨h0,hh0,hD⟩ := eventual_switch_terraces_from_pippenger hPippenger
  refine ⟨h0,hh0,?_⟩
  intro h hh
  letI : NeZero h := ⟨by omega⟩
  letI : NeZero (2*h-1) := ⟨by omega⟩
  letI : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨D,hpre⟩ := hD h hh
  refine ⟨D,hpre,?_⟩
  simpa [alphabet,DecoratedPhysicalCounting.multiplicity] using exact_physical_family_counts (le_trans hh0 hh) D hpre


theorem eventual_primitive_count_le_census_from_pippenger
    (hPippenger : PippengerTheorem.{0}) :
    ∃ h0 : ℕ, 33 ≤ h0 ∧ ∀ h ≥ h0, primitiveOrbits h ≤ totalAsymmetric h := by
  obtain ⟨h0,hh0,hD⟩ := eventual_switch_terraces_from_pippenger hPippenger
  refine ⟨h0,hh0,?_⟩
  intro h hh
  have hh33 : 33 ≤ h := le_trans hh0 hh
  letI : NeZero h := ⟨by omega⟩
  letI : NeZero (2*h-1) := ⟨by omega⟩
  letI : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨D,hpre⟩ := hD h hh
  have hc := aperiodic_count_le_total_census hh33 D hpre
  simpa [primitiveOrbits, alphabet, DecoratedPhysicalCounting.multiplicity, totalAsymmetric, show 2 ≤ h by omega] using hc


theorem physical_logarithmic_bound_from_pippenger
    (hPippenger : PippengerTheorem.{0}) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ (h : ℕ) in atTop, ∃ hh : 2 ≤ h,
        (h : ℝ)*(DecoratedPhysicalCounting.multiplicity h : ℝ) + (h : ℝ)*Real.logb 2 LayoutAsymptotic.plasticRoot -
          Real.logb 2 (h : ℝ) - err h ≤ Real.logb 2 (A_h h hh : ℝ) := by
  obtain ⟨h0,hh0,hbound⟩ := eventual_primitive_count_le_census_from_pippenger hPippenger
  have hb : ∀ᶠ h in atTop, primitiveOrbits h ≤ totalAsymmetric h := by
    filter_upwards [Filter.eventually_ge_atTop h0] with h hh
    exact hbound h hh
  have ht : Tendsto (fun h : ℕ => ((primitiveOrbits h : ℝ)*h)/
      (LayoutAsymptotic.plasticRoot*(2:ℝ)^(DecoratedPhysicalCounting.multiplicity h))^h) atTop (𝓝 1) := by
    simpa [alphabet, Nat.cast_pow] using primitive_physical_asymptotic
  obtain ⟨err,herr,hlog⟩ := OrbitLogarithmic.logarithmic_lower_from_asymptotic
    totalAsymmetric primitiveOrbits DecoratedPhysicalCounting.multiplicity LayoutAsymptotic.plasticRoot_bounds.1 ht hb
  refine ⟨err,herr,?_⟩
  filter_upwards [hlog,Filter.eventually_ge_atTop 2] with h hhlog hh
  refine ⟨hh,?_⟩
  simpa [totalAsymmetric,hh] using hhlog


theorem decorated_physical_counting_from_pippenger
    (hPippenger : PippengerTheorem.{0}) :
    (∀ j : ℕ, 0 < j → (C j : ℚ) =
      ∑ ab ∈ ((range (j+1)) ×ˢ (range (j+1))).filter
        (fun ab : ℕ × ℕ => 2*ab.1+3*ab.2=j),
        (j : ℚ)/((ab.1+ab.2 : ℕ) : ℚ)*(Nat.choose (ab.1+ab.2) ab.1 : ℚ)) ∧
    (∃ h0 : ℕ, ∃ hh0 : 33 ≤ h0, ∀ h (hh : h0 ≤ h), PhysicalExactAt h (le_trans hh0 hh)) ∧
    Tendsto (fun h : ℕ => ((primitiveOrbits h : ℝ)*h)/
      (LayoutAsymptotic.plasticRoot*(alphabet h : ℝ))^h) atTop (𝓝 1) ∧
    (∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ (h : ℕ) in atTop, ∃ hh : 2 ≤ h,
        (h : ℝ)*(DecoratedPhysicalCounting.multiplicity h : ℝ) + (h : ℝ)*Real.logb 2 LayoutAsymptotic.plasticRoot -
          Real.logb 2 (h : ℝ) - err h ≤ Real.logb 2 (A_h h hh : ℝ)) :=
  ⟨C_binomial_formula_A8, eventual_exact_physical_counts_from_pippenger hPippenger,
    primitive_physical_asymptotic, physical_logarithmic_bound_from_pippenger hPippenger⟩


end
end EndpointPippenger
