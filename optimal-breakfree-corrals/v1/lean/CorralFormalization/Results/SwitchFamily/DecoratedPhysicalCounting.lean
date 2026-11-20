import CorralFormalization.Results.SwitchFamily.DecoratedPhysicalOrbitCounts
import CorralFormalization.Results.SwitchFamily.Counting.BinomialFormula

/-!
# The physical A.3 count, existence, and logarithmic asymptotic

The actual physical-orbit quotient has already been proved in
`DecoratedPhysicalOrbitCounts`. Here the prescribed terrace is supplied for all
sufficiently large heights from the explicit external matching inputs,
and the physical census obtains the printed logarithmic consequence.
-/

open EndpointTransitions EndpointMatching.Fractional.Rounding
open CorralLatinTailMarker
open CorralFormalization.PhysicalCensus
open CorralFormalization.Results.SwitchFamily.Counting
open CorralFormalization.Results.SwitchFamily.Counting.DecoratedPhysicalCode
open CorralFormalization.Results.SwitchFamily.DecoratedPhysicalOrbitCounts
open CorralFormalization.Results.SwitchFamily.OrbitCorrespondence
open Filter Topology Finset
open scoped Topology

namespace CorralFormalization.Results.SwitchFamily.DecoratedPhysicalCounting

noncomputable section

def multiplicity (h : ℕ) : ℕ := switchMultiplicity (2*h-1)
def alphabet (h : ℕ) : ℕ := 2^(multiplicity h)
def primitiveOrbits (h : ℕ) : ℕ := aperiodicOrbitCount h (alphabet h)

def totalAsymmetric (h : ℕ) : ℕ := if hh : 2 ≤ h then A_h h hh else 0

/-- At this height the number `primitiveOrbits h` is realized by the
asymmetric physical equivalence classes of an actual constructed family. -/
def PhysicalRepresentativeAt (h : ℕ) (hh : 33 ≤ h) : Prop := by
  letI : NeZero h := ⟨by omega⟩
  letI : NeZero (2*h-1) := ⟨by omega⟩
  letI : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  exact ∃ D : CorralFormalization.LatinCompletion.TerraceCompletion.DirectedTerrace (2*h-1),
    ∃ hD : Prefix.PrescribedTerrace (multiplicity h) D,
      (asymmetricWordImage (anchoredDecoratedFamily hh D hD)).card = primitiveOrbits h

/-- The literal A9/A10 physical family counts at one height, with the
prescribed terrace and the constructed physical family included as witnesses. -/
def PhysicalExactAt (h : ℕ) (hh : 33 ≤ h) : Prop := by
  letI : NeZero h := ⟨by omega⟩
  letI : NeZero (2*h-1) := ⟨by omega⟩
  letI : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  exact ∃ D : CorralFormalization.LatinCompletion.TerraceCompletion.DirectedTerrace (2*h-1),
    ∃ hD : Prefix.PrescribedTerrace (multiplicity h) D,
      (Finset.univ.image (fun u => physicalOrbit (anchoredDecoratedFamily hh D hD u))).card =
        (∑ d ∈ h.divisors, Nat.totient d * C (h/d) * alphabet h^(h/d)) / h ∧
      (((asymmetricWordImage (anchoredDecoratedFamily hh D hD)).card : ℕ) : ℚ) =
        (∑ d ∈ h.divisors, (ArithmeticFunction.moebius d : ℚ) *
          (C (h/d) : ℚ) * (alphabet h : ℚ)^(h/d)) / (h : ℚ)

/-- The supplied terrace exists at each sufficiently large height. Together
with `exact_physical_family_counts`, this gives the paper's A.3 physical
families rather than only a count conditional on an arbitrary input. -/
theorem eventual_switch_terraces_from_matching
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ h0 : ℕ, 33 ≤ h0 ∧ ∀ h ≥ h0,
      ∃ D : CorralFormalization.LatinCompletion.TerraceCompletion.DirectedTerrace (2*h-1),
        Prefix.PrescribedTerrace (multiplicity h) D := by
  obtain ⟨ε,hε,Np,hp,Nq,hq,h0,hh0,hD⟩ :=
    Prefix.uniform_endpoint_and_appendix_terrace_from_matching_inputs hAKS hPippenger
  exact ⟨h0,hh0,hD⟩

theorem eventual_physical_representatives_from_matching
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ h0 : ℕ, ∃ hh0 : 33 ≤ h0, ∀ h (hh : h0 ≤ h),
      PhysicalRepresentativeAt h (le_trans hh0 hh) := by
  obtain ⟨h0,hh0,hD⟩ := eventual_switch_terraces_from_matching hAKS hPippenger
  refine ⟨h0,hh0,?_⟩
  intro h hh
  letI : NeZero h := ⟨by omega⟩
  letI : NeZero (2*h-1) := ⟨by omega⟩
  letI : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨D,hpre⟩ := hD h hh
  refine ⟨D,hpre,?_⟩
  simpa [primitiveOrbits,alphabet,multiplicity] using
    (physical_count_identification (le_trans hh0 hh) D hpre).2

theorem eventual_exact_physical_counts_from_matching
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ h0 : ℕ, ∃ hh0 : 33 ≤ h0, ∀ h (hh : h0 ≤ h),
      PhysicalExactAt h (le_trans hh0 hh) := by
  obtain ⟨h0,hh0,hD⟩ := eventual_switch_terraces_from_matching hAKS hPippenger
  refine ⟨h0,hh0,?_⟩
  intro h hh
  letI : NeZero h := ⟨by omega⟩
  letI : NeZero (2*h-1) := ⟨by omega⟩
  letI : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨D,hpre⟩ := hD h hh
  refine ⟨D,hpre,?_⟩
  simpa [alphabet,multiplicity] using exact_physical_family_counts (le_trans hh0 hh) D hpre

/-- The physical A.3 family is available at every sufficiently large height,
and its asymmetric count is a lower bound on the full physical census. -/
theorem eventual_primitive_count_le_census
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ h0 : ℕ, 33 ≤ h0 ∧ ∀ h ≥ h0, primitiveOrbits h ≤ totalAsymmetric h := by
  obtain ⟨h0,hh0,hD⟩ := eventual_switch_terraces_from_matching hAKS hPippenger
  refine ⟨h0,hh0,?_⟩
  intro h hh
  have hh33 : 33 ≤ h := le_trans hh0 hh
  letI : NeZero h := ⟨by omega⟩
  letI : NeZero (2*h-1) := ⟨by omega⟩
  letI : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨D,hpre⟩ := hD h hh
  have hc := aperiodic_count_le_total_census hh33 D hpre
  simpa [primitiveOrbits, alphabet, multiplicity, totalAsymmetric, show 2 ≤ h by omega] using hc

/-- The varying alphabet is held fixed at each height inside every divisor
term; its actual primitive physical orbit count has the printed asymptotic. -/
theorem primitive_physical_asymptotic :
    Tendsto (fun h : ℕ => ((primitiveOrbits h : ℝ)*h)/
      (LayoutAsymptotic.plasticRoot*(alphabet h : ℝ))^h) atTop (𝓝 1) := by
  simpa [primitiveOrbits] using
    LayoutAsymptotic.decorated_aperiodic_orbit_asymptotic alphabet
      (fun h => Nat.one_le_pow (multiplicity h) 2 (by omega))

/-- The A.3 physical census bound with an explicit vanishing error sequence.
Only the two published matching inputs remain ordinary theorem arguments. -/
theorem physical_logarithmic_bound_from_matching
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ (h : ℕ) in atTop, ∃ hh : 2 ≤ h,
        (h : ℝ)*(multiplicity h : ℝ) + (h : ℝ)*Real.logb 2 LayoutAsymptotic.plasticRoot -
          Real.logb 2 (h : ℝ) - err h ≤ Real.logb 2 (A_h h hh : ℝ) := by
  obtain ⟨h0,hh0,hbound⟩ := eventual_primitive_count_le_census hAKS hPippenger
  have hb : ∀ᶠ h in atTop, primitiveOrbits h ≤ totalAsymmetric h := by
    filter_upwards [Filter.eventually_ge_atTop h0] with h hh
    exact hbound h hh
  have ht : Tendsto (fun h : ℕ => ((primitiveOrbits h : ℝ)*h)/
      (LayoutAsymptotic.plasticRoot*(2:ℝ)^(multiplicity h))^h) atTop (𝓝 1) := by
    simpa [alphabet, Nat.cast_pow] using primitive_physical_asymptotic
  obtain ⟨err,herr,hlog⟩ := OrbitLogarithmic.logarithmic_lower_from_asymptotic
    totalAsymmetric primitiveOrbits multiplicity LayoutAsymptotic.plasticRoot_bounds.1 ht hb
  refine ⟨err,herr,?_⟩
  filter_upwards [hlog,Filter.eventually_ge_atTop 2] with h hhlog hh
  refine ⟨hh,?_⟩
  simpa [totalAsymmetric,hh] using hhlog

/-- The paper-shaped A.3 conclusion: its literal A8 formula, eventual
actual physical A9/A10 counts, asymptotic primitive count and final census
logarithmic bound, all combined from the two external matching inputs. -/
theorem decorated_physical_counting_from_matching
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
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
        (h : ℝ)*(multiplicity h : ℝ) + (h : ℝ)*Real.logb 2 LayoutAsymptotic.plasticRoot -
          Real.logb 2 (h : ℝ) - err h ≤ Real.logb 2 (A_h h hh : ℝ)) :=
  ⟨C_binomial_formula_A8, eventual_exact_physical_counts_from_matching hAKS hPippenger,
    primitive_physical_asymptotic, physical_logarithmic_bound_from_matching hAKS hPippenger⟩

end
end CorralFormalization.Results.SwitchFamily.DecoratedPhysicalCounting
