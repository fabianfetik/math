import CorralFormalization.Results.SwitchFamily.SwitchCountFromModifications
import CorralFormalization.Results.SwitchFamily.CanonicalLayouts

/-!
# Quantifier-level assembly for the Appendix A switch family

The definition below exposes the sole pending physical input: every actual
switch-set is realized by palette- and edge-preserving modifications of the
actual canonical rows. The prescribed terrace, concrete sites, owner
distinction, marker isolation, chosen fixed layout, orbital counting and
floor/logarithm estimates are all paid by earlier proved theorems.
-/

open EndpointTransitions EndpointMatching.Fractional.Rounding
open CorralFormalization.PhysicalCensus
open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.GeneralTiles
open CorralFormalization.Results.PathTerraceCompletion
open CorralFormalization.Results.SwitchFamily.FamilySwitches
open CorralFormalization.Results.SwitchFamily.CanonicalLayouts

namespace CorralFormalization.Results.SwitchFamily

noncomputable section

/-- Concrete physical obligation: realize every chosen set of actual
Appendix A pairs on every prescribed terrace and canonical phase tiling.
This is not itself an existence proof of the modifications. -/
def CanonicalRowModificationSupply : Prop :=
  ∀ (h : ℕ) [NeZero h] [NeZero (2*h-1)] [NeZero (h*(2*h-1))]
    (hh : 33 ≤ h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (Prefix.count (2*h-1)) D)
    (a b : ℕ) (htotal : h=3*a+2*b),
      ∀ U ∈ (explicitSwitchLayer hh).edges.toFinset.powerset,
        ∃ P : RowModification (2*h-1)
            ((fromBlocks htotal).family (completedOfSpecifiedPrefix D (by omega) hD.1)),
          P.family = switchedFamily (explicitSwitchLayer hh)
            ((fromBlocks htotal).family (completedOfSpecifiedPrefix D (by omega) hD.1)) U

/-- The complete finite and logarithmic A.2 conclusions follow at all large
heights from AKS, Pippenger, and the explicitly stated physical modification
supplier. The endpoint tolerance is the same as the full odd-abelian result. -/
theorem eventual_switch_family_from_matching_and_modifications
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0})
    (hmod : CanonicalRowModificationSupply) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∃ Npath : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 Npath ∧
      ∃ h0 : ℕ, ∃ hh0 : 33 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
        2^(h * switchMultiplicity (2*h-1)) ≤ A_h h (by omega) ∧
        (Real.sqrt 2 / 5) * (h : ℝ)^((3 : ℝ)/2) - (14 / 5) * (h : ℝ) ≤
          Real.logb 2 (A_h h (by omega) : ℝ) := by
  obtain ⟨ε0,hε0,Nphysical,hphysical,Npath,H,h0,hh0,hterrace⟩ :=
    Prefix.uniform_endpoint_and_appendix_terrace_from_matching_inputs hAKS hPippenger
  refine ⟨ε0,hε0,Nphysical,hphysical,Npath,H,h0,hh0,?_⟩
  intro h hh
  have hh33 : 33 ≤ h := hh0.trans hh
  have : NeZero h := ⟨by omega⟩
  have : NeZero (2*h-1) := ⟨by omega⟩
  have : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨D,hD⟩ := hterrace h hh
  obtain ⟨a,b,htotal,p,hthree⟩ := fixed_layout_exists h (by omega)
  exact count_and_log_from_actual_row_modifications hh33 D hD.1 (fromBlocks htotal) p hthree
    (hmod h hh33 D hD a b htotal)

end
end CorralFormalization.Results.SwitchFamily
