import CorralFormalization.Results.SwitchFamily.EventualSwitchFamily
import CorralFormalization.Results.SwitchFamily.Physical.Simultaneous

/-!
# The full Appendix A.2 switch-family theorem

The concrete simultaneous row modifications discharge the final physical
supplier. The resulting theorem retains only the cited AKS and Pippenger
inputs used to construct the prescribed terrace; there is no matching,
marker, switch, orbit or final-count supplier among its arguments.
-/

open EndpointTransitions EndpointMatching.Fractional.Rounding
open CorralFormalization.PhysicalCensus
open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.Results.PathTerraceCompletion
open CorralFormalization.Results.SwitchFamily.CanonicalLayouts

namespace CorralFormalization.Results.SwitchFamily

noncomputable section

/-- The literal all-height physical modification obligation is proved by
the concrete positive-word and simultaneous-site construction. -/
theorem canonical_row_modification_supply_proved : CanonicalRowModificationSupply := by
  intro h _ _ _ hh D hD a b htotal U hU
  have hs : (5*Prefix.count (2*h-1)+8)^2 ≤ 2*h-1 :=
    Prefix.count_square_bound (by omega)
  have hm := Physical.explicit_actual_row_modification D rfl (by omega) hs hD (fromBlocks htotal) U
  exact hm

/-- The complete A.2 finite lower bound and explicit logarithmic consequence,
for every sufficiently large height and at a tolerance shared with the
full odd-abelian endpoint theorem. -/
theorem switch_family_theorem_from_matching_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∃ Npath : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 Npath ∧
      ∃ h0 : ℕ, ∃ hh0 : 33 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
        2^(h * switchMultiplicity (2*h-1)) ≤ A_h h (by omega) ∧
        (Real.sqrt 2 / 5) * (h : ℝ)^((3 : ℝ)/2) - (14 / 5) * (h : ℝ) ≤
          Real.logb 2 (A_h h (by omega) : ℝ) :=
  eventual_switch_family_from_matching_and_modifications hAKS hPippenger
    canonical_row_modification_supply_proved

end
end CorralFormalization.Results.SwitchFamily
