import CorralFormalization.EndpointProof.Factor.CycleExpansion.Prepared

/-!
# Uniform physical endpoint completion

The fixed sample and its actual contracted closure are constructed before
the target is presented.  Expanding that closure gives the paper's physical
cycle or path factor.  The two cited matching results remain explicit inputs.
-/

open scoped BigOperators Classical
namespace EndpointFactor
open EndpointLayeredSample EndpointTransitions EndpointMatching.Fractional.Rounding
noncomputable section
universe u

/-- The paper's odd-abelian physical endpoint conclusion, under the explicitly
formulated AKS set-family and Pippenger matching inputs.  The same proof
works for any admissible paper parameter `r`. -/
theorem uniformPhysicalEndpointCompletion_of_AKS_Pippenger
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (hPippenger : PippengerTheorem.{u})
    (r : ℝ) (hr : 0 < r) (hr10 : r ≤ 1/10) :
    CycleCut.UniformPhysicalEndpointCompletion.{u} := by
  obtain ⟨T, hTeven, hTL, m, hm, hkT, dist, hdr, hq, hqr, hqk, hq3,
    μ, hμ, hμhalf, hε, N, hsample⟩ :=
    Allocation.exists_uniform_common_sample_and_contracted_closure
      hAKS hPippenger r hr hr10
  unfold CycleCut.UniformPhysicalEndpointCompletion
  refine ⟨_, hε, N, ?_⟩
  intro G _ _ hodd hn W D X Y hX hY hXY hXYcard hK hW hDzero hD hsum
  obtain ⟨sample, _, _, _, htargets⟩ := hsample G hodd hn
  exact CycleExpansion.endpointConclusion_of_preparedWithContractedClosure
    (htargets W D X Y hX hY hXY hXYcard hK hW hD hDzero hsum)

/-- A closed parameter choice.  The two published inputs remain visible in
the theorem statement; no endpoint or physical-cycle existence is assumed. -/
theorem uniformPhysicalEndpointCompletion_from_AKS_Pippenger
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (hPippenger : PippengerTheorem.{u}) :
    CycleCut.UniformPhysicalEndpointCompletion.{u} := by
  apply uniformPhysicalEndpointCompletion_of_AKS_Pippenger hAKS hPippenger (1/100)
  · norm_num
  · norm_num

end
end EndpointFactor
