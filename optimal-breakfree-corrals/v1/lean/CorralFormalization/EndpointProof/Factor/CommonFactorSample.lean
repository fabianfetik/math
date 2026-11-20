import CorralFormalization.EndpointProof.Factor.FactorParameters
import CorralFormalization.EndpointProof.Probability.LayeredSample.RouterReservoir

/-!
# The paper's fixed constants on one augmented sample

This instantiates the proved common event at the actual order of choices in
the path-factor construction. It does not construct the later layer fills or the complete router.
-/

namespace EndpointLayeredSample

open EndpointMatching.Fractional.Rounding EndpointTransitions
noncomputable section
universe u

/-- The two paper lower bounds for its even parameter `T`. -/
def explicitTLowerBound (r : ℝ) : ℝ :=
  max (1000/r) ((10^6 : ℝ)/explicitRouterDensity (explicitThinning r))

/-- Actual paper-shaped choice of constants and one augmented sample.
It simultaneously supplies exact-matching, ordinary ordinary-transition transitions, the pair/size
events, and local router primitives plus the intermediate-port pool.
The only nonstandard inputs are the explicitly typed AKS and Pippenger
theorems. No global router or path factor is assumed or asserted. -/
theorem exists_explicitAugmentedSample
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (hPippenger : PippengerTheorem.{u}) (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ 1/10) :
    ∃ T : ℕ, Even T ∧ explicitTLowerBound r ≤ (T : ℝ) ∧ ∃ m : ℕ,
      0 < m ∧ m + 12 = 2*T ∧ ∃ d : Densities m,
        d.r = r ∧ 0 < d.q ∧ 100*d.q ≤ d.r ∧ d.q*((m : ℝ)+12) = 1 ∧
        d.q ≤ 1/3 ∧ ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1/2 ∧
          0 < explicitEpsilon d.q m μ r (explicitRouterDensity (explicitThinning r)) ∧
          25*d.q + 5*explicitEpsilon d.q m μ r (explicitRouterDensity (explicitThinning r)) <
            explicitRouterDensity (explicitThinning r)/4 ∧
          ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
            Odd (Fintype.card G) → N ≤ Fintype.card G →
            ∃ s : AugmentedSample G m,
              GoodSample d (explicitSizeTolerance (Fintype.card G)) (forgetAugmented s) ∧
              LayerTransitionEvent d (explicitTheta d.q m) (explicitEta d.q m μ) (forgetAugmented s) ∧
              AugmentedRouterReservoirEvent (explicitThinning r) s := by
  obtain ⟨T, hTeven, hTL, m, hm, hk, d, hdr, hq, hqr, hqk, hqthird, ha, hc⟩ :=
    exists_evenExplicitDensities r (explicitTLowerBound r) hr hrsmall
  have hu := explicitThinning_bounds r hr
  have hu1 : explicitThinning r ≤ 1 := by
    have := hu.2
    linarith
  have hb := explicitRouterDensity_bounds (explicitThinning r) hu.1 hu1
  have hθ := explicitTheta_bounds d.q m hq hqthird
  have hdrpos : 0 < d.r := by simpa [hdr] using hr
  have hur : explicitThinning r ≤ d.r := by simpa [hdr] using hu.2
  obtain ⟨μ, hμ, hμhalf, hsample⟩ :=
    exists_goodAugmented_layeredTransitions_and_routerReservoir hAKS hPippenger d
      (explicitTheta d.q m) (explicitThinning r) hq hqthird hθ.1 hθ.2 hdrpos hu.1 hur
  have hη := explicitEta_bounds d.q m μ hq hqthird hμ
  obtain ⟨N, hN⟩ := hsample (explicitEta d.q m μ) hη.1 hη.2.1 hη.2.2.1 hη.2.2.2
  have hε := explicitEpsilon_bounds d.q m μ r (explicitRouterDensity (explicitThinning r))
    hq hqthird hμ hr hb.1
  have hTbound : (10^6 : ℝ)/explicitRouterDensity (explicitThinning r) ≤ (T : ℝ) :=
    (le_max_right _ _).trans hTL
  have hkreal : (m : ℝ)+12 = 2*(T : ℝ) := by exact_mod_cast hk
  have hqT : d.q * (2*(T : ℝ)) = 1 := by rw [← hkreal]; exact hqk
  have hqbound := reciprocalRouterBound d.q T (explicitRouterDensity (explicitThinning r))
    hq hb.1 hTbound hqT
  have hslack := explicitRouter_fraction_slack d.q
    (explicitEpsilon d.q m μ r (explicitRouterDensity (explicitThinning r)))
    (explicitRouterDensity (explicitThinning r)) hb.1 hqbound hε.2.2.2.1
  exact ⟨T, hTeven, hTL, m, hm, hk, d, hdr, hq, hqr, hqk, hqthird,
    μ, hμ, hμhalf, hε.1, hslack, N, hN⟩

end
end EndpointLayeredSample
