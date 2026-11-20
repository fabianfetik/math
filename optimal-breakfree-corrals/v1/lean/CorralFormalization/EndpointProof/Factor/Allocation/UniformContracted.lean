import CorralFormalization.EndpointProof.Factor.Allocation.UniformOrdinary
import CorralFormalization.EndpointProof.Factor.Allocation.ContractedClosure

/-!
# One sample, all targets, and an actual one-cycle track closure

The input order is the paper's: fixed constants, one group-uniform threshold,
one augmented sample, every later target, then exact-matching and the router setting.
Expanding the contracted cycle into the full marked physical cycle and cutting
its virtual edges remain separate obligations.
-/

open scoped BigOperators Classical
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointTransitions EndpointMatching.Fractional.Rounding
open EndpointFactor.OrdinaryFragments
noncomputable section
universe u

/-- Actual prepared paths and a fully specified single-cycle contracted
closure for the literal floor quotient and remainder of this target. -/
def PreparedWithContractedClosure {G : Type u} [Fintype G] [AddCommGroup G] {m : ℕ}
    (dist : Densities m) (sample : AugmentedSample G m) (W D X Y : Finset G) : Prop := by
  classical
  let ℓ := W.card/(m+12)
  let w := W.card%(m+12)
  let d := Fintype.card G-(m+12)*ℓ
  exact 0 < ℓ ∧ ∃ P : PreparedTarget dist sample W D X Y ℓ w d,
    ∃ A : LayerData G (m+1) ℓ, ∃ hLayer : A.layer = P.ordinaryLayer,
      (∀ i, A.color i ⊆ P.ordinaryColour i) ∧
      ∃ O : Outcome A P.ordinaryPool P.leftover P.bank Y,
        Nonempty (ContractedClosure P A hLayer O)

/-- The common sample gives a concrete single-cycle contracted closure for
every later paper-admissible target, assuming the original target checksum.
The only external theorem parameters are the stated AKS and Pippenger inputs. -/
theorem exists_uniform_common_sample_and_contracted_closure
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (hPippenger : PippengerTheorem.{u}) (r : ℝ) (hr : 0 < r) (hr10 : r ≤ 1/10) :
    ∃ T : ℕ, Even T ∧ explicitTLowerBound r ≤ (T : ℝ) ∧ ∃ m : ℕ,
      0 < m ∧ m+12=2*T ∧ ∃ dist : Densities m,
        dist.r = r ∧ 0 < dist.q ∧ 100*dist.q ≤ dist.r ∧
        dist.q*((m : ℝ)+12)=1 ∧ dist.q ≤ 1/3 ∧ ∃ μ : ℝ,
        0 < μ ∧ μ ≤ 1/2 ∧
        let ε := explicitEpsilon dist.q m μ r (explicitRouterDensity (explicitThinning r))
        0 < ε ∧ ∃ N : ℕ,
          ∀ (G : Type u) [Fintype G] [AddCommGroup G],
            Odd (Fintype.card G) → N ≤ Fintype.card G →
            ∃ sample : AugmentedSample G m,
              GoodSample dist (explicitSizeTolerance (Fintype.card G)) (forgetAugmented sample) ∧
              LayerTransitionEvent dist (explicitTheta dist.q m) (explicitEta dist.q m μ)
                (forgetAugmented sample) ∧
              AugmentedRouterReservoirEvent (explicitThinning r) sample ∧
              ∀ W D X Y : Finset G,
                X ⊆ W → Y ⊆ W → Disjoint X Y → X.card = Y.card →
                (X.card : ℝ) ≤ ε*Fintype.card G →
                (1-ε)*Fintype.card G ≤ (W.card : ℝ) →
                D.card+X.card = W.card → (0 : G) ∉ D →
                (∑ c ∈ D, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x →
                PreparedWithContractedClosure dist sample W D X Y := by
  obtain ⟨T, hTeven, hTL, m, hm, hkT, dist, hdr, hq, hqr, hqk, hq3,
    μ, hμ, hμhalf, hε, N, hsample⟩ :=
    exists_uniform_common_sample_and_attached_paths hAKS hPippenger r hr hr10
  refine ⟨T, hTeven, hTL, m, hm, hkT, dist, hdr, hq, hqr, hqk, hq3,
    μ, hμ, hμhalf, hε, N, ?_⟩
  intro G _ _ hodd hn
  obtain ⟨sample, hgood, htrans, hevent, htargets⟩ := hsample G hodd hn
  refine ⟨sample, hgood, htrans, hevent, ?_⟩
  intro W D X Y hX hY hXY hXYcard hK hW hD hDzero hsum
  have hprepared := htargets W D X Y hX hY hXY hXYcard hK hW hD hDzero
  dsimp [PreparedAndAttached] at hprepared
  dsimp [PreparedWithContractedClosure]
  obtain ⟨hℓpos, P, A, hLayer, hColors, _, O, hedit⟩ := hprepared
  exact ⟨hℓpos, P, A, hLayer, hColors, O,
    exists_contractedClosure P A hLayer hColors O hgood.1 hXYcard hD hDzero hsum hedit⟩

end
end EndpointFactor.Allocation
