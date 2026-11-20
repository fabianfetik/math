import CorralFormalization.EndpointProof.Factor.Allocation.CanonicalDivision
import CorralFormalization.EndpointProof.Factor.ClosingLedger.Prepared

/-!
# One common sample before every target, through ordinary attachment

This is not the full endpoint theorem: it stops after the ordinary paths
and fixed router are constructed. It does prove all their paper-scale source,
division, retention, donor and actual inventory premises on one sample.
-/

open scoped BigOperators Classical
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointTransitions EndpointMatching.Fractional.Rounding
open EndpointFactor.OrdinaryFragments
open EndpointMatching.AbsorptionAssembly
noncomputable section
universe u

/-- The actual fixed router and the actual attached ordinary paths for one
target. All three division quantities are the literal paper choices. -/
def PreparedAndAttached {G : Type u} [Fintype G] [AddCommGroup G] {m : ℕ}
    (dist : Densities m) (sample : AugmentedSample G m) (W D X Y : Finset G) : Prop := by
  classical
  let ℓ := W.card/(m+12)
  let w := W.card%(m+12)
  let d := Fintype.card G-(m+12)*ℓ
  exact 0 < ℓ ∧ ∃ P : PreparedTarget dist sample W D X Y ℓ w d,
    ∃ A : LayerData G (m+1) ℓ,
      A.layer = P.ordinaryLayer ∧ (∀ i, A.color i ⊆ P.ordinaryColour i) ∧
      (A.deficit : ℝ) ≤ explicitDelta dist.q*Fintype.card G/10000 ∧
      ∃ O : Outcome A P.ordinaryPool P.leftover P.bank Y,
        (physicalEditDistance (vertexSet (forgetAugmented sample) (lastVertex m))
          (vertexSet (forgetAugmented sample) (firstVertex m))
          (colourSet (forgetAugmented sample) (specialColour m))
          (O.after.ends \ Y) (P.special 0 \ X)
          (remainingBank P.bank O.joins P.ordinaryPool A.colors) : ℝ) ≤
            explicitDelta dist.q*Fintype.card G

/-- One categorical augmented sample, chosen before all later `W,D,X,Y`,
supplies the literal paper constants and the actual path-fragment attachment.
AKS and Pippenger remain explicit external theorem parameters. -/
theorem exists_uniform_common_sample_and_attached_paths
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
                PreparedAndAttached dist sample W D X Y := by
  obtain ⟨T, hTeven, hTL, m, hm, hkT, dist, hdr, hq, hqr, hqk, hq3,
    μ, hμ, hμhalf, hε, hslack, N₁, hsample⟩ :=
    exists_explicitAugmentedSample hAKS hPippenger r hr hr10
  let b := explicitRouterDensity (explicitThinning r)
  let ε := explicitEpsilon dist.q m μ r b
  have hεpos : 0 < ε := hε
  have hu := explicitThinning_bounds r hr
  have hu1 : explicitThinning r ≤ 1 := by linarith [hu.2]
  have hb := explicitRouterDensity_bounds (explicitThinning r) hu.1 hu1
  have hεbounds := explicitEpsilon_bounds dist.q m μ r b hq hq3 hμ hr hb.1
  have hη := explicitEta_bounds dist.q m μ hq hq3 hμ
  have hr' : 0 < dist.r := by simpa [hdr] using hr
  have hr10' : dist.r ≤ 1/10 := by simpa [hdr] using hr10
  have hwindows := explicitDensityWindows hm dist hq hr10' hqr hqk
  obtain ⟨N₂, hlarge⟩ := explicitSizeTolerance_add_const_eventually ε ((m : ℝ)+12) hεpos
  refine ⟨T, hTeven, hTL, m, hm, hkT, dist, hdr, hq, hqr, hqk, hq3,
    μ, hμ, hμhalf, hεpos, max N₁ N₂, ?_⟩
  intro G _ _ hodd hn
  have hn₁ : N₁ ≤ Fintype.card G := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ Fintype.card G := le_trans (le_max_right _ _) hn
  obtain ⟨sample, hgood, htrans, hevent⟩ := hsample G hodd hn₁
  refine ⟨sample, hgood, htrans, hevent, ?_⟩
  intro W D X Y hX hY hXY hXYcard hK hW hD hDzero
  let k := m+12
  let ℓ := W.card/k
  let w := W.card%k
  let d := Fintype.card G-k*ℓ
  have htol0 := explicitSizeTolerance_nonneg (Fintype.card G)
  have horder := hlarge (Fintype.card G) hn₂
  have htol : explicitSizeTolerance (Fintype.card G) ≤ ε*Fintype.card G := by
    have hk0 : 0 ≤ ((m : ℝ)+12) := by positivity
    linarith
  have hkreal : (k : ℝ) ≤ ε*Fintype.card G := by
    dsimp [k]
    push_cast
    linarith
  have hkpos : 0 < k := by dsimp [k]; omega
  obtain ⟨hWdiv, hdiv, hw, hd⟩ := canonical_division_bounds W k ε hkpos hW hkreal
  have hεrq : ε ≤ dist.r*dist.q/10^8 := by simpa [ε, b, hdr] using hεbounds.2.2.2.2.1
  have hεη : ε ≤ explicitEta dist.q m μ/10000 := by simpa [ε, b] using hεbounds.2.1
  have hεΔ : ε ≤ explicitDelta dist.q/100000 := by simpa [ε, b] using hεbounds.2.2.1
  have hslack' : 25*dist.q+5*ε < explicitRouterDensity (explicitThinning r)/4 := by
    simpa [ε, b] using hslack
  obtain ⟨hℓpos, P, A, hAlayer, hAcolors, hAdef, ⟨O⟩⟩ :=
    prepare_and_attach_of_good_sample dist sample (explicitThinning r) ε (explicitEta dist.q m μ)
    hgood hevent htrans hu.1 hu1 hm hq hq3 hr' hr10' hqr hεpos hη.1
    hεrq hεη hεΔ hwindows.2.1.2 hwindows.2.2.2 hqk hslack' W D X Y ℓ w d
    hX hY hXY hXYcard hWdiv hdiv hD hDzero hd htol hK hw
  have hedit := P.closing_edit_within_radius A hAlayer O hXYcard ε hq3 hd htol hK hw hεpos hεΔ hAdef
  change 0 < ℓ ∧ ∃ P : PreparedTarget dist sample W D X Y ℓ w d,
    ∃ A : LayerData G (m+1) ℓ,
      A.layer = P.ordinaryLayer ∧ (∀ i, A.color i ⊆ P.ordinaryColour i) ∧
      (A.deficit : ℝ) ≤ explicitDelta dist.q*Fintype.card G/10000 ∧
      ∃ O : Outcome A P.ordinaryPool P.leftover P.bank Y,
        (physicalEditDistance (vertexSet (forgetAugmented sample) (lastVertex m))
          (vertexSet (forgetAugmented sample) (firstVertex m))
          (colourSet (forgetAugmented sample) (specialColour m))
          (O.after.ends \ Y) (P.special 0 \ X)
          (remainingBank P.bank O.joins P.ordinaryPool A.colors) : ℝ) ≤
            explicitDelta dist.q*Fintype.card G
  exact ⟨hℓpos, P, A, hAlayer, hAcolors, hAdef, O, by simpa [explicitDelta] using hedit⟩

end
end EndpointFactor.Allocation
