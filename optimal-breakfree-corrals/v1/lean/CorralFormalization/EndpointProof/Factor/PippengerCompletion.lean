import CorralFormalization.EndpointProof.Matching.Fractional.PippengerExactMatching
import CorralFormalization.EndpointProof.Factor.UniformPhysicalCompletion

/-! Pippenger-only endpoint completion, reusing the existing deterministic
physical closure and the same-sample exact-matching event. -/

open scoped BigOperators Classical
open EndpointLayeredSample EndpointTransitions EndpointMatching.Fractional.Rounding
open EndpointMatching.AbsorptionAssembly EndpointFactor EndpointFactor.Allocation
open EndpointFactor.OrdinaryFragments

namespace EndpointPippenger
noncomputable section
universe u

theorem exists_explicitAugmentedSample_pippenger
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
    exists_goodAugmented_layeredTransitions_and_routerReservoir_pippenger hPippenger d
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

theorem exists_uniform_common_sample_and_attached_paths_pippenger
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
    exists_explicitAugmentedSample_pippenger hPippenger r hr hr10
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

theorem exists_uniform_common_sample_and_contracted_closure_pippenger
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
    exists_uniform_common_sample_and_attached_paths_pippenger hPippenger r hr hr10
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

theorem uniformPhysicalEndpointCompletion_of_pippenger
    (hPippenger : PippengerTheorem.{u})
    (r : ℝ) (hr : 0 < r) (hr10 : r ≤ 1/10) :
    CycleCut.UniformPhysicalEndpointCompletion.{u} := by
  obtain ⟨T, hTeven, hTL, m, hm, hkT, dist, hdr, hq, hqr, hqk, hq3,
    μ, hμ, hμhalf, hε, N, hsample⟩ :=
    exists_uniform_common_sample_and_contracted_closure_pippenger
      hPippenger r hr hr10
  unfold CycleCut.UniformPhysicalEndpointCompletion
  refine ⟨_, hε, N, ?_⟩
  intro G _ _ hodd hn W D X Y hX hY hXY hXYcard hK hW hDzero hD hsum
  obtain ⟨sample, _, _, _, htargets⟩ := hsample G hodd hn
  exact CycleExpansion.endpointConclusion_of_preparedWithContractedClosure
    (htargets W D X Y hX hY hXY hXYcard hK hW hD hDzero hsum)

/-- A closed parameter choice.  Pippenger remains the explicit input in
the theorem statement; no endpoint or physical-cycle existence is assumed. -/
theorem uniformPhysicalEndpointCompletion_from_pippenger
    (hPippenger : PippengerTheorem.{u}) :
    CycleCut.UniformPhysicalEndpointCompletion.{u} := by
  apply uniformPhysicalEndpointCompletion_of_pippenger hPippenger (1/100)
  · norm_num
  · norm_num

end
end EndpointPippenger
