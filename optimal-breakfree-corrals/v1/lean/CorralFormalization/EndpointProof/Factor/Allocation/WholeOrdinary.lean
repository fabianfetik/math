import CorralFormalization.EndpointProof.Factor.Allocation.PreparedOutcome

/-!
# One sample through the actual ordinary attachment

For each later admissible target, the shared sample now supplies actual
special and generic layers, a fixed router, colour pools, ordinary-transition matchings,
and the attached ordinary path family. The final router splice, exact
closing and cyclic assembly remain separate.
-/

open scoped BigOperators Classical
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointFactor.OrdinaryFragments
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}

theorem prepare_and_attach_of_good_sample
    (dist : Densities m) (sample : AugmentedSample G m) (u ε η : ℝ)
    (hgood : GoodSample dist (explicitSizeTolerance (Fintype.card G)) (forgetAugmented sample))
    (hevent : AugmentedRouterReservoirEvent u sample)
    (htrans : LayerTransitionEvent dist (explicitTheta dist.q m) η (forgetAugmented sample))
    (hu : 0 < u) (hu1 : u ≤ 1) (hm : 0 < m)
    (hq : 0 < dist.q) (hq3 : dist.q ≤ 1/3)
    (hr : 0 < dist.r) (hr10 : dist.r ≤ 1/10) (hqr : 100*dist.q ≤ dist.r)
    (hε : 0 < ε) (hη : 0 < η)
    (hεrq : ε ≤ dist.r*dist.q/10^8) (hεη : ε ≤ η/10000)
    (hεΔ : ε ≤ explicitDelta dist.q/100000)
    (ha : dist.a ≤ (1-dist.r/2)*dist.q) (hc : dist.c ≤ (1-dist.r/2)*dist.q)
    (hqk : dist.q*((m : ℝ)+12) = 1)
    (hslack : 25*dist.q+5*ε < explicitRouterDensity u/4)
    (W D X Y : Finset G) (ℓ w d : ℕ)
    (hX : X ⊆ W) (hY : Y ⊆ W) (hXY : Disjoint X Y) (hXYcard : X.card = Y.card)
    (hW : W.card = (m+12)*ℓ+w) (hdiv : (m+12)*ℓ+d = Fintype.card G)
    (hD : D.card+X.card = W.card) (hDzero : (0 : G) ∉ D)
    (hd : (d : ℝ) ≤ 2*ε*Fintype.card G)
    (hsize : explicitSizeTolerance (Fintype.card G) ≤ ε*Fintype.card G)
    (hK : (X.card : ℝ) ≤ ε*Fintype.card G)
    (hw : (w : ℝ) ≤ ε*Fintype.card G) :
    0 < ℓ ∧ ∃ P : PreparedTarget dist sample W D X Y ℓ w d,
      ∃ A : LayerData G (m+1) ℓ,
        A.layer = P.ordinaryLayer ∧ (∀ i, A.color i ⊆ P.ordinaryColour i) ∧
        (A.deficit : ℝ) ≤ explicitDelta dist.q*Fintype.card G/10000 ∧
        Nonempty (Outcome A P.ordinaryPool P.leftover P.bank Y) := by
  obtain ⟨P⟩ := prepare_target_of_good_sample dist sample u ε η hgood hevent hu hu1
    hq hq3 hr hr10 hε hη hεrq hεη ha hc hqk hslack W D X Y ℓ w d
    hX hY hXY hXYcard hW hdiv hD hd hsize hK
  have hn : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos (α := G)
  have hqk' : dist.q * ((m+12 : ℕ) : ℝ) = 1 := by simpa using hqk
  have hℓ := layer_capacity_eq (Fintype.card G) (m+12) ℓ d dist.q hdiv hqk'
  obtain ⟨_, hKcapR, hℓposR, _, _, hnearSize, hspecial, hgeneric, hcolour⟩ :=
    explicit_layer_numeric_bounds dist.q dist.r ε η (Fintype.card G) d
      (explicitSizeTolerance (Fintype.card G)) X.card ℓ dist.a dist.c
      hq hq3 hr hr10 hε hη hn (Nat.cast_nonneg _)
      (explicitSizeTolerance_nonneg _) (Nat.cast_nonneg _)
      hεrq hεη hd hsize hK hℓ ha hc
  have hKcap : X.card ≤ ℓ := by exact_mod_cast hKcapR
  have hℓpos : 0 < ℓ := by exact_mod_cast hℓposR
  obtain ⟨A, hAlayer, hAcolors, _, hAdef⟩ :=
    P.exists_ordinaryLayerData (explicitTheta dist.q m) η htrans hm hq hr10 hqr hqk
      hDzero hnearSize hspecial hgeneric hcolour
  have hDefBudget := ordinary_total_deficit_budget dist.q m (Fintype.card G) hq hq3 hn.le
  have hAdef' : (A.deficit : ℝ) ≤ explicitDelta dist.q * Fintype.card G/10000 :=
    hAdef.trans hDefBudget
  have hΔq : explicitDelta dist.q ≤ dist.q^2 := (explicitDelta_bounds dist.q hq (by linarith)).2
  have hOutcome := P.exists_fragmentOutcome A hAlayer hAcolors hgood.2.1 hXYcard hKcap hDzero
    ε (explicitDelta dist.q) hq hq3 hε hΔq hεΔ hd hsize hK hw hAdef'
  exact ⟨hℓpos, P, A, hAlayer, hAcolors, hAdef', hOutcome⟩

end
end EndpointFactor.Allocation
