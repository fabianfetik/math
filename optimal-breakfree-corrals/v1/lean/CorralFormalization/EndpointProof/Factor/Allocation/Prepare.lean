import CorralFormalization.EndpointProof.Factor.Allocation.ColourPools
import CorralFormalization.EndpointProof.Factor.Allocation.LayerBudgetBounds

/-!
# Preparing one actual paper target on the common sample

The result constructs the special classes, router, generic layers, singleton
remainder and the ordinary/bank colour allocation in their actual target sets.
The later matching/fragment/closing construction remains a separate step.
-/

open scoped BigOperators Classical symmDiff
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointRouter
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}

structure PreparedTarget (dist : Densities m) (sample : AugmentedSample G m)
    (W D X Y : Finset G) (ℓ w d : ℕ) where
  special : Fin 3 → Finset G
  starts_in_special : X ⊆ special 0
  ends_in_special : Y ⊆ special 2
  special_data : ∀ i, special i ⊆ W ∧ (special i).card = ℓ ∧
    ((vertexSet (forgetAugmented sample) (specialVertexRole i) ∆ special i).card : ℝ) ≤
      (2+dist.q)*(d : ℝ)+explicitSizeTolerance (Fintype.card G)+4*X.card
  special_disjoint : ∀ i j, i ≠ j → Disjoint (special i) (special j)
  special_carrier : ∀ i, special i ⊆ forcedCarrier
    (fun j => vertexSet (forgetAugmented sample) (specialVertexRole j)) (specialForced X Y)
      W (vertexSet (forgetAugmented sample) (reserveVertex m))
  router : PhysicalRouter sample special W D ℓ
  generic : Fin m → Finset G
  generic_data : ∀ i, generic i ⊆ W \ (Finset.univ.biUnion special ∪
      fixedInteriorFinset router.first router.second) ∧
    (generic i).card = ℓ ∧
    (vertexSet (forgetAugmented sample) (Sum.inr i) \ generic i).card ≤ d+2*X.card
  generic_disjoint : ∀ i j, i ≠ j → Disjoint (generic i) (generic j)
  leftover_card : ((W \ (Finset.univ.biUnion special ∪
      fixedInteriorFinset router.first router.second)) \ Finset.univ.biUnion generic).card = w
  pools : Fin (m+2) → Finset G
  pools_data : ∀ i, pools i ⊆ D \ fixedColorFinset router.first router.second ∧
    (pools i).card = explicitColourCapacity ℓ w X.card i
  pools_disjoint : ∀ i j, i ≠ j → Disjoint (pools i) (pools j)
  pools_complete : Finset.univ.biUnion pools = D \ fixedColorFinset router.first router.second
  ordinary_loss : ∀ i : Fin (m+1),
    (colourSet (forgetAugmented sample) (Sum.inr i) \ pools i.castSucc).card ≤ d+X.card
  bank_loss : ((colourSet (forgetAugmented sample) (specialColour m) \
      pools (Fin.last (m+1))).card : ℝ) ≤ d+explicitSizeTolerance (Fintype.card G)+X.card
  bank_edit : ((colourSet (forgetAugmented sample) (specialColour m) ∆
      pools (Fin.last (m+1))).card : ℝ) ≤
      (2+dist.q)*d+explicitSizeTolerance (Fintype.card G)+X.card

/-- Actual target preparation from one already-good paper sample. Its
numerical premises are the paper's eventual finite-order bounds; no special
layer, router, generic layer or colour allocation is assumed. -/
theorem prepare_target_of_good_sample
    (dist : Densities m) (sample : AugmentedSample G m) (u ε η : ℝ)
    (hgood : GoodSample dist (explicitSizeTolerance (Fintype.card G)) (forgetAugmented sample))
    (hevent : AugmentedRouterReservoirEvent u sample)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (hq : 0 < dist.q) (hq3 : dist.q ≤ 1/3)
    (hr : 0 < dist.r) (hr10 : dist.r ≤ 1/10)
    (hε : 0 < ε) (hη : 0 < η)
    (hεrq : ε ≤ dist.r*dist.q/10^8) (hεη : ε ≤ η/10000)
    (ha : dist.a ≤ (1-dist.r/2)*dist.q) (hc : dist.c ≤ (1-dist.r/2)*dist.q)
    (hqk : dist.q*((m : ℝ)+12) = 1)
    (hslack : 25*dist.q+5*ε < explicitRouterDensity u/4)
    (W D X Y : Finset G) (ℓ w d : ℕ)
    (hX : X ⊆ W) (hY : Y ⊆ W) (hXY : Disjoint X Y) (hXYcard : X.card = Y.card)
    (hW : W.card = (m+12)*ℓ+w) (hdiv : (m+12)*ℓ+d = Fintype.card G)
    (hD : D.card+X.card = W.card)
    (hd : (d : ℝ) ≤ 2*ε*Fintype.card G)
    (hsize : explicitSizeTolerance (Fintype.card G) ≤ ε*Fintype.card G)
    (hK : (X.card : ℝ) ≤ ε*Fintype.card G) :
    Nonempty (PreparedTarget dist sample W D X Y ℓ w d) := by
  have hn : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos (α := G)
  have hqk' : dist.q * ((m+12 : ℕ) : ℝ) = 1 := by simpa using hqk
  have hℓ := layer_capacity_eq (Fintype.card G) (m+12) ℓ d dist.q hdiv hqk'
  have htol := explicitSizeTolerance_nonneg (Fintype.card G)
  obtain ⟨hreserve, hKcapR, hℓposR, haFit, hcFit, _, _, _, _⟩ :=
    explicit_layer_numeric_bounds dist.q dist.r ε η (Fintype.card G) d
      (explicitSizeTolerance (Fintype.card G)) X.card ℓ dist.a dist.c
      hq hq3 hr hr10 hε hη hn (Nat.cast_nonneg _) htol (Nat.cast_nonneg _)
      hεrq hεη hd hsize hK hℓ ha hc
  have hKcap : X.card ≤ ℓ := by exact_mod_cast hKcapR
  have hℓpos : 0 < ℓ := by exact_mod_cast hℓposR
  have hmiss : ((Finset.univ : Finset G) \ W).card ≤ d := by
    have hsplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ W)
    simp only [Finset.card_univ] at hsplit
    omega
  obtain ⟨special, hXsp, hYsp, hspec, hpair, hcarrier, hrouter⟩ :=
    special_layers_and_router_of_good_sample dist sample u ε
      (explicitSizeTolerance (Fintype.card G)) hgood hevent hu hu1 W D X Y ℓ d
      hℓpos htol hmiss hℓ hreserve hX hY hXY hXYcard hKcap hD hd hK hslack
  obtain ⟨router⟩ := hrouter
  have hspecsize : ∀ i, (special i).card = ℓ := fun i => (hspec i).2.1
  have hspecsub : ∀ i, special i ⊆ W := fun i => (hspec i).1
  obtain ⟨generic, hgen, hgendisj, hleft⟩ :=
    exists_explicit_generic_vertex_layers dist sample W D X Y special ℓ w d router
      hgood hspecsize hpair hspecsub hcarrier hXYcard hW hmiss haFit
  obtain ⟨pools, hpools, hpairs, hcomplete, hord, hbankloss, hbankedit⟩ :=
    exists_explicit_colour_pools dist sample special W D ℓ w X.card d router
      (explicitSizeTolerance (Fintype.card G)) hgood.2.2 htol hW hD hdiv hKcap hℓ hcFit
  exact ⟨{
    special := special
    starts_in_special := hXsp
    ends_in_special := hYsp
    special_data := hspec
    special_disjoint := hpair
    special_carrier := hcarrier
    router := router
    generic := generic
    generic_data := hgen
    generic_disjoint := hgendisj
    leftover_card := hleft
    pools := pools
    pools_data := hpools
    pools_disjoint := hpairs
    pools_complete := hcomplete
    ordinary_loss := hord
    bank_loss := hbankloss
    bank_edit := hbankedit }⟩

end
end EndpointFactor.Allocation
