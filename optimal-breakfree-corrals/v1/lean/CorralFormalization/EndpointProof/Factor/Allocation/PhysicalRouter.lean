import CorralFormalization.EndpointProof.Factor.Allocation.RouterLedger

/-!
# The global router inside the actual target inventories

This connects the installed-router theorem to the actual three selected
special classes and the original augmented sample. It does not construct the
ordinary path system or the final factor.
-/

open scoped BigOperators Classical symmDiff
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointRouter EndpointFactor Equiv Equiv.Perm
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}

/-- Genuine fixed router data, with physical inventories contained in the
requested target and with the later closing quantifier explicit. -/
structure PhysicalRouter (sample : AugmentedSample G m) (special : Fin 3 → Finset G)
    (W D : Finset G) (ℓ : ℕ) where
  input : Fin ℓ → G
  output : Fin ℓ → G
  input_injective : Function.Injective input
  output_injective : Function.Injective output
  input_mem : ∀ i, input i ∈ special 0
  output_mem : ∀ i, output i ∈ special 1
  input_covers : ∀ x ∈ special 0, ∃ i, input i = x
  output_covers : ∀ x ∈ special 1, ∃ i, output i = x
  middle : Fin ℓ → G
  first : LayerGeometry (firstMatchingLayer ℓ) input middle
  second : LayerGeometry (secondMatchingLayer ℓ) middle output
  interior_card : (fixedInteriorFinset first second).card = 9*ℓ
  color_card : (fixedColorFinset first second).card = 10*ℓ
  interior_in_target : fixedInteriorFinset first second ⊆ W
  interior_in_reserve : fixedInteriorFinset first second ⊆
    vertexSet (forgetAugmented sample) (reserveVertex m)
  interior_avoids_special : Disjoint (fixedInteriorFinset first second) (Finset.univ.biUnion special)
  color_in_target : fixedColorFinset first second ⊆ D
  color_in_reserve : fixedColorFinset first second ⊆
    colourSet (forgetAugmented sample) (reserveColour m)
  colors_nonzero : 0 ∉ fixedColorFinset first second
  settings_valid : ∀ a b : List (Fin ℓ × Fin ℓ),
    a.Sublist (firstLayer ℓ) → b.Sublist (secondLayer ℓ) →
      ((List.finRange ℓ).flatMap (fun i => (installedRoutes first second a b i).vertices)).Nodup ∧
      ((List.finRange ℓ).flatMap (fun i =>
        (installedRoutes first second a b i).colors (fun x y : G => y-x))).Nodup ∧
      routeInteriorFinset first second a b = fixedInteriorFinset first second ∧
      routeColorFinset first second a b = fixedColorFinset first second
  later_closing : ∀ closing : Perm (Fin ℓ),
    ∃ a b : List (Fin ℓ × Fin ℓ),
      a.Sublist (firstLayer ℓ) ∧ b.Sublist (secondLayer ℓ) ∧
      (closing * (switchProduct b * switchProduct a)).IsCycleOn Set.univ ∧
      ∀ i, (installedRoutes first second a b i).first = input i ∧
        (installedRoutes first second a b i).last = output ((switchProduct b * switchProduct a) i)

/-- Enumerate a finite physical set without duplicating or omitting points. -/
def enumerateSet (S : Finset G) (ℓ : ℕ) (h : S.card = ℓ) : Fin ℓ → G :=
  fun i => ((Finset.equivFinOfCardEq h).symm i : S).val

theorem enumerateSet_injective (S : Finset G) (ℓ : ℕ) (h : S.card = ℓ) :
    Function.Injective (enumerateSet S ℓ h) := by
  intro i j hij
  apply (Finset.equivFinOfCardEq h).symm.injective
  exact Subtype.ext hij

theorem enumerateSet_mem (S : Finset G) (ℓ : ℕ) (h : S.card = ℓ) (i : Fin ℓ) :
    enumerateSet S ℓ h i ∈ S := ((Finset.equivFinOfCardEq h).symm i).property

theorem enumerateSet_covers (S : Finset G) (ℓ : ℕ) (h : S.card = ℓ)
    (x : G) (hx : x ∈ S) : ∃ i, enumerateSet S ℓ h i = x := by
  let i := Finset.equivFinOfCardEq h ⟨x, hx⟩
  refine ⟨i, ?_⟩
  simp [enumerateSet, i]

/-- The actual common-sample router event and paper ledger produce a physical
router from the selected first/second special layers. -/
theorem physicalRouter_of_explicit_ledger
    (sample : AugmentedSample G m) (u q ε : ℝ) (special : Fin 3 → Finset G)
    (W D : Finset G) (ℓ d K : ℕ)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (hevent : AugmentedRouterReservoirEvent u sample) (hℓ0 : 0 < ℓ)
    (hpair : ∀ i j, i ≠ j → Disjoint (special i) (special j))
    (hsize : ∀ i, (special i).card = ℓ)
    (hD : D.card + K = W.card)
    (hmiss : ((Finset.univ : Finset G) \ W).card ≤ d)
    (hℓ : (ℓ : ℝ) ≤ q * Fintype.card G)
    (hd : (d : ℝ) ≤ 2*ε * Fintype.card G)
    (hK : (K : ℝ) ≤ ε * Fintype.card G)
    (hslack : 25*q + 5*ε < explicitRouterDensity u/4) :
    Nonempty (PhysicalRouter sample special W D ℓ) := by
  classical
  let rawSample := forgetAugmented sample
  let RV := vertexSet rawSample (reserveVertex m)
  let RC := colourSet rawSample (reserveColour m)
  let F := explicitRouterForbidden special RV RC W D
  let input := enumerateSet (special 0) ℓ (hsize 0)
  let output := enumerateSet (special 1) ℓ (hsize 1)
  have hin : Function.Injective input := enumerateSet_injective _ _ _
  have hout : Function.Injective output := enumerateSet_injective _ _ _
  have hcross : ∀ i j, input i ≠ output j := by
    intro i j heq
    have hi : input i ∈ special 0 := enumerateSet_mem _ _ _ _
    have hj : output j ∈ special 1 := enumerateSet_mem _ _ _ _
    exact Finset.disjoint_left.mp (hpair 0 1 (by decide)) hi (heq ▸ hj)
  have hn : 0 < Fintype.card G := Fintype.card_pos
  have hledger := explicitRouterForbidden_ledger special RV RC W D ℓ d K q ε
    (explicitRouterDensity u) hpair hsize hD hmiss hℓ hd hK hslack hn
  have h' : ReservoirEvent u (routerTrialBudget u (Fintype.card G)) (routerBits sample) := by
    simpa only [AugmentedRouterReservoirEvent, explicitSwitchBudget_eq_routerExplicitBudget] using hevent
  obtain ⟨middle, first, second, _, _, _, hicard, hccard, hiRV, hcRC, hiF, hcF,
      hzero, hsettings, hclosing⟩ :=
    h'.install_global_router u (routerBits sample) hu hu1 hℓ0 F input output hin hout hcross hledger
  have hspecialF : Finset.univ.biUnion special ⊆ F := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hRVF : RV \ W ⊆ F := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hRCF : RC \ D ⊆ F := by
    intro x hx
    exact Finset.mem_union_right _ hx
  have hiReserve : fixedInteriorFinset first second ⊆ RV := by
    intro x hx
    exact routerVertexReservoir_subset_rawReserve sample (hiRV x hx)
  have hcReserve : fixedColorFinset first second ⊆ RC := by
    intro x hx
    exact routerColourReservoir_subset_rawReserve sample (hcRC x hx)
  have hiW : fixedInteriorFinset first second ⊆ W := by
    intro x hx
    by_contra hnot
    have hxF := hRVF (Finset.mem_sdiff.mpr ⟨hiReserve hx, hnot⟩)
    exact Finset.disjoint_left.mp hiF hx hxF
  have hcD : fixedColorFinset first second ⊆ D := by
    intro x hx
    by_contra hnot
    have hxF := hRCF (Finset.mem_sdiff.mpr ⟨hcReserve hx, hnot⟩)
    exact Finset.disjoint_left.mp hcF hx hxF
  refine ⟨{
    input := input
    output := output
    input_injective := hin
    output_injective := hout
    input_mem := enumerateSet_mem _ _ _
    output_mem := enumerateSet_mem _ _ _
    input_covers := enumerateSet_covers _ _ _
    output_covers := enumerateSet_covers _ _ _
    middle := middle
    first := first
    second := second
    interior_card := hicard
    color_card := hccard
    interior_in_target := hiW
    interior_in_reserve := hiReserve
    interior_avoids_special := hiF.mono_right hspecialF
    color_in_target := hcD
    color_in_reserve := hcReserve
    colors_nonzero := hzero
    settings_valid := ?_
    later_closing := hclosing }⟩
  intro a b ha hb
  have h := hsettings a b ha hb
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- On one fixed good augmentation, every later target satisfying these
finite paper inequalities has actual prescribed-terminal special layers
and an actual globally valid later-settable router inside `W` and `D`. -/
theorem special_layers_and_router_of_good_sample
    (dist : Densities m) (sample : AugmentedSample G m) (u ε tolerance : ℝ)
    (hgood : GoodSample dist tolerance (forgetAugmented sample))
    (hevent : AugmentedRouterReservoirEvent u sample)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (W D X Y : Finset G) (ℓ d : ℕ)
    (hℓ0 : 0 < ℓ) (htol : 0 ≤ tolerance)
    (hmiss : ((Finset.univ : Finset G) \ W).card ≤ d)
    (hℓeq : (ℓ : ℝ) = dist.q * Fintype.card G - dist.q * d)
    (hreserve : 4 * ((d : ℝ) + tolerance) ≤ dist.r * Fintype.card G)
    (hX : X ⊆ W) (hY : Y ⊆ W) (hXY : Disjoint X Y)
    (hXYcard : X.card = Y.card) (hXcap : X.card ≤ ℓ)
    (hD : D.card + X.card = W.card)
    (hd : (d : ℝ) ≤ 2*ε * Fintype.card G)
    (hK : (X.card : ℝ) ≤ ε * Fintype.card G)
    (hslack : 25*dist.q + 5*ε < explicitRouterDensity u/4) :
    ∃ special : Fin 3 → Finset G,
      X ⊆ special 0 ∧ Y ⊆ special 2 ∧
      (∀ i, special i ⊆ W ∧ (special i).card = ℓ ∧
        ((vertexSet (forgetAugmented sample) (specialVertexRole i) ∆ special i).card : ℝ) ≤
          (2+dist.q)*(d : ℝ)+tolerance+4*X.card) ∧
      (∀ i j, i ≠ j → Disjoint (special i) (special j)) ∧
      (∀ i, special i ⊆ forcedCarrier
        (fun j => vertexSet (forgetAugmented sample) (specialVertexRole j)) (specialForced X Y)
          W (vertexSet (forgetAugmented sample) (reserveVertex m))) ∧
      Nonempty (PhysicalRouter sample special W D ℓ) := by
  have hmiss' : (((Finset.univ : Finset G) \ W).card : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hmiss
  obtain ⟨special, hXsp, hYsp, hspec, hpair, hcarrier⟩ :=
    exists_explicit_special_vertex_layers dist (forgetAugmented sample) W X Y ℓ d tolerance
      hgood.2.2 (Nat.cast_nonneg _) htol hmiss' hℓeq hreserve hX hY hXY hXYcard hXcap
  have hsize : ∀ i, (special i).card = ℓ := fun i => (hspec i).2.1
  have hqmiss : 0 ≤ dist.q * (d : ℝ) := mul_nonneg dist.q_nonneg (Nat.cast_nonneg _)
  have hℓ : (ℓ : ℝ) ≤ dist.q * Fintype.card G := by linarith
  have hroute := physicalRouter_of_explicit_ledger sample u dist.q ε special W D ℓ d X.card
    hu hu1 hevent hℓ0 hpair hsize hD hmiss hℓ hd hK hslack
  exact ⟨special, hXsp, hYsp, hspec, hpair, hcarrier, hroute⟩

end
end EndpointFactor.Allocation
