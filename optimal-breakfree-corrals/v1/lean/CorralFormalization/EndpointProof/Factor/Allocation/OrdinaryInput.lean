import CorralFormalization.EndpointProof.Factor.Allocation.Prepare
import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Outcome

/-!
# Physical ordinary-layer inputs from the prepared target

The first ordinary layer is special layer V₂, followed by every generic
layer and finally Vⱼ. The ordinary colours are the non-bank pools.
-/

open scoped BigOperators Classical symmDiff
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointRouter EndpointFactor.OrdinaryFragments
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
variable {dist : Densities m} {sample : AugmentedSample G m}
variable {W D X Y : Finset G} {ℓ w d : ℕ}

def PreparedTarget.ordinaryLayer (P : PreparedTarget dist sample W D X Y ℓ w d) :
    Fin (m+2) → Finset G :=
  Fin.cases (P.special 1) (Fin.lastCases (P.special 2) P.generic)

def ordinaryVertexRole {m : ℕ} : Fin (m+2) → VertexRole m :=
  Fin.cases (secondVertex m) (Fin.lastCases (lastVertex m) (fun i => Sum.inr i))

def PreparedTarget.ordinaryColour (P : PreparedTarget dist sample W D X Y ℓ w d) :
    Fin (m+1) → Finset G := fun i => P.pools i.castSucc

def PreparedTarget.leftover (P : PreparedTarget dist sample W D X Y ℓ w d) : Finset G :=
  (W \ (Finset.univ.biUnion P.special ∪ fixedInteriorFinset P.router.first P.router.second)) \
    Finset.univ.biUnion P.generic

def PreparedTarget.ordinaryPool (P : PreparedTarget dist sample W D X Y ℓ w d) : Finset G :=
  Finset.univ.biUnion P.ordinaryColour

def PreparedTarget.bank (P : PreparedTarget dist sample W D X Y ℓ w d) : Finset G :=
  P.pools (Fin.last (m+1))

theorem PreparedTarget.special_generic_disjoint
    (P : PreparedTarget dist sample W D X Y ℓ w d) (i : Fin 3) (j : Fin m) :
    Disjoint (P.special i) (P.generic j) := by
  apply Finset.disjoint_left.mpr
  intro x hs hg
  have hblocked : x ∈ Finset.univ.biUnion P.special ∪
      fixedInteriorFinset P.router.first P.router.second := by
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hs⟩
  exact (Finset.mem_sdiff.mp ((P.generic_data j).1 hg)).2 hblocked

theorem PreparedTarget.ordinaryLayer_size
    (P : PreparedTarget dist sample W D X Y ℓ w d) (i : Fin (m+2)) :
    (P.ordinaryLayer i).card = ℓ := by
  induction i using Fin.cases with
  | zero => simpa [ordinaryLayer] using (P.special_data 1).2.1
  | succ i =>
      induction i using Fin.lastCases with
      | last => simpa [ordinaryLayer, ← Fin.succ_last] using (P.special_data 2).2.1
      | cast i => simpa [ordinaryLayer] using (P.generic_data i).2.1

theorem PreparedTarget.ordinaryLayer_disjoint
    (P : PreparedTarget dist sample W D X Y ℓ w d) :
    ∀ i j, i ≠ j → Disjoint (P.ordinaryLayer i) (P.ordinaryLayer j) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
          induction j using Fin.lastCases with
          | last => simpa [ordinaryLayer, ← Fin.succ_last] using P.special_disjoint 1 2 (by decide)
          | cast j => simpa [ordinaryLayer] using P.special_generic_disjoint 1 j
  | succ i =>
      induction i using Fin.lastCases with
      | last =>
          induction j using Fin.cases with
          | zero => simpa [ordinaryLayer, ← Fin.succ_last] using (P.special_disjoint 1 2 (by decide)).symm
          | succ j =>
              induction j using Fin.lastCases with
              | last => exact (hij rfl).elim
              | cast j => simpa [ordinaryLayer, ← Fin.succ_last] using P.special_generic_disjoint 2 j
      | cast i =>
          induction j using Fin.cases with
          | zero => simpa [ordinaryLayer] using (P.special_generic_disjoint 1 i).symm
          | succ j =>
              induction j using Fin.lastCases with
              | last => simpa [ordinaryLayer, ← Fin.succ_last] using (P.special_generic_disjoint 2 i).symm
              | cast j =>
                  have hij' : i ≠ j := by
                    intro h; subst j; exact hij rfl
                  simpa [ordinaryLayer] using P.generic_disjoint i j hij'

theorem PreparedTarget.ordinaryColour_size
    (P : PreparedTarget dist sample W D X Y ℓ w d) (i : Fin (m+1)) :
    (P.ordinaryColour i).card = ℓ := by
  simpa [ordinaryColour, explicitColourCapacity] using (P.pools_data i.castSucc).2

theorem PreparedTarget.ordinaryColour_disjoint
    (P : PreparedTarget dist sample W D X Y ℓ w d) :
    ∀ i j, i ≠ j → Disjoint (P.ordinaryColour i) (P.ordinaryColour j) := by
  intro i j hij
  apply P.pools_disjoint
  intro heq
  exact hij ((Fin.castSucc_injective (m+1)) heq)

theorem PreparedTarget.ordinaryColour_subset
    (P : PreparedTarget dist sample W D X Y ℓ w d) (i : Fin (m+1)) :
    P.ordinaryColour i ⊆ D :=
  (P.pools_data i.castSucc).1.trans Finset.sdiff_subset

theorem PreparedTarget.ordinaryColour_nonzero
    (P : PreparedTarget dist sample W D X Y ℓ w d) (hDzero : (0 : G) ∉ D)
    (i : Fin (m+1)) : (0 : G) ∉ P.ordinaryColour i :=
  fun h => hDzero (P.ordinaryColour_subset i h)

theorem ordinaryVertexRole_nonreserve (i : Fin (m+2)) :
    ordinaryVertexRole i ≠ reserveVertex m := by
  induction i using Fin.cases with
  | zero => simp [ordinaryVertexRole, secondVertex, reserveVertex]
  | succ i =>
      induction i using Fin.lastCases with
      | last => simp [ordinaryVertexRole, lastVertex, reserveVertex, ← Fin.succ_last]
      | cast i => simp [ordinaryVertexRole, reserveVertex]

theorem PreparedTarget.special_raw_loss
    (P : PreparedTarget dist sample W D X Y ℓ w d) (i : Fin 3) :
    (((vertexSet (forgetAugmented sample) (specialVertexRole i) \ P.special i).card : ℝ)) ≤
      (2+dist.q)*(d : ℝ)+explicitSizeTolerance (Fintype.card G)+4*X.card := by
  have hsub := Finset.symmDiff_subset_sdiff
    (s := vertexSet (forgetAugmented sample) (specialVertexRole i)) (t := P.special i)
  have hc := Finset.card_le_card hsub
  have hc' : (((vertexSet (forgetAugmented sample) (specialVertexRole i) \ P.special i).card : ℝ)) ≤
      ((vertexSet (forgetAugmented sample) (specialVertexRole i) ∆ P.special i).card : ℝ) := by
    exact_mod_cast hc
  exact hc'.trans (P.special_data i).2.2

theorem PreparedTarget.ordinaryVertex_loss
    (P : PreparedTarget dist sample W D X Y ℓ w d) (η : ℝ)
    (hspecial : (2+dist.q)*(d : ℝ)+explicitSizeTolerance (Fintype.card G)+4*X.card ≤
      η*Fintype.card G)
    (hgeneric : (d : ℝ)+2*X.card ≤ η*Fintype.card G) (i : Fin (m+2)) :
    (((vertexSet (forgetAugmented sample) (ordinaryVertexRole i) \ P.ordinaryLayer i).card : ℝ)) ≤
      η*Fintype.card G := by
  induction i using Fin.cases with
  | zero =>
      have h := (P.special_raw_loss 1).trans hspecial
      simpa [ordinaryVertexRole, ordinaryLayer, specialVertexRole, secondVertex] using h
  | succ i =>
      induction i using Fin.lastCases with
      | last =>
          have h := (P.special_raw_loss 2).trans hspecial
          simpa [ordinaryVertexRole, ordinaryLayer, specialVertexRole, lastVertex,
            ← Fin.succ_last] using h
      | cast i =>
          have hnat := (P.generic_data i).2.2
          have hreal : (((vertexSet (forgetAugmented sample) (Sum.inr i) \ P.generic i).card : ℝ)) ≤
              (d : ℝ)+2*X.card := by exact_mod_cast hnat
          simpa [ordinaryVertexRole, ordinaryLayer] using hreal.trans hgeneric

theorem PreparedTarget.ordinaryColour_loss
    (P : PreparedTarget dist sample W D X Y ℓ w d) (η : ℝ)
    (hbound : (d : ℝ)+X.card ≤ η*Fintype.card G) (i : Fin (m+1)) :
    (((colourSet (forgetAugmented sample) (Sum.inr i) \ P.ordinaryColour i).card : ℝ)) ≤
      η*Fintype.card G := by
  have hnat := P.ordinary_loss i
  have hreal : (((colourSet (forgetAugmented sample) (Sum.inr i) \ P.ordinaryColour i).card : ℝ)) ≤
      (d : ℝ)+X.card := by exact_mod_cast hnat
  exact hreal.trans hbound

def ordinaryTransitionRoles (i : Fin (m+1)) : Fin 3 → RawRole m :=
  ![Sum.inl (ordinaryVertexRole i.castSucc), Sum.inl (ordinaryVertexRole i.succ),
    Sum.inr (Sum.inr i)]

theorem ordinaryTransitionRoles_nonreserve (i : Fin (m+1)) (j : Fin 3) :
    NonReserveRole (ordinaryTransitionRoles i j) := by
  fin_cases j
  · exact ordinaryVertexRole_nonreserve _
  · exact ordinaryVertexRole_nonreserve _
  · simp [ordinaryTransitionRoles, NonReserveRole, reserveColour]

/-- ordinary-transition on the common sample produces the actual near matching for every
ordinary triple of the physically prepared layers and colour pools. -/
theorem PreparedTarget.ordinaryNearMatchings
    (P : PreparedTarget dist sample W D X Y ℓ w d) (t η : ℝ)
    (hevent : LayerTransitionEvent dist t η (forgetAugmented sample))
    (hm : 0 < m) (hq : 0 < dist.q) (hr : dist.r ≤ 1/10)
    (hqr : 100*dist.q ≤ dist.r) (hqk : dist.q*((m : ℝ)+12) = 1)
    (hsize : |(ℓ : ℝ)-dist.q*Fintype.card G| ≤ η*Fintype.card G)
    (hspecial : (2+dist.q)*(d : ℝ)+explicitSizeTolerance (Fintype.card G)+4*X.card ≤
      η*Fintype.card G)
    (hgeneric : (d : ℝ)+2*X.card ≤ η*Fintype.card G)
    (hcolour : (d : ℝ)+X.card ≤ η*Fintype.card G) :
    ∀ i : Fin (m+1),
      PhysicalNearMatching (ordinaryTarget P.ordinaryLayer P.ordinaryColour i)
        ((ℓ : ℝ)-t*Fintype.card G) := by
  intro i
  apply hevent.physicalNearMatching_explicitRoles hm hq hr hqr hqk
    (ordinaryTransitionRoles i) (ordinaryTransitionRoles_nonreserve i)
    (ordinaryTarget P.ordinaryLayer P.ordinaryColour i) ℓ
  · intro j
    fin_cases j <;> simp [ordinaryTarget, P.ordinaryLayer_size, P.ordinaryColour_size]
  · exact hsize
  · intro j
    fin_cases j
    · simpa [physicalRoleSets, ordinaryTransitionRoles, ordinaryTarget] using
        P.ordinaryVertex_loss η hspecial hgeneric i.castSucc
    · simpa [physicalRoleSets, ordinaryTransitionRoles, ordinaryTarget] using
        P.ordinaryVertex_loss η hspecial hgeneric i.succ
    · simpa [physicalRoleSets, ordinaryTransitionRoles, ordinaryTarget, ordinaryColour] using
        P.ordinaryColour_loss η hcolour i

theorem PreparedTarget.exists_ordinaryLayerData
    (P : PreparedTarget dist sample W D X Y ℓ w d) (t η : ℝ)
    (hevent : LayerTransitionEvent dist t η (forgetAugmented sample))
    (hm : 0 < m) (hq : 0 < dist.q) (hr : dist.r ≤ 1/10)
    (hqr : 100*dist.q ≤ dist.r) (hqk : dist.q*((m : ℝ)+12) = 1)
    (hDzero : (0 : G) ∉ D)
    (hsize : |(ℓ : ℝ)-dist.q*Fintype.card G| ≤ η*Fintype.card G)
    (hspecial : (2+dist.q)*(d : ℝ)+explicitSizeTolerance (Fintype.card G)+4*X.card ≤
      η*Fintype.card G)
    (hgeneric : (d : ℝ)+2*X.card ≤ η*Fintype.card G)
    (hcolour : (d : ℝ)+X.card ≤ η*Fintype.card G) :
    ∃ A : LayerData G (m+1) ℓ,
      A.layer = P.ordinaryLayer ∧ (∀ i, A.color i ⊆ P.ordinaryColour i) ∧
      (∀ i, ((ℓ-(A.tail i).card : ℕ) : ℝ) ≤ t*Fintype.card G) ∧
      (A.deficit : ℝ) ≤ ((m+1 : ℕ) : ℝ)*(t*Fintype.card G) := by
  apply exists_layerData_of_near P.ordinaryLayer P.ordinaryColour
    P.ordinaryLayer_size P.ordinaryLayer_disjoint P.ordinaryColour_disjoint
    (P.ordinaryColour_nonzero hDzero) (t*Fintype.card G)
  exact P.ordinaryNearMatchings t η hevent hm hq hr hqr hqk hsize hspecial hgeneric hcolour

theorem PreparedTarget.ordinaryLayer_first
    (P : PreparedTarget dist sample W D X Y ℓ w d) : P.ordinaryLayer 0 = P.special 1 := by
  simp [ordinaryLayer]

theorem PreparedTarget.ordinaryLayer_last
    (P : PreparedTarget dist sample W D X Y ℓ w d) :
    P.ordinaryLayer (Fin.last (m+1)) = P.special 2 := by
  simp [ordinaryLayer, ← Fin.succ_last]

theorem PreparedTarget.leftover_disjoint_ordinaryLayer
    (P : PreparedTarget dist sample W D X Y ℓ w d) (i : Fin (m+2)) :
    Disjoint P.leftover (P.ordinaryLayer i) := by
  apply Finset.disjoint_left.mpr
  intro x hx hxLayer
  have hnotGeneric : x ∉ Finset.univ.biUnion P.generic := (Finset.mem_sdiff.mp hx).2
  have hnotSpecial : x ∉ Finset.univ.biUnion P.special := by
    intro h
    have hblocked : x ∈ Finset.univ.biUnion P.special ∪
        fixedInteriorFinset P.router.first P.router.second := Finset.mem_union_left _ h
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2 hblocked
  induction i using Fin.cases with
  | zero =>
      have hi : x ∈ P.special 1 := by simpa [ordinaryLayer] using hxLayer
      exact hnotSpecial (Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, hi⟩)
  | succ i =>
      induction i using Fin.lastCases with
      | last =>
          have hi : x ∈ P.special 2 := by simpa [ordinaryLayer, ← Fin.succ_last] using hxLayer
          exact hnotSpecial (Finset.mem_biUnion.mpr ⟨2, Finset.mem_univ _, hi⟩)
      | cast i =>
          have hi : x ∈ P.generic i := by simpa [ordinaryLayer] using hxLayer
          exact hnotGeneric (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)

theorem PreparedTarget.leftover_disjoint_vertices
    (P : PreparedTarget dist sample W D X Y ℓ w d) (A : LayerData G (m+1) ℓ)
    (hlayer : A.layer = P.ordinaryLayer) : Disjoint P.leftover A.vertices := by
  apply Finset.disjoint_left.mpr
  intro x hxL hxV
  obtain ⟨i, hi⟩ := A.mem_vertices x |>.mp hxV
  rw [hlayer] at hi
  exact Finset.disjoint_left.mp (P.leftover_disjoint_ordinaryLayer i) hxL hi

theorem PreparedTarget.ordinaryPool_card
    (P : PreparedTarget dist sample W D X Y ℓ w d) : P.ordinaryPool.card = (m+1)*ℓ := by
  unfold ordinaryPool
  rw [Finset.card_biUnion]
  · simp [P.ordinaryColour_size]
  · intro i _ j _ hij
    exact P.ordinaryColour_disjoint i j hij

theorem PreparedTarget.ordinaryPool_subset
    (P : PreparedTarget dist sample W D X Y ℓ w d) : P.ordinaryPool ⊆ D := by
  intro x hx
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  exact P.ordinaryColour_subset i hi

theorem PreparedTarget.bank_disjoint_ordinaryPool
    (P : PreparedTarget dist sample W D X Y ℓ w d) : Disjoint P.bank P.ordinaryPool := by
  apply Finset.disjoint_left.mpr
  intro x hbank hpool
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hpool
  have hd := P.pools_disjoint (Fin.last (m+1)) i.castSucc (Fin.castSucc_ne_last i).symm
  exact Finset.disjoint_left.mp hd hbank hi

theorem PreparedTarget.bank_card
    (P : PreparedTarget dist sample W D X Y ℓ w d) (hK : X.card ≤ ℓ) :
    P.bank.card + X.card = ℓ+w := by
  have h := (P.pools_data (Fin.last (m+1))).2
  simp only [explicitColourCapacity, Fin.lastCases_last] at h
  change (P.pools (Fin.last (m+1))).card + X.card = ℓ+w
  omega

theorem PreparedTarget.bank_subset
    (P : PreparedTarget dist sample W D X Y ℓ w d) : P.bank ⊆ D :=
  (P.pools_data (Fin.last (m+1))).1.trans Finset.sdiff_subset

theorem PreparedTarget.bank_nonzero
    (P : PreparedTarget dist sample W D X Y ℓ w d) (hDzero : (0 : G) ∉ D) :
    (0 : G) ∉ P.bank := fun h => hDzero (P.bank_subset h)

theorem PreparedTarget.matching_colors_subset_ordinaryPool
    (P : PreparedTarget dist sample W D X Y ℓ w d) (A : LayerData G (m+1) ℓ)
    (hcolors : ∀ i, A.color i ⊆ P.ordinaryColour i) : A.colors ⊆ P.ordinaryPool := by
  intro x hx
  obtain ⟨i, hi⟩ := (A.mem_colors x).mp hx
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hcolors i hi⟩

end
end EndpointFactor.Allocation
