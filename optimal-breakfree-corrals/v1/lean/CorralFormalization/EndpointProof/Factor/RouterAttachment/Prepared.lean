import CorralFormalization.EndpointProof.Factor.RouterAttachment.Physical
import CorralFormalization.EndpointProof.Factor.Allocation.OrdinaryInput

/-!
# PreparedTarget pays all raw freshness conditions for the router splice

The ordinary point carrier and all non-router colour stocks are derived
from the actual prepared classes, remainder and pools. No global splice
validity or target-inventory conclusion is supplied as a premise.
-/

open scoped Classical BigOperators
namespace EndpointFactor.RouterAttachment
open OrdinaryFragments Allocation EndpointRouter EndpointLayeredSample
noncomputable section
universe u
variable {G : Type u} [Fintype G] [AddCommGroup G]
variable {m ℓ w d : ℕ} {dist : Densities m} {sample : AugmentedSample G m}
variable {W D X Y : Finset G}

variable (P : PreparedTarget dist sample W D X Y ℓ w d)

def ordinaryCarrier : Finset G := (Finset.univ.biUnion P.ordinaryLayer) ∪ P.leftover

private theorem mem_specialUnion (x : G) :
    x ∈ Finset.univ.biUnion P.special ↔ x ∈ P.special 0 ∨ x ∈ P.special 1 ∨ x ∈ P.special 2 := by
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    fin_cases i <;> tauto
  · rintro (h | h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩

theorem mem_ordinaryLayerUnion (x : G) :
    x ∈ Finset.univ.biUnion P.ordinaryLayer ↔
      x ∈ P.special 1 ∨ x ∈ P.special 2 ∨ x ∈ Finset.univ.biUnion P.generic := by
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    induction i using Fin.cases with
    | zero => exact Or.inl hi
    | succ i =>
      induction i using Fin.lastCases with
      | last => exact Or.inr (Or.inl (by simpa [PreparedTarget.ordinaryLayer,← Fin.succ_last] using hi))
      | cast i => exact Or.inr (Or.inr ⟨i,by simpa [PreparedTarget.ordinaryLayer] using hi⟩)
  · rintro (h | h | ⟨i,h⟩)
    · exact ⟨0,h⟩
    · exact ⟨(Fin.last m).succ,by simpa [PreparedTarget.ordinaryLayer,← Fin.succ_last] using h⟩
    · exact ⟨i.castSucc.succ,by simpa [PreparedTarget.ordinaryLayer] using h⟩

/-- Every ordinary and leftover vertex is exactly a target point outside
first special layer and fixed router interior. -/
theorem ordinaryCarrier_eq : ordinaryCarrier P =
    W \ (P.special 0 ∪ fixedInteriorFinset P.router.first P.router.second) := by
  ext x
  rw [ordinaryCarrier,Finset.mem_union,mem_ordinaryLayerUnion]
  have hIsp (i : Fin 3) : x ∈ P.special i → x ∉ fixedInteriorFinset P.router.first P.router.second := by
    intro hx hI
    exact Finset.disjoint_left.mp P.router.interior_avoids_special hI
      (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩)
  have hgen : x ∈ Finset.univ.biUnion P.generic →
      x ∈ W ∧ x ∉ Finset.univ.biUnion P.special ∪ fixedInteriorFinset P.router.first P.router.second := by
    intro hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_sdiff.mp ((P.generic_data i).1 hi)
  constructor
  · rintro ((h1 | h2 | hg) | hL)
    · exact Finset.mem_sdiff.mpr ⟨(P.special_data 1).1 h1, by
        simp only [Finset.mem_union,not_or]
        exact ⟨fun h0 => Finset.disjoint_left.mp (P.special_disjoint 0 1 (by decide)) h0 h1,hIsp 1 h1⟩⟩
    · exact Finset.mem_sdiff.mpr ⟨(P.special_data 2).1 h2, by
        simp only [Finset.mem_union,not_or]
        exact ⟨fun h0 => Finset.disjoint_left.mp (P.special_disjoint 0 2 (by decide)) h0 h2,hIsp 2 h2⟩⟩
    · have hg' := hgen hg
      refine Finset.mem_sdiff.mpr ⟨hg'.1,?_⟩
      rintro h
      rcases Finset.mem_union.mp h with h0 | hI
      · exact hg'.2 (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨0,Finset.mem_univ _,h0⟩))
      · exact hg'.2 (Finset.mem_union_right _ hI)
    · have hL' := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hL).1
      refine Finset.mem_sdiff.mpr ⟨hL'.1,?_⟩
      rintro h
      rcases Finset.mem_union.mp h with h0 | hI
      · exact hL'.2 (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨0,Finset.mem_univ _,h0⟩))
      · exact hL'.2 (Finset.mem_union_right _ hI)
  · intro hx
    have hxW := (Finset.mem_sdiff.mp hx).1
    have hxnot := (Finset.mem_sdiff.mp hx).2
    by_cases h1 : x ∈ P.special 1
    · exact Or.inl (Or.inl h1)
    by_cases h2 : x ∈ P.special 2
    · exact Or.inl (Or.inr (Or.inl h2))
    by_cases hg : x ∈ Finset.univ.biUnion P.generic
    · exact Or.inl (Or.inr (Or.inr hg))
    apply Or.inr
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨hxW,?_⟩,hg⟩
    intro h
    rcases Finset.mem_union.mp h with hsp | hI
    · rcases (mem_specialUnion P x).mp hsp with h0 | h1' | h2'
      · exact hxnot (Finset.mem_union_left _ h0)
      · exact h1 h1'
      · exact h2 h2'
    · exact hxnot (Finset.mem_union_right _ hI)

theorem ordinaryCarrier_disjoint :
    Disjoint (P.special 0 ∪ fixedInteriorFinset P.router.first P.router.second) (ordinaryCarrier P) := by
  rw [ordinaryCarrier_eq]
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  exact (Finset.mem_sdiff.mp hx').2 hx

theorem full_vertex_inventory :
    (P.special 0 ∪ fixedInteriorFinset P.router.first P.router.second) ∪ ordinaryCarrier P = W := by
  rw [ordinaryCarrier_eq]
  have hs : P.special 0 ∪ fixedInteriorFinset P.router.first P.router.second ⊆ W := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (P.special_data 0).1 hx
    · exact P.router.interior_in_target hx
  ext x
  have hs' : x ∈ P.special 0 ∪ fixedInteriorFinset P.router.first P.router.second → x ∈ W := fun h => hs h
  simp only [Finset.mem_union] at hs'
  simp only [Finset.mem_union,Finset.mem_sdiff]
  tauto

theorem nonRouterColors : P.ordinaryPool ∪ P.bank = D \ fixedColorFinset P.router.first P.router.second := by
  rw [← P.pools_complete]
  ext c
  simp only [PreparedTarget.ordinaryPool,PreparedTarget.ordinaryColour,PreparedTarget.bank,
    Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro (⟨i,hi⟩ | hi)
    · exact ⟨i.castSucc,hi⟩
    · exact ⟨Fin.last (m+1),hi⟩
  · rintro ⟨i,hi⟩
    by_cases hlt : i.val < m+1
    · let k : Fin (m+1) := ⟨i.val,hlt⟩
      have he : k.castSucc = i := Fin.ext rfl
      exact Or.inl ⟨k,he.symm ▸ hi⟩
    · have he : i = Fin.last (m+1) := Fin.ext (by simp; omega)
      exact Or.inr (he ▸ hi)

section Outcome
variable (A : LayerData G (m+1) ℓ) (hLayer : A.layer = P.ordinaryLayer)
    (hColors : ∀ i, A.color i ⊆ P.ordinaryColour i)
    (O : Outcome A P.ordinaryPool P.leftover P.bank Y)

include hLayer in
theorem outcome_vertex_inventory : O.after.vertices = ordinaryCarrier P := by
  rw [O.after_vertices]
  congr 1
  simp only [LayerData.vertices,hLayer]

include hLayer in
theorem outcome_starts : O.after.starts = P.special 1 := by
  rw [O.after_starts,hLayer]
  rfl

include hColors in
theorem outcome_colors_subset : O.after.colors ⊆ D \ fixedColorFinset P.router.first P.router.second := by
  rw [O.after_colors,← nonRouterColors P]
  intro c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · obtain ⟨i,hi⟩ := (A.mem_colors c).mp hc
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hColors i hi⟩)
  · exact Finset.mem_union_right _ (O.joins_subset hc)

include hLayer in
theorem outcome_point_fresh :
    Disjoint (P.special 0 ∪ fixedInteriorFinset P.router.first P.router.second) O.after.vertices := by
  rw [outcome_vertex_inventory P A hLayer O]
  exact ordinaryCarrier_disjoint P

include hColors in
theorem outcome_color_fresh : Disjoint (fixedColorFinset P.router.first P.router.second) O.after.colors := by
  apply Finset.disjoint_left.mpr
  intro c hc hc'
  exact (Finset.mem_sdiff.mp (outcome_colors_subset P A hColors O hc')).2 hc

/-- Concrete all-settings prefix construction with every raw freshness
premise discharged from PreparedTarget and the actual attached outcome. -/
def preparedFamily (a b : List (Fin ℓ × Fin ℓ))
    (ha : a.Sublist (firstLayer ℓ)) (hb : b.Sublist (secondLayer ℓ)) : Family G :=
  PhysicalRouter.prependRouter P.router O.after (outcome_starts P A hLayer O) a b ha hb
    (outcome_point_fresh P A hLayer O) (outcome_color_fresh P A hColors O)

@[simp] theorem preparedFamily_vertices (a b : List (Fin ℓ × Fin ℓ))
    (ha : a.Sublist (firstLayer ℓ)) (hb : b.Sublist (secondLayer ℓ)) :
    (preparedFamily P A hLayer hColors O a b ha hb).vertices = W := by
  rw [preparedFamily,PhysicalRouter.prependRouter_vertices,outcome_vertex_inventory P A hLayer O,
    full_vertex_inventory P]

@[simp] theorem preparedFamily_colors (a b : List (Fin ℓ × Fin ℓ))
    (ha : a.Sublist (firstLayer ℓ)) (hb : b.Sublist (secondLayer ℓ)) :
    (preparedFamily P A hLayer hColors O a b ha hb).colors =
      D \ remainingBank P.bank O.joins P.ordinaryPool A.colors := by
  rw [preparedFamily,PhysicalRouter.prependRouter_colors]
  have hbank : remainingBank P.bank O.joins P.ordinaryPool A.colors =
      D \ (fixedColorFinset P.router.first P.router.second ∪ O.after.colors) := by
    rw [O.remaining_exact,nonRouterColors P]
    ext c
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hbank]
  have hsub : fixedColorFinset P.router.first P.router.second ∪ O.after.colors ⊆ D := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact P.router.color_in_target hc
    · exact (Finset.mem_sdiff.mp (outcome_colors_subset P A hColors O hc)).1
  ext c
  have hs : c ∈ fixedColorFinset P.router.first P.router.second ∪ O.after.colors → c ∈ D := fun h => hsub h
  simp only [Finset.mem_sdiff]
  tauto

@[simp] theorem preparedFamily_starts (a b : List (Fin ℓ × Fin ℓ))
    (ha : a.Sublist (firstLayer ℓ)) (hb : b.Sublist (secondLayer ℓ)) :
    (preparedFamily P A hLayer hColors O a b ha hb).starts = P.special 0 := by
  exact PhysicalRouter.prependRouter_starts _ _ _ _ _ _ _ _ _

@[simp] theorem preparedFamily_ends (a b : List (Fin ℓ × Fin ℓ))
    (ha : a.Sublist (firstLayer ℓ)) (hb : b.Sublist (secondLayer ℓ)) :
    (preparedFamily P A hLayer hColors O a b ha hb).ends = O.after.ends := by
  exact PhysicalRouter.prependRouter_ends _ _ _ _ _ _ _ _ _

include hLayer in
/-- Physical closing endpoints are disjoint even when an original ordinary
path was a singleton: its prepended router starts in the disjoint V₁ layer. -/
theorem closing_endpoints_disjoint : Disjoint (O.after.ends \ Y) (P.special 0 \ X) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  have he := O.after.ends_subset (Finset.mem_sdiff.mp hx).1
  have hi : x ∈ P.special 0 ∪ fixedInteriorFinset P.router.first P.router.second :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mp hx').1
  exact Finset.disjoint_left.mp (outcome_point_fresh P A hLayer O) hi he

end Outcome
end
end EndpointFactor.RouterAttachment
