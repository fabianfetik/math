import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Core

/-! # Extend an actual fragment partition by a physical partial matching -/

open scoped Classical
namespace EndpointFactor.OrdinaryFragments
open EndpointMatching.AbsorptionAssembly FragmentChecksum
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

namespace Family
variable (F : Family G) {X Y C : Finset G}
    (M : PhysicalDifferenceMatching X Y C)

private theorem step_simple (i : F.Index) (hfresh : Disjoint Y F.vertices) :
    (stepPath M (F.path i)).Nodup := by
  unfold stepPath
  split_ifs with hx
  · apply (F.simple i).append (by simp)
    apply List.disjoint_left.mpr
    intro g hg hg'
    have he : g = (M.endpoint ⟨lastOrZero (F.path i), hx⟩).val := by simpa using hg'
    exact Finset.disjoint_left.mp hfresh (he ▸ (M.endpoint _).property)
      ((F.mem_vertices g).mpr ⟨i, hg⟩)
  · exact F.simple i

private theorem step_disjoint (i j : F.Index) (hij : i ≠ j)
    (hfresh : Disjoint Y F.vertices) :
    List.Disjoint (stepPath M (F.path i)) (stepPath M (F.path j)) := by
  apply List.disjoint_left.mpr
  intro g hi hj
  rcases (mem_stepPath M _ _).mp hi with hi | ⟨x, hx, he⟩
  · rcases (mem_stepPath M _ _).mp hj with hj | ⟨y, hy, he'⟩
    · exact List.disjoint_left.mp (F.disjoint i j hij) hi hj
    · exact Finset.disjoint_left.mp hfresh (he' ▸ (M.endpoint y).property)
        ((F.mem_vertices g).mpr ⟨i, hi⟩)
  · rcases (mem_stepPath M _ _).mp hj with hj | ⟨y, hy, he'⟩
    · exact Finset.disjoint_left.mp hfresh (he ▸ (M.endpoint x).property)
        ((F.mem_vertices g).mpr ⟨j, hj⟩)
    · have hxy : x = y := M.endpoint.injective (Subtype.ext (he.trans he'.symm))
      have hlast : F.last i = F.last j := by
        change lastOrZero (F.path i) = lastOrZero (F.path j)
        exact hx.symm.trans ((congrArg Subtype.val hxy).trans hy)
      exact hij (F.last_injective hlast)

private theorem step_rainbow (i : F.Index) (hfresh : Disjoint C F.colors) :
    (labels (stepPath M (F.path i))).Nodup := by
  rw [labels_stepPath M _ (F.nonempty i)]
  split_ifs with hx
  · apply (F.rainbow i).append (by simp)
    apply List.disjoint_left.mpr
    intro g hg hg'
    have he : g = (M.color ⟨lastOrZero (F.path i), hx⟩).val := by simpa using hg'
    exact Finset.disjoint_left.mp hfresh (he ▸ (M.color _).property)
      ((F.mem_colors g).mpr ⟨i, hg⟩)
  · simpa using F.rainbow i

private theorem step_color_disjoint (i j : F.Index) (hij : i ≠ j)
    (hfresh : Disjoint C F.colors) :
    List.Disjoint (labels (stepPath M (F.path i))) (labels (stepPath M (F.path j))) := by
  apply List.disjoint_left.mpr
  intro g hi hj
  rcases (mem_labels_stepPath M _ (F.nonempty i) _).mp hi with hi | ⟨x, hx, he⟩
  · rcases (mem_labels_stepPath M _ (F.nonempty j) _).mp hj with hj | ⟨y, hy, he'⟩
    · exact List.disjoint_left.mp (F.color_disjoint i j hij) hi hj
    · exact Finset.disjoint_left.mp hfresh (he' ▸ (M.color y).property)
        ((F.mem_colors g).mpr ⟨i, hi⟩)
  · rcases (mem_labels_stepPath M _ (F.nonempty j) _).mp hj with hj | ⟨y, hy, he'⟩
    · exact Finset.disjoint_left.mp hfresh (he ▸ (M.color x).property)
        ((F.mem_colors g).mpr ⟨j, hj⟩)
    · have hxy : x = y := M.color.injective (Subtype.ext (he.trans he'.symm))
      have hlast : F.last i = F.last j := by
        change lastOrZero (F.path i) = lastOrZero (F.path j)
        exact hx.symm.trans ((congrArg Subtype.val hxy).trans hy)
      exact hij (F.last_injective hlast)

private theorem step_singleton_disjoint (i : F.Index) (N : Finset G)
    (hYN : Y ⊆ N) (hfresh : Disjoint N F.vertices) (g : ↥(N \ Y)) :
    List.Disjoint (stepPath M (F.path i)) [g.val] := by
  apply List.disjoint_left.mpr
  intro x hx hx'
  have he : x = g.val := by simpa using hx'
  subst x
  rcases (mem_stepPath M _ _).mp hx with h | ⟨y, hy, he⟩
  · exact Finset.disjoint_left.mp hfresh (Finset.mem_sdiff.mp g.property).1
      ((F.mem_vertices _).mpr ⟨i, h⟩)
  · exact (Finset.mem_sdiff.mp g.property).2 (he ▸ (M.endpoint y).property)

/-- Each old path is extended at most once; unmatched new heads are retained
as singletons. No perfect matching is assumed. -/
def extend (N : Finset G) (hX : X ⊆ F.ends) (hYN : Y ⊆ N)
    (hNV : Disjoint N F.vertices) (hCF : Disjoint C F.colors) : Family G where
  Index := Sum F.Index ↥(N \ Y)
  indexFintype := inferInstance
  path := Sum.elim (fun i => stepPath M (F.path i)) (fun g => [g.val])
  nonempty := by
    intro i
    cases i with
    | inl i => exact stepPath_nonempty M _ (F.nonempty i)
    | inr g => simp
  simple := by
    intro i
    cases i with
    | inl i => exact F.step_simple M i (Finset.disjoint_of_subset_left hYN hNV)
    | inr g => simp
  disjoint := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        exact F.step_disjoint M i j (fun h => hij (congrArg Sum.inl h))
          (Finset.disjoint_of_subset_left hYN hNV)
      | inr g => exact F.step_singleton_disjoint M i N hYN hNV g
    | inr g =>
      cases j with
      | inl j => exact (F.step_singleton_disjoint M j N hYN hNV g).symm
      | inr g' =>
        change List.Disjoint [g.val] [g'.val]
        simp only [List.disjoint_singleton, List.mem_singleton]
        intro h
        exact hij (congrArg Sum.inr (Subtype.ext h.symm))
  rainbow := by
    intro i
    cases i with
    | inl i => exact F.step_rainbow M i hCF
    | inr g => simp [labels, edgeLabels]
  color_disjoint := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact F.step_color_disjoint M i j (fun h => hij (congrArg Sum.inl h)) hCF
      | inr g => simp [labels, edgeLabels]
    | inr g => simp [labels, edgeLabels]

section Inventories
variable (N : Finset G) (hX : X ⊆ F.ends) (hYN : Y ⊆ N)
    (hNV : Disjoint N F.vertices) (hCF : Disjoint C F.colors)

@[simp] theorem extend_vertices :
    (F.extend M N hX hYN hNV hCF).vertices = F.vertices ∪ N := by
  ext g
  rw [mem_vertices, Finset.mem_union, F.mem_vertices]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | inl i =>
      rcases (mem_stepPath M _ _).mp hi with hi | ⟨x, hx, he⟩
      · exact Or.inl ⟨i, hi⟩
      · exact Or.inr (hYN (he ▸ (M.endpoint x).property))
    | inr g' =>
      have he : g = g'.val := by simpa [extend] using hi
      exact Or.inr (he ▸ (Finset.mem_sdiff.mp g'.property).1)
  · rintro (⟨i, hi⟩ | hg)
    · exact ⟨Sum.inl i, (mem_stepPath M _ _).mpr (Or.inl hi)⟩
    · by_cases hgY : g ∈ Y
      · obtain ⟨x, hx⟩ := M.endpoint.surjective ⟨g, hgY⟩
        obtain ⟨i, hi⟩ := (F.mem_ends x.val).mp (hX x.property)
        exact ⟨Sum.inl i, (mem_stepPath M _ _).mpr
          (Or.inr ⟨x, hi.symm, congrArg Subtype.val hx⟩)⟩
      · exact ⟨Sum.inr ⟨g, Finset.mem_sdiff.mpr ⟨hg, hgY⟩⟩, by simp [extend]⟩

@[simp] theorem extend_colors :
    (F.extend M N hX hYN hNV hCF).colors = F.colors ∪ C := by
  ext g
  rw [mem_colors, Finset.mem_union, F.mem_colors]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | inl i =>
      rcases (mem_labels_stepPath M _ (F.nonempty i) _).mp hi with hi | ⟨x, hx, he⟩
      · exact Or.inl ⟨i, hi⟩
      · exact Or.inr (he ▸ (M.color x).property)
    | inr g' => simp [extend, labels, edgeLabels] at hi
  · rintro (⟨i, hi⟩ | hg)
    · exact ⟨Sum.inl i, (mem_labels_stepPath M _ (F.nonempty i) _).mpr (Or.inl hi)⟩
    · obtain ⟨x, hx⟩ := M.color.surjective ⟨g, hg⟩
      obtain ⟨i, hi⟩ := (F.mem_ends x.val).mp (hX x.property)
      exact ⟨Sum.inl i, (mem_labels_stepPath M _ (F.nonempty i) _).mpr
        (Or.inr ⟨x, hi.symm, congrArg Subtype.val hx⟩)⟩

@[simp] theorem extend_starts :
    (F.extend M N hX hYN hNV hCF).starts = F.starts ∪ (N \ Y) := by
  ext g
  rw [mem_starts, Finset.mem_union, F.mem_starts]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | inl i => exact Or.inl ⟨i, (first_stepPath M _ (F.nonempty i)).symm.trans hi⟩
    | inr g' =>
      have he : g'.val = g := hi
      exact Or.inr (he ▸ g'.property)
  · rintro (⟨i, hi⟩ | hg)
    · exact ⟨Sum.inl i, (first_stepPath M _ (F.nonempty i)).trans hi⟩
    · exact ⟨Sum.inr ⟨g, hg⟩, rfl⟩

@[simp] theorem extend_ends :
    (F.extend M N hX hYN hNV hCF).ends = (F.ends \ X) ∪ N := by
  ext g
  rw [mem_ends, Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | inl i =>
      change lastOrZero (stepPath M (F.path i)) = g at hi
      rw [last_stepPath] at hi
      split_ifs at hi with hx
      · exact Or.inr (hYN (hi ▸ (M.endpoint _).property))
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨(F.mem_ends g).mpr ⟨i, hi⟩, by simpa [← hi] using hx⟩)
    | inr g' =>
      have he : g'.val = g := hi
      exact Or.inr (he ▸ (Finset.mem_sdiff.mp g'.property).1)
  · rintro (hg | hg)
    · obtain ⟨i, hi⟩ := (F.mem_ends g).mp (Finset.mem_sdiff.mp hg).1
      have hx : lastOrZero (F.path i) ∉ X := by
        change F.last i ∉ X
        simpa [hi] using (Finset.mem_sdiff.mp hg).2
      refine ⟨Sum.inl i, ?_⟩
      change lastOrZero (stepPath M (F.path i)) = g
      rw [last_stepPath, dif_neg hx]
      exact hi
    · by_cases hgY : g ∈ Y
      · obtain ⟨x, hx⟩ := M.endpoint.surjective ⟨g, hgY⟩
        obtain ⟨i, hi⟩ := (F.mem_ends x.val).mp (hX x.property)
        have htail : lastOrZero (F.path i) ∈ X := by
          change F.last i ∈ X
          rw [hi]
          exact x.property
        refine ⟨Sum.inl i, ?_⟩
        change lastOrZero (stepPath M (F.path i)) = g
        rw [last_stepPath, dif_pos htail]
        have he : (⟨lastOrZero (F.path i), htail⟩ : X) = x := Subtype.ext hi
        simpa only [he] using congrArg Subtype.val hx
      · exact ⟨Sum.inr ⟨g, Finset.mem_sdiff.mpr ⟨hg, hgY⟩⟩, rfl⟩

/-- The component count uses actual matching bijections and actual fresh
vertices, with no list-length/cardinality identification left unpaid. -/
theorem extend_count :
    Fintype.card (F.extend M N hX hYN hNV hCF).Index + C.card =
      Fintype.card F.Index + N.card := by
  change Fintype.card (Sum F.Index ↥(N \ Y)) + C.card = _
  rw [Fintype.card_sum, Fintype.card_coe]
  have hc : C.card = Y.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr (M.color.symm.trans M.endpoint)
  have hn := Finset.card_sdiff_add_card_eq_card hYN
  omega

end Inventories
end Family

/-- No edge is invented when isolated leftover vertices are added. -/
def emptyMatching : PhysicalDifferenceMatching (∅ : Finset G) ∅ ∅ where
  endpoint := Equiv.refl _
  color := Equiv.refl _
  difference := by intro x; exact False.elim (Finset.notMem_empty _ x.property)

end
end EndpointFactor.OrdinaryFragments
