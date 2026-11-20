import CorralFormalization.EndpointProof.Factor.PhysicalNearMatching
import CorralFormalization.EndpointProof.Factor.FragmentChecksum

/-!
# Actual disjoint directed fragment families

The index type labels actual, pairwise vertex-disjoint nonempty lists.  All
inventories below are physical finite sets; their cardinalities are justified
by injectivity or `Nodup`, never by an unverified list length.
-/

open scoped BigOperators Classical
namespace EndpointFactor.OrdinaryFragments

open EndpointMatching.AbsorptionAssembly FragmentChecksum

noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

abbrev labels (p : List G) : List G := edgeLabels (fun a b : G => b-a) p

structure Family (G : Type u) [AddCommGroup G] where
  Index : Type u
  indexFintype : Fintype Index
  path : Index → List G
  nonempty : ∀ i, path i ≠ []
  simple : ∀ i, (path i).Nodup
  disjoint : ∀ i j, i ≠ j → List.Disjoint (path i) (path j)
  rainbow : ∀ i, (labels (path i)).Nodup
  color_disjoint : ∀ i j, i ≠ j → List.Disjoint (labels (path i)) (labels (path j))

attribute [instance] Family.indexFintype

namespace Family
variable (F : Family G)

def vertices : Finset G := Finset.univ.biUnion (fun i => (F.path i).toFinset)
def colors : Finset G := Finset.univ.biUnion (fun i => (labels (F.path i)).toFinset)
def first (i : F.Index) : G := firstOrZero (F.path i)
def last (i : F.Index) : G := lastOrZero (F.path i)
def starts : Finset G := Finset.univ.image F.first
def ends : Finset G := Finset.univ.image F.last

def lists : List (List G) := (Finset.univ : Finset F.Index).toList.map F.path

@[simp] theorem mem_vertices (x : G) : x ∈ F.vertices ↔ ∃ i, x ∈ F.path i := by
  simp [vertices]
@[simp] theorem mem_colors (c : G) : c ∈ F.colors ↔ ∃ i, c ∈ labels (F.path i) := by
  simp [colors]
@[simp] theorem mem_starts (x : G) : x ∈ F.starts ↔ ∃ i, F.first i = x := by
  simp [starts]
@[simp] theorem mem_ends (x : G) : x ∈ F.ends ↔ ∃ i, F.last i = x := by
  simp [ends]

theorem first_mem (i : F.Index) : F.first i ∈ F.path i :=
  firstOrZero_mem (F.nonempty i)
theorem last_mem (i : F.Index) : F.last i ∈ F.path i :=
  lastOrZero_mem (F.nonempty i)

theorem first_injective : Function.Injective F.first := by
  intro i j h
  by_contra hij
  exact List.disjoint_left.mp (F.disjoint i j hij) (F.first_mem i)
    (by simpa only [h] using F.first_mem j)

theorem last_injective : Function.Injective F.last := by
  intro i j h
  by_contra hij
  exact List.disjoint_left.mp (F.disjoint i j hij) (F.last_mem i)
    (by simpa only [h] using F.last_mem j)

@[simp] theorem starts_card : F.starts.card = Fintype.card F.Index := by
  rw [starts, Finset.card_image_of_injective _ F.first_injective, Finset.card_univ]
@[simp] theorem ends_card : F.ends.card = Fintype.card F.Index := by
  rw [ends, Finset.card_image_of_injective _ F.last_injective, Finset.card_univ]

theorem starts_subset : F.starts ⊆ F.vertices := by
  intro x hx
  obtain ⟨i, rfl⟩ := (F.mem_starts x).mp hx
  exact (F.mem_vertices _).mpr ⟨i, F.first_mem i⟩
theorem ends_subset : F.ends ⊆ F.vertices := by
  intro x hx
  obtain ⟨i, rfl⟩ := (F.mem_ends x).mp hx
  exact (F.mem_vertices _).mpr ⟨i, F.last_mem i⟩

@[simp] theorem mem_lists (p : List G) : p ∈ F.lists ↔ ∃ i, F.path i = p := by
  simp [lists]

theorem lists_nonempty : [] ∉ F.lists := by
  rintro h
  obtain ⟨i, hi⟩ := (F.mem_lists []).mp h
  exact F.nonempty i hi

theorem lists_simple : F.lists.flatten.Nodup := by
  change (((Finset.univ : Finset F.Index).toList.map F.path).flatten).Nodup
  change ((Finset.univ : Finset F.Index).toList.flatMap F.path).Nodup
  apply List.nodup_flatMap.mpr
  refine ⟨fun i _ => F.simple i, ?_⟩
  apply (Finset.nodup_toList _).imp_of_mem
  intro i j _ _ hij
  exact F.disjoint i j hij

theorem lists_rainbow : (F.lists.flatMap labels).Nodup := by
  rw [lists, List.flatMap_map]
  apply List.nodup_flatMap.mpr
  refine ⟨fun i _ => F.rainbow i, ?_⟩
  apply (Finset.nodup_toList _).imp_of_mem
  intro i j _ _ hij
  exact F.color_disjoint i j hij

@[simp] theorem lists_vertices : F.lists.flatten.toFinset = F.vertices := by
  ext x
  simp [lists, vertices]
@[simp] theorem lists_colors : (F.lists.flatMap labels).toFinset = F.colors := by
  ext x
  simp [lists, colors]
@[simp] theorem lists_starts : (F.lists.map firstOrZero).toFinset = F.starts := by
  ext x
  simp [lists, starts, first]
@[simp] theorem lists_ends : (F.lists.map lastOrZero).toFinset = F.ends := by
  ext x
  simp [lists, ends, last]
@[simp] theorem lists_length : F.lists.length = Fintype.card F.Index := by
  simp [lists]

theorem inventory_card : F.colors.card + Fintype.card F.Index = F.vertices.card := by
  have h := fragmentFamily_inventory_card F.lists F.vertices F.colors
    F.lists_nonempty F.lists_simple F.lists_rainbow F.lists_vertices F.lists_colors
  simpa using h

end Family

/-- A real isolated vertex is retained as its singleton path. -/
def singletons (S : Finset G) : Family G where
  Index := S
  indexFintype := inferInstance
  path := fun x => [x.val]
  nonempty := by simp
  simple := by simp
  disjoint := by
    intro i j hij
    simp only [List.disjoint_singleton, List.mem_singleton]
    exact fun h => hij (Subtype.ext h.symm)
  rainbow := by simp [labels, edgeLabels]
  color_disjoint := by simp [labels, edgeLabels]

@[simp] theorem singletons_vertices (S : Finset G) : (singletons S).vertices = S := by
  ext x
  rw [Family.mem_vertices]
  constructor
  · rintro ⟨i, hi⟩
    have he : x = i.val := by simpa [singletons] using hi
    exact he ▸ i.property
  · intro hx
    exact ⟨⟨x, hx⟩, by simp [singletons]⟩
@[simp] theorem singletons_colors (S : Finset G) : (singletons S).colors = ∅ := by
  ext c
  simp [Family.colors, singletons, labels, edgeLabels]
@[simp] theorem singletons_starts (S : Finset G) : (singletons S).starts = S := by
  ext x
  rw [Family.mem_starts]
  constructor
  · rintro ⟨i, hi⟩
    have he : i.val = x := by simpa [Family.first, singletons, firstOrZero] using hi
    exact he ▸ i.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
@[simp] theorem singletons_ends (S : Finset G) : (singletons S).ends = S := by
  ext x
  rw [Family.mem_ends]
  constructor
  · rintro ⟨i, hi⟩
    have he : i.val = x := by simpa [Family.last, singletons, lastOrZero] using hi
    exact he ▸ i.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
@[simp] theorem singletons_count (S : Finset G) :
    Fintype.card (singletons S).Index = S.card := Fintype.card_coe S

private theorem labels_append_one (p : List G) (hp : p ≠ []) (y : G) :
    labels (p ++ [y]) = labels p ++ [y-lastOrZero p] := by
  have he := List.dropLast_append_getLast hp
  calc
    labels (p ++ [y]) = labels (p.dropLast ++ p.getLast hp :: [y]) := by
      simpa [List.append_assoc] using congrArg (fun z : List G => labels (z ++ [y])) he.symm
    _ = labels (p.dropLast ++ [p.getLast hp]) ++ [y - p.getLast hp] := by
      rw [labels, edgeLabels_append_pivot]
      rfl
    _ = labels p ++ [y-lastOrZero p] := by
      rw [he]
      simp [lastOrZero, List.getLast?_eq_some_getLast hp]

/-- Append the actual matched head exactly when this path's end is a tail. -/
def stepPath {X Y C : Finset G} (M : PhysicalDifferenceMatching X Y C)
    (p : List G) : List G :=
  if h : lastOrZero p ∈ X then p ++ [(M.endpoint ⟨lastOrZero p, h⟩).val] else p

section Step
variable {X Y C : Finset G} (M : PhysicalDifferenceMatching X Y C)

@[simp] theorem stepPath_nonempty (p : List G) (hp : p ≠ []) : stepPath M p ≠ [] := by
  unfold stepPath
  split <;> simp_all

theorem mem_stepPath (p : List G) (g : G) :
    g ∈ stepPath M p ↔ g ∈ p ∨
      ∃ x : X, x.val = lastOrZero p ∧ (M.endpoint x).val = g := by
  unfold stepPath
  split_ifs with h
  · simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (hp | hg)
      · exact Or.inl hp
      · exact Or.inr ⟨⟨lastOrZero p, h⟩, rfl, hg.symm⟩
    · rintro (hp | ⟨x, hx, hg⟩)
      · exact Or.inl hp
      · right
        have he : x = ⟨lastOrZero p, h⟩ := Subtype.ext hx
        simpa [he] using hg.symm
  · constructor
    · exact Or.inl
    · rintro (hp | ⟨x, hx, _⟩)
      · exact hp
      · exact False.elim (h (hx ▸ x.property))

theorem first_stepPath (p : List G) (hp : p ≠ []) :
    firstOrZero (stepPath M p) = firstOrZero p := by
  unfold stepPath
  split_ifs <;> cases p <;> simp_all [firstOrZero]

theorem last_stepPath (p : List G) :
    lastOrZero (stepPath M p) =
      if h : lastOrZero p ∈ X then (M.endpoint ⟨lastOrZero p, h⟩).val else lastOrZero p := by
  unfold stepPath
  split_ifs <;> simp [lastOrZero]

theorem labels_stepPath (p : List G) (hp : p ≠ []) :
    labels (stepPath M p) = labels p ++
      if h : lastOrZero p ∈ X then [(M.color ⟨lastOrZero p, h⟩).val] else [] := by
  unfold stepPath
  split_ifs with h
  · rw [labels_append_one p hp]
    rw [M.difference]
  · simp

theorem mem_labels_stepPath (p : List G) (hp : p ≠ []) (g : G) :
    g ∈ labels (stepPath M p) ↔ g ∈ labels p ∨
      ∃ x : X, x.val = lastOrZero p ∧ (M.color x).val = g := by
  rw [labels_stepPath M p hp]
  split_ifs with h
  · simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (hp | hg)
      · exact Or.inl hp
      · exact Or.inr ⟨⟨lastOrZero p, h⟩, rfl, hg.symm⟩
    · rintro (hp | ⟨x, hx, hg⟩)
      · exact Or.inl hp
      · right
        have he : x = ⟨lastOrZero p, h⟩ := Subtype.ext hx
        simpa [he] using hg.symm
  · simp only [List.append_nil]
    constructor
    · exact Or.inl
    · rintro (hp | ⟨x, hx, _⟩)
      · exact hp
      · exact False.elim (h (hx ▸ x.property))

end Step

end
end EndpointFactor.OrdinaryFragments
