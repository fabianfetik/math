import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Layers

/-! # Primary paths, their genuine endpoints, and isolated remainder vertices -/

open scoped Classical BigOperators
namespace EndpointFactor.OrdinaryFragments
open EndpointMatching.AbsorptionAssembly FragmentChecksum
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

namespace Family
variable (F : Family G)

/-- Primary keys are selected by actual initial vertices. -/
def primary (B : Finset G) : Finset F.Index := Finset.univ.filter (fun i => F.first i ∈ B)
def primaryEnds (B : Finset G) : Finset G := (F.primary B).image F.last

def goodPrimaryEnds (B E : Finset G) : Finset G := F.primaryEnds B ∩ E

@[simp] theorem mem_primary (B : Finset G) (i : F.Index) :
    i ∈ F.primary B ↔ F.first i ∈ B := by simp [primary]
@[simp] theorem mem_primaryEnds (B : Finset G) (g : G) :
    g ∈ F.primaryEnds B ↔ ∃ i, F.first i ∈ B ∧ F.last i = g := by
  simp [primaryEnds]

theorem primaryEnds_subset (B : Finset G) : F.primaryEnds B ⊆ F.ends := by
  intro g hg
  obtain ⟨i, _, hi⟩ := (F.mem_primaryEnds B g).mp hg
  exact (F.mem_ends g).mpr ⟨i, hi⟩

theorem primary_card (B : Finset G) (hB : B ⊆ F.starts) :
    (F.primary B).card = B.card := by
  have he : (F.primary B).image F.first = B := by
    ext g
    simp only [Finset.mem_image, mem_primary]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hg
      obtain ⟨i, hi⟩ := (F.mem_starts g).mp (hB hg)
      exact ⟨i, hi.symm ▸ hg, hi⟩
  calc
    (F.primary B).card = ((F.primary B).image F.first).card :=
      (Finset.card_image_of_injective _ F.first_injective).symm
    _ = B.card := congrArg Finset.card he

theorem primaryEnds_card (B : Finset G) (hB : B ⊆ F.starts) :
    (F.primaryEnds B).card = B.card := by
  rw [primaryEnds, Finset.card_image_of_injective _ F.last_injective, F.primary_card B hB]

/-- Extra keys are actual components outside the primary family. -/
def extras (B : Finset G) : Finset F.Index := Finset.univ \ F.primary B

@[simp] theorem mem_extras (B : Finset G) (i : F.Index) :
    i ∈ F.extras B ↔ F.first i ∉ B := by simp [extras]

theorem extras_card (B : Finset G) (hB : B ⊆ F.starts) (ℓ H : ℕ)
    (hsize : B.card = ℓ) (hcount : Fintype.card F.Index = ℓ+H) :
    (F.extras B).card = H := by
  have h := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (F.primary B))
  rw [Finset.card_univ, F.primary_card B hB, hsize, hcount] at h
  change (Finset.univ \ F.primary B).card = H
  omega

theorem bad_primary_card (B E : Finset G) :
    ((F.primary B).filter (fun i => F.last i ∉ E)).card =
      (F.primaryEnds B \ E).card := by
  let bad := (F.primary B).filter (fun i => F.last i ∉ E)
  have he : bad.image F.last = F.primaryEnds B \ E := by
    ext g
    simp only [Finset.mem_image, Finset.mem_filter, mem_primary, Finset.mem_sdiff,
      mem_primaryEnds, bad]
    constructor
    · rintro ⟨i, ⟨hi, hiE⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, hiE⟩
    · rintro ⟨⟨i, hi, rfl⟩, hiE⟩
      exact ⟨i, ⟨hi, hiE⟩, rfl⟩
  calc
    bad.card = (bad.image F.last).card :=
      (Finset.card_image_of_injective _ F.last_injective).symm
    _ = (F.primaryEnds B \ E).card := congrArg Finset.card he

/-- At most `h` primary endpoints can be outside a last layer of size `ℓ`
when the actual endpoint inventory consists of `ℓ+h` distinct vertices. -/
theorem bad_primary_le (B E : Finset G) (hE : E ⊆ F.ends) (ℓ h : ℕ)
    (hsize : E.card = ℓ) (hcount : Fintype.card F.Index = ℓ+h) :
    ((F.primary B).filter (fun i => F.last i ∉ E)).card ≤ h := by
  let bad := (F.primary B).filter (fun i => F.last i ∉ E)
  have hsub : bad.image F.last ⊆ F.ends \ E := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_sdiff.mpr ⟨(F.mem_ends _).mpr ⟨i, rfl⟩, (Finset.mem_filter.mp hi).2⟩
  have he := Finset.card_sdiff_add_card_eq_card hE
  rw [F.ends_card, hcount, hsize] at he
  have hb := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ F.last_injective] at hb
  change bad.card ≤ h
  omega

/-- This is the actual donor-endpoint set `Z₀`: it consists only of ends
of original primary paths, and all of its points lie in the last layer. -/
theorem goodPrimaryEnds_large (B E : Finset G) (hB : B ⊆ F.starts)
    (hE : E ⊆ F.ends) (ℓ h : ℕ) (hBsize : B.card = ℓ)
    (hEsize : E.card = ℓ) (hcount : Fintype.card F.Index = ℓ+h) :
    (E \ F.goodPrimaryEnds B E).card ≤ h := by
  have hp : (F.primaryEnds B).card = ℓ := by rw [F.primaryEnds_card B hB, hBsize]
  have hdiff : F.primaryEnds B \ E ⊆ F.ends \ E :=
    Finset.sdiff_subset_sdiff (F.primaryEnds_subset B) Finset.Subset.rfl
  have hde := Finset.card_sdiff_add_card_eq_card hE
  rw [F.ends_card, hcount, hEsize] at hde
  have hbound := Finset.card_le_card hdiff
  have hsplit := Finset.card_union_add_card_inter (F.primaryEnds B) E
  have hsub := Finset.card_le_card (Finset.subset_union_right : E ⊆ F.primaryEnds B ∪ E)
  have hpart := Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_left : F.primaryEnds B ∩ E ⊆ F.primaryEnds B)
  have heq : F.primaryEnds B \ (F.primaryEnds B ∩ E) = F.primaryEnds B \ E := by
    ext g
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [heq] at hpart
  have hpartE := Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_right : F.primaryEnds B ∩ E ⊆ E)
  change (E \ (F.primaryEnds B ∩ E)).card ≤ h
  omega

/-- Add every actual leftover point, keeping the original paths literally
unchanged. This is separate from adding edges by a near matching. -/
def addIsolates (L : Finset G) (hfresh : Disjoint L F.vertices) : Family G :=
  F.extend emptyMatching L (by simp) (by simp) hfresh (by simp)

@[simp] theorem addIsolates_vertices (L : Finset G) (hfresh : Disjoint L F.vertices) :
    (F.addIsolates L hfresh).vertices = F.vertices ∪ L := by
  simp [addIsolates]
@[simp] theorem addIsolates_colors (L : Finset G) (hfresh : Disjoint L F.vertices) :
    (F.addIsolates L hfresh).colors = F.colors := by
  simp [addIsolates]
@[simp] theorem addIsolates_starts (L : Finset G) (hfresh : Disjoint L F.vertices) :
    (F.addIsolates L hfresh).starts = F.starts ∪ L := by
  simp [addIsolates]
@[simp] theorem addIsolates_ends (L : Finset G) (hfresh : Disjoint L F.vertices) :
    (F.addIsolates L hfresh).ends = F.ends ∪ L := by
  simp [addIsolates]
@[simp] theorem addIsolates_count (L : Finset G) (hfresh : Disjoint L F.vertices) :
    Fintype.card (F.addIsolates L hfresh).Index = Fintype.card F.Index + L.card := by
  change Fintype.card (Sum F.Index ↥(L \ (∅ : Finset G))) = _
  rw [Fintype.card_sum, Fintype.card_coe, Finset.sdiff_empty]

theorem addIsolates_primaryEnds (L B : Finset G) (hfresh : Disjoint L F.vertices)
    (hB : B ⊆ F.vertices) :
    (F.addIsolates L hfresh).primaryEnds B = F.primaryEnds B := by
  ext g
  simp only [mem_primaryEnds]
  constructor
  · rintro ⟨i, hi, he⟩
    cases i with
    | inl i =>
      exact ⟨i, by simpa [addIsolates, extend, first, stepPath] using hi,
        by simpa [addIsolates, extend, last, stepPath] using he⟩
    | inr x =>
      have hxB : x.val ∈ B := by simpa [addIsolates, extend, first, firstOrZero] using hi
      exact False.elim (Finset.disjoint_left.mp hfresh
        (Finset.mem_sdiff.mp x.property).1 (hB hxB))
  · rintro ⟨i, hi, he⟩
    refine ⟨Sum.inl i, ?_, ?_⟩
    · simpa [addIsolates, extend, first, stepPath] using hi
    · simpa [addIsolates, extend, last, stepPath] using he

/-- Isolated remainder points do not create bad primary ends. -/
theorem addIsolates_bad_primary_le (L B E : Finset G)
    (hfresh : Disjoint L F.vertices) (hB : B ⊆ F.vertices)
    (hE : E ⊆ F.ends) (ℓ h : ℕ) (hsize : E.card = ℓ)
    (hcount : Fintype.card F.Index = ℓ+h) :
    (((F.addIsolates L hfresh).primary B).filter
      (fun i => (F.addIsolates L hfresh).last i ∉ E)).card ≤ h := by
  rw [bad_primary_card, F.addIsolates_primaryEnds L B hfresh hB, ← F.bad_primary_card B E]
  exact F.bad_primary_le B E hE ℓ h hsize hcount

end Family

namespace LayerData
variable {j ℓ : ℕ} (D : LayerData G j ℓ)

/-- Complete ordinary decomposition, with the true `w` remainder vertices.
`F₀` records the original ordinary primary paths, before any attachment.
The displayed equality of primary endpoint sets means the leftover
singletons cannot silently weaken the `h` bound to `h+w`. -/
theorem exists_with_leftovers (L : Finset G) (hL : Disjoint L D.vertices) :
    ∃ F₀ F : Family G,
      F₀.vertices = D.vertices ∧ F₀.colors = D.colors ∧
      D.layer 0 ⊆ F₀.starts ∧ D.layer (Fin.last j) ⊆ F₀.ends ∧
      Fintype.card F₀.Index = ℓ+D.deficit ∧
      F.vertices = D.vertices ∪ L ∧ F.colors = D.colors ∧
      D.layer 0 ⊆ F.starts ∧ D.layer (Fin.last j) ⊆ F.ends ∧
      Fintype.card F.Index = ℓ+D.deficit+L.card ∧
      (F.primary (D.layer 0)).card = ℓ ∧
      F.primaryEnds (D.layer 0) = F₀.primaryEnds (D.layer 0) ∧
      (D.layer (Fin.last j) \ F.goodPrimaryEnds (D.layer 0) (D.layer (Fin.last j))).card ≤ D.deficit := by
  obtain ⟨F₀, hV, hC, hS, hE, hcount⟩ := D.exists_family
  have hLf : Disjoint L F₀.vertices := by rw [hV]; exact hL
  let F := F₀.addIsolates L hLf
  have hS' : D.layer 0 ⊆ F.starts := by
    rw [Family.addIsolates_starts]
    exact hS.trans Finset.subset_union_left
  have hE' : D.layer (Fin.last j) ⊆ F.ends := by
    rw [Family.addIsolates_ends]
    exact hE.trans Finset.subset_union_left
  have hB : D.layer 0 ⊆ F₀.vertices := by
    rw [hV]
    intro g hg
    exact (D.mem_vertices _).mpr ⟨0, hg⟩
  have hp : F.primaryEnds (D.layer 0) = F₀.primaryEnds (D.layer 0) :=
    F₀.addIsolates_primaryEnds L (D.layer 0) hLf hB
  refine ⟨F₀, F, hV, hC, hS, hE, hcount, ?_, ?_, hS', hE', ?_, ?_, hp, ?_⟩
  · rw [Family.addIsolates_vertices, hV]
  · rw [Family.addIsolates_colors, hC]
  · rw [Family.addIsolates_count, hcount]
  · rw [F.primary_card _ hS', D.size]
  · rw [Family.goodPrimaryEnds, hp]
    exact F₀.goodPrimaryEnds_large _ _ hS hE ℓ D.deficit (D.size _) (D.size _) hcount

end LayerData
end
end EndpointFactor.OrdinaryFragments
