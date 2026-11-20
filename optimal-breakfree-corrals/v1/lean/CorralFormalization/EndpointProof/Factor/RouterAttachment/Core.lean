import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Outcome

/-! # Splice actual prefix segments to actual disjoint ordinary paths -/

open scoped Classical BigOperators
namespace EndpointFactor.RouterAttachment
open OrdinaryFragments FragmentChecksum
noncomputable section
universe u v
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

private theorem pairwise_from_mem {I : Type v} {R : I → I → Prop}
    (hsymm : ∀ i j, R i j → R j i) {l : List I} (h : l.Pairwise R)
    {i j : I} (hi : i ∈ l) (hj : j ∈ l) (hij : i ≠ j) : R i j := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.pairwise_cons] at h
    by_cases hiA : i = a
    · subst i
      have hjl : j ∈ l := (List.mem_cons.mp hj).resolve_left (Ne.symm hij)
      exact h.1 j hjl
    · have hil : i ∈ l := (List.mem_cons.mp hi).resolve_left hiA
      by_cases hjA : j = a
      · subst j
        exact hsymm a i (h.1 i hil)
      · exact ih h.2 hil ((List.mem_cons.mp hj).resolve_left hjA)

theorem parts_of_nodup {n : ℕ} {V : Type v} (p : Fin n → List V)
    (h : ((List.finRange n).flatMap p).Nodup) :
    (∀ i, (p i).Nodup) ∧ (∀ i j, i ≠ j → List.Disjoint (p i) (p j)) := by
  have hp := List.nodup_flatMap.mp h
  refine ⟨fun i => hp.1 i (by simp), ?_⟩
  intro i j hij
  exact pairwise_from_mem (fun _ _ h => h.symm) hp.2 (by simp) (by simp) hij

/-- No edge is duplicated at the shared prefix/ordinary endpoint. -/
theorem labels_body_append (P : Segment G) (q : List G)
    (hhead : q.head? = some P.last) :
    labels (P.body ++ q) = P.colors (fun a b : G => b-a) ++ labels q := by
  cases q with
  | nil => simp at hhead
  | cons x xs =>
    have hx : x = P.last := by simpa using hhead
    subst x
    exact edgeLabels_append_pivot _ _ _ _

variable {n : ℕ}

def bodyInventory (P : Fin n → Segment G) : Finset G :=
  Finset.univ.biUnion (fun i => (P i).body.toFinset)
def colorInventory (P : Fin n → Segment G) : Finset G :=
  Finset.univ.biUnion (fun i => ((P i).colors (fun a b : G => b-a)).toFinset)

@[simp] theorem mem_bodyInventory (P : Fin n → Segment G) (g : G) :
    g ∈ bodyInventory P ↔ ∃ i, g ∈ (P i).body := by simp [bodyInventory]
@[simp] theorem mem_colorInventory (P : Fin n → Segment G) (g : G) :
    g ∈ colorInventory P ↔ ∃ i, g ∈ (P i).colors (fun a b : G => b-a) := by simp [colorInventory]

section Splice
variable (F : Family G) (P : Fin n → Segment G) (e : Fin n ≃ F.Index)
    (hjoin : ∀ i, (P i).last = F.first (e i))
    (hvertices : ((List.finRange n).flatMap (fun i => (P i).vertices)).Nodup)
    (hcolors : ((List.finRange n).flatMap (fun i => (P i).colors (fun a b : G => b-a))).Nodup)
    (hbodyfresh : Disjoint (bodyInventory P) F.vertices)
    (hcolorfresh : Disjoint (colorInventory P) F.colors)

include hjoin in
private theorem join_head (k : F.Index) : (F.path k).head? = some (P (e.symm k)).last := by
  have h : (F.path k).head? = some (F.first k) := by
    cases hp : F.path k with
    | nil => exact False.elim (F.nonempty _ hp)
    | cons a tail => simp [Family.first, firstOrZero, hp]
  simpa only [hjoin, e.apply_symm_apply] using h

include hbodyfresh in
private theorem body_fresh (i : Fin n) (k : F.Index) : List.Disjoint (P i).body (F.path k) := by
  apply List.disjoint_left.mpr
  intro g hg hg'
  exact Finset.disjoint_left.mp hbodyfresh ((mem_bodyInventory P g).mpr ⟨i,hg⟩)
    ((F.mem_vertices g).mpr ⟨k,hg'⟩)

include hcolorfresh in
private theorem color_fresh (i : Fin n) (k : F.Index) :
    List.Disjoint ((P i).colors (fun a b : G => b-a)) (labels (F.path k)) := by
  apply List.disjoint_left.mpr
  intro g hg hg'
  exact Finset.disjoint_left.mp hcolorfresh ((mem_colorInventory P g).mpr ⟨i,hg⟩)
    ((F.mem_colors g).mpr ⟨k,hg'⟩)

/-- The key set remains the old family's actual finite key type; this
also works when `G` lies in an arbitrary universe. -/
def prepend : Family G where
  Index := F.Index
  indexFintype := F.indexFintype
  path := fun k => (P (e.symm k)).body ++ F.path k
  nonempty := by intro k; simp [Segment.body]
  simple := by
    intro k
    exact (((parts_of_nodup _ hvertices).1 (e.symm k)).of_append_left).append
      (F.simple _) (body_fresh F P hbodyfresh _ k)
  disjoint := by
    intro i j hij
    apply List.disjoint_left.mpr
    intro g hi hj
    rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hj with hj | hj
      · exact List.disjoint_left.mp ((parts_of_nodup _ hvertices).2 (e.symm i) (e.symm j)
          (fun h => hij (e.symm.injective h))) (List.mem_append_left _ hi) (List.mem_append_left _ hj)
      · exact Finset.disjoint_left.mp hbodyfresh ((mem_bodyInventory P g).mpr ⟨e.symm i,hi⟩)
          ((F.mem_vertices g).mpr ⟨j,hj⟩)
    · rcases List.mem_append.mp hj with hj | hj
      · exact Finset.disjoint_left.mp hbodyfresh ((mem_bodyInventory P g).mpr ⟨e.symm j,hj⟩)
          ((F.mem_vertices g).mpr ⟨i,hi⟩)
      · exact List.disjoint_left.mp (F.disjoint i j hij) hi hj
  rainbow := by
    intro k
    rw [labels_body_append _ _ (join_head F P e hjoin k)]
    exact ((parts_of_nodup _ hcolors).1 (e.symm k)).append (F.rainbow _)
      (color_fresh F P hcolorfresh _ k)
  color_disjoint := by
    intro i j hij
    rw [labels_body_append _ _ (join_head F P e hjoin i),
      labels_body_append _ _ (join_head F P e hjoin j)]
    apply List.disjoint_left.mpr
    intro c hi hj
    rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hj with hj | hj
      · exact List.disjoint_left.mp ((parts_of_nodup _ hcolors).2 (e.symm i) (e.symm j)
          (fun h => hij (e.symm.injective h))) hi hj
      · exact Finset.disjoint_left.mp hcolorfresh ((mem_colorInventory P c).mpr ⟨e.symm i,hi⟩)
          ((F.mem_colors c).mpr ⟨j,hj⟩)
    · rcases List.mem_append.mp hj with hj | hj
      · exact Finset.disjoint_left.mp hcolorfresh ((mem_colorInventory P c).mpr ⟨e.symm j,hj⟩)
          ((F.mem_colors c).mpr ⟨i,hi⟩)
      · exact List.disjoint_left.mp (F.color_disjoint i j hij) hi hj

@[simp] theorem prepend_vertices :
    (prepend F P e hjoin hvertices hcolors hbodyfresh hcolorfresh).vertices =
      bodyInventory P ∪ F.vertices := by
  ext g
  simp only [Family.mem_vertices, Finset.mem_union, mem_bodyInventory]
  constructor
  · rintro ⟨k,hk⟩
    rcases List.mem_append.mp hk with hk | hk
    · exact Or.inl ⟨e.symm k,hk⟩
    · exact Or.inr ⟨k,hk⟩
  · rintro (⟨i,hi⟩ | ⟨k,hk⟩)
    · refine ⟨e i,?_⟩
      change g ∈ (P (e.symm (e i))).body ++ F.path (e i)
      simpa using List.mem_append_left (F.path (e i)) hi
    · exact ⟨k,List.mem_append_right _ hk⟩

@[simp] theorem prepend_colors :
    (prepend F P e hjoin hvertices hcolors hbodyfresh hcolorfresh).colors =
      colorInventory P ∪ F.colors := by
  ext g
  simp only [Family.mem_colors, Finset.mem_union, mem_colorInventory]
  constructor
  · rintro ⟨k,hk⟩
    change g ∈ labels ((P (e.symm k)).body ++ F.path k) at hk
    rw [labels_body_append _ _ (join_head F P e hjoin k)] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact Or.inl ⟨e.symm k,hk⟩
    · exact Or.inr ⟨k,hk⟩
  · rintro (⟨i,hi⟩ | ⟨k,hk⟩)
    · refine ⟨e i,?_⟩
      change g ∈ labels ((P (e.symm (e i))).body ++ F.path (e i))
      rw [labels_body_append _ _ (join_head F P e hjoin (e i))]
      exact List.mem_append_left _ (by simpa using hi)
    · refine ⟨k,?_⟩
      change g ∈ labels ((P (e.symm k)).body ++ F.path k)
      rw [labels_body_append _ _ (join_head F P e hjoin k)]
      exact List.mem_append_right _ hk

@[simp] theorem prepend_first (k : F.Index) :
    (prepend F P e hjoin hvertices hcolors hbodyfresh hcolorfresh).first k = (P (e.symm k)).first := by
  simp [prepend, Family.first, firstOrZero, Segment.body]
@[simp] theorem prepend_last (k : F.Index) :
    (prepend F P e hjoin hvertices hcolors hbodyfresh hcolorfresh).last k = F.last k := by
  simp [prepend, Family.last, lastOrZero, List.getLast?_append,
    List.getLast?_eq_some_getLast (F.nonempty k)]

@[simp] theorem prepend_starts :
    (prepend F P e hjoin hvertices hcolors hbodyfresh hcolorfresh).starts =
      Finset.univ.image (fun i => (P i).first) := by
  ext g
  simp only [Family.mem_starts, prepend_first, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k,hk⟩; exact ⟨e.symm k,hk⟩
  · rintro ⟨i,hi⟩; exact ⟨e i,by simpa using hi⟩

@[simp] theorem prepend_ends :
    (prepend F P e hjoin hvertices hcolors hbodyfresh hcolorfresh).ends = F.ends := by
  ext g
  simp only [Family.mem_ends]
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k,(prepend_last F P e hjoin hvertices hcolors hbodyfresh hcolorfresh k).symm.trans hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,(prepend_last F P e hjoin hvertices hcolors hbodyfresh hcolorfresh k).trans hk⟩

end Splice
end
end EndpointFactor.RouterAttachment
