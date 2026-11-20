import CorralFormalization.EndpointProof.Factor.CycleExpansion.Core

/-! # Mark virtual sources and retain every actual real colour exactly once -/

open scoped Classical BigOperators
namespace EndpointFactor.CycleExpansion
open OrdinaryFragments FragmentChecksum EndpointMatching.AbsorptionAssembly
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

private theorem edge_source_dropLast (p : List G) (e : G × G)
    (he : e ∈ edgeLabels (fun a b : G => (a,b)) p) : e.1 ∈ p.dropLast := by
  induction p with
  | nil => simp [edgeLabels] at he
  | cons a p ih =>
    cases p with
    | nil => simp [edgeLabels] at he
    | cons b p =>
      rcases List.mem_cons.mp he with rfl | he
      · simp [List.dropLast_cons_cons]
      · have h := ih he
        simpa [List.dropLast_cons_cons] using List.mem_cons_of_mem a h

/-- An actual family endpoint cannot be an internal source on any path. -/
theorem internal_source_not_end (F : Family G) (k : F.Index) (e : G × G)
    (he : e ∈ edgeLabels (fun a b : G => (a,b)) (F.path k)) : e.1 ∉ F.ends := by
  have hs := edge_source_dropLast (F.path k) e he
  have hp : e.1 ∈ F.path k := List.mem_of_mem_dropLast hs
  rintro h
  obtain ⟨j,hj⟩ := (F.mem_ends e.1).mp h
  by_cases hjk : j = k
  · subst j
    have hl : (F.path k).getLast (F.nonempty k) = F.last k := by
      simp [Family.last,lastOrZero,List.getLast?_eq_some_getLast (F.nonempty k)]
    have hshape : (F.path k).dropLast ++ [F.last k] = F.path k := by
      rw [← hl,List.dropLast_append_getLast]
    have hn : ((F.path k).dropLast ++ [F.last k]).Nodup := hshape.symm ▸ F.simple k
    exact (List.nodup_append.mp hn).2.2 e.1 hs (F.last k) (by simp) hj.symm
  · exact List.disjoint_left.mp (F.disjoint k j (Ne.symm hjk)) hp (by simpa [hj] using F.last_mem j)

theorem internal_filter (F : Family G) (Y : Finset G) (hY : Y ⊆ F.ends) (k : F.Index) :
    (edgeLabels (fun a b : G => (a,b)) (F.path k)).filter (fun e => decide (e.1 ∉ Y)) =
      edgeLabels (fun a b : G => (a,b)) (F.path k) := by
  apply List.filter_eq_self.mpr
  intro e he
  simp only [decide_eq_true_eq]
  exact fun hy => internal_source_not_end F k e he (hY hy)

variable {n : ℕ}

def realSegmentLabels (F : Family G) (key : Fin n ≃ F.Index) (ρ : Equiv.Perm (Fin n))
    (Y : Finset G) (i : Fin n) : List G :=
  (((trackSegment F key ρ i).colors (fun a b : G => (a,b))).filter
    (fun e => decide (e.1 ∉ Y))).map (fun e => e.2-e.1)

theorem realSegmentLabels_eq (F : Family G) (key : Fin n ≃ F.Index)
    (ρ : Equiv.Perm (Fin n)) (Y : Finset G) (hY : Y ⊆ F.ends) (i : Fin n) :
    realSegmentLabels F key ρ Y i = labels (F.path (key i)) ++
      if F.last (key i) ∈ Y then [] else [F.first (key (ρ i))-F.last (key i)] := by
  unfold realSegmentLabels
  simp only [Segment.colors,Segment.vertices,trackSegment_body]
  rw [edgeLabels_append_one _ _ (F.nonempty _),List.filter_append,List.map_append,internal_filter F Y hY]
  have hmap : (edgeLabels (fun a b : G => (a,b)) (F.path (key i))).map (fun e => e.2-e.1) =
      labels (F.path (key i)) := (edgeLabels_map _ _ _).symm
  rw [hmap]
  have hl : (F.path (key i)).getLast (F.nonempty _) = F.last (key i) := by
    simp [Family.last,lastOrZero,List.getLast?_eq_some_getLast (F.nonempty _)]
  by_cases hi : F.last (key i) ∈ Y <;> simp [hl,hi,trackSegment]

theorem cyclicRealDifferences_eq (F : Family G) (key : Fin n ≃ F.Index)
    (ρ : Equiv.Perm (Fin n)) (root : Fin n) (hc : ρ.IsCycleOn Set.univ) (Y : Finset G) :
    CycleCut.cyclicRealDifferences Y (vertices F key ρ root hc) (vertices_nonempty F key ρ root hc) =
      (trackOrder ρ root hc).order.flatMap (realSegmentLabels F key ρ Y) := by
  unfold CycleCut.cyclicRealDifferences
  rw [cyclic_edges,List.filter_flatMap,List.map_flatMap]
  rfl

section Matching
variable (E S X Y H : Finset G) (M : PhysicalDifferenceMatching (E \ Y) (S \ X) H)
    (endAt : Fin n ≃ E)

def closingLabels (i : Fin n) : List G :=
  if hy : (endAt i).val ∈ Y then []
  else [(M.color ⟨(endAt i).val,Finset.mem_sdiff.mpr ⟨(endAt i).property,hy⟩⟩).val]

theorem mem_closingLabels (i : Fin n) (c : G) :
    c ∈ closingLabels E S X Y H M endAt i ↔
      ∃ hy : (endAt i).val ∉ Y,
        (M.color ⟨(endAt i).val,Finset.mem_sdiff.mpr ⟨(endAt i).property,hy⟩⟩).val = c := by
  unfold closingLabels
  split_ifs with hy
  · simp only [List.not_mem_nil,false_iff]
    rintro ⟨hny,_⟩
    exact hny hy
  · simp only [List.mem_singleton]
    constructor
    · intro h; exact ⟨hy,h.symm⟩
    · rintro ⟨_,h⟩; exact h.symm

theorem closingLabels_subset (i : Fin n) {c : G} (hc : c ∈ closingLabels E S X Y H M endAt i) : c ∈ H := by
  obtain ⟨hy,hc⟩ := (mem_closingLabels E S X Y H M endAt i c).mp hc
  exact hc ▸ (M.color _).property

theorem closingLabels_unique (i j : Fin n) {c : G}
    (hi : c ∈ closingLabels E S X Y H M endAt i)
    (hj : c ∈ closingLabels E S X Y H M endAt j) : i = j := by
  obtain ⟨hyi,hi⟩ := (mem_closingLabels E S X Y H M endAt i c).mp hi
  obtain ⟨hyj,hj⟩ := (mem_closingLabels E S X Y H M endAt j c).mp hj
  have hm := M.color.injective (Subtype.ext (hi.trans hj.symm))
  apply endAt.injective
  have hvals : (endAt i).val = (endAt j).val := congrArg (fun x : ↥(E \ Y) => x.val) hm
  exact Subtype.ext hvals

variable (F : Family G) (key : Fin n ≃ F.Index) (ρ : Equiv.Perm (Fin n))
    (hY : Y ⊆ F.ends) (hEnd : ∀ i, F.last (key i) = (endAt i).val)
    (hReal : ∀ i, ∀ hy : (endAt i).val ∉ Y,
      (M.color ⟨(endAt i).val,Finset.mem_sdiff.mpr ⟨(endAt i).property,hy⟩⟩).val =
        F.first (key (ρ i))-F.last (key i))
    (hFresh : Disjoint H F.colors)

include hY hEnd hReal in
theorem realSegmentLabels_matching (i : Fin n) :
    realSegmentLabels F key ρ Y i = labels (F.path (key i)) ++ closingLabels E S X Y H M endAt i := by
  rw [realSegmentLabels_eq F key ρ Y hY]
  unfold closingLabels
  rw [hEnd]
  split_ifs with hy
  · rfl
  · rw [hReal i hy]
    rw [hEnd]

include hY hEnd hReal hFresh in
theorem realSegmentLabels_nodup (i : Fin n) : (realSegmentLabels F key ρ Y i).Nodup := by
  rw [realSegmentLabels_matching E S X Y H M endAt F key ρ hY hEnd hReal]
  apply (F.rainbow _).append
  · unfold closingLabels
    split_ifs <;> simp
  · apply List.disjoint_left.mpr
    intro c hc hc'
    exact Finset.disjoint_left.mp hFresh (closingLabels_subset E S X Y H M endAt i hc')
      ((F.mem_colors _).mpr ⟨key i,hc⟩)

include hY hEnd hReal hFresh in
theorem realSegmentLabels_disjoint (i j : Fin n) (hij : i ≠ j) :
    List.Disjoint (realSegmentLabels F key ρ Y i) (realSegmentLabels F key ρ Y j) := by
  rw [realSegmentLabels_matching E S X Y H M endAt F key ρ hY hEnd hReal,
    realSegmentLabels_matching E S X Y H M endAt F key ρ hY hEnd hReal]
  apply List.disjoint_left.mpr
  intro c hi hj
  rcases List.mem_append.mp hi with hi | hi
  · rcases List.mem_append.mp hj with hj | hj
    · exact List.disjoint_left.mp (F.color_disjoint _ _ (fun h => hij (key.injective h))) hi hj
    · exact Finset.disjoint_left.mp hFresh (closingLabels_subset E S X Y H M endAt j hj)
        ((F.mem_colors _).mpr ⟨key i,hi⟩)
  · rcases List.mem_append.mp hj with hj | hj
    · exact Finset.disjoint_left.mp hFresh (closingLabels_subset E S X Y H M endAt i hi)
        ((F.mem_colors _).mpr ⟨key j,hj⟩)
    · exact hij (closingLabels_unique E S X Y H M endAt i j hi hj)

include hY hEnd hReal hFresh in
theorem cyclicRealDifferences_nodup (root : Fin n) (hc : ρ.IsCycleOn Set.univ) :
    (CycleCut.cyclicRealDifferences Y (vertices F key ρ root hc) (vertices_nonempty F key ρ root hc)).Nodup := by
  rw [cyclicRealDifferences_eq]
  apply List.nodup_flatMap.mpr
  refine ⟨fun i _ => realSegmentLabels_nodup E S X Y H M endAt F key ρ hY hEnd hReal hFresh i,?_⟩
  apply (trackOrder ρ root hc).nodup.imp
  intro i j hij
  exact realSegmentLabels_disjoint E S X Y H M endAt F key ρ hY hEnd hReal hFresh i j hij

include hY hEnd hReal in
theorem cyclicRealDifferences_inventory (root : Fin n) (hc : ρ.IsCycleOn Set.univ) :
    (CycleCut.cyclicRealDifferences Y (vertices F key ρ root hc) (vertices_nonempty F key ρ root hc)).toFinset =
      F.colors ∪ H := by
  rw [cyclicRealDifferences_eq]
  ext c
  simp only [List.mem_toFinset,List.mem_flatMap,Finset.mem_union,Family.mem_colors]
  constructor
  · rintro ⟨i,_,hi⟩
    rw [realSegmentLabels_matching E S X Y H M endAt F key ρ hY hEnd hReal] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact Or.inl ⟨key i,hi⟩
    · exact Or.inr (closingLabels_subset E S X Y H M endAt i hi)
  · rintro (⟨k,hk⟩ | hH)
    · obtain ⟨i,rfl⟩ := key.surjective k
      refine ⟨i,(trackOrder ρ root hc).covers i,?_⟩
      rw [realSegmentLabels_matching E S X Y H M endAt F key ρ hY hEnd hReal]
      exact List.mem_append_left _ hk
    · obtain ⟨x,hx⟩ := M.color.surjective ⟨c,hH⟩
      let y : E := ⟨x.val,(Finset.mem_sdiff.mp x.property).1⟩
      obtain ⟨i,hi⟩ := endAt.surjective y
      have hy : (endAt i).val ∉ Y := by
        simpa only [hi] using (Finset.mem_sdiff.mp x.property).2
      have he : (⟨(endAt i).val,Finset.mem_sdiff.mpr ⟨(endAt i).property,hy⟩⟩ : ↥(E \ Y)) = x :=
        Subtype.ext (congrArg (fun y : E => y.val) hi)
      refine ⟨i,(trackOrder ρ root hc).covers i,?_⟩
      rw [realSegmentLabels_matching E S X Y H M endAt F key ρ hY hEnd hReal]
      apply List.mem_append_right
      apply (mem_closingLabels E S X Y H M endAt i c).mpr
      exact ⟨hy,by simpa only [he] using congrArg Subtype.val hx⟩

end Matching
end
end EndpointFactor.CycleExpansion
