import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Counts

/-! # Exact directed-edge coverage by the constructed ordinary paths -/

open scoped Classical BigOperators
namespace EndpointFactor.OrdinaryFragments
open EndpointMatching.AbsorptionAssembly FragmentChecksum
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

abbrev directedEdges (p : List G) : List (G × G) := edgeLabels (fun a b : G => (a,b)) p

def matchingEdges {X Y C : Finset G} (M : PhysicalDifferenceMatching X Y C) : Finset (G × G) :=
  Finset.univ.image (fun x : X => (x.val, (M.endpoint x).val))

@[simp] theorem mem_matchingEdges {X Y C : Finset G} (M : PhysicalDifferenceMatching X Y C)
    (e : G × G) : e ∈ matchingEdges M ↔ ∃ x : X, (x.val, (M.endpoint x).val) = e := by
  simp [matchingEdges]

private theorem directedEdges_append_one (p : List G) (hp : p ≠ []) (y : G) :
    directedEdges (p ++ [y]) = directedEdges p ++ [(lastOrZero p,y)] := by
  have he := List.dropLast_append_getLast hp
  calc
    directedEdges (p ++ [y]) = directedEdges (p.dropLast ++ p.getLast hp :: [y]) := by
      simpa [List.append_assoc] using congrArg (fun z : List G => directedEdges (z ++ [y])) he.symm
    _ = directedEdges (p.dropLast ++ [p.getLast hp]) ++ [(p.getLast hp,y)] := by
      rw [directedEdges, edgeLabels_append_pivot]
      rfl
    _ = directedEdges p ++ [(lastOrZero p,y)] := by
      rw [he]
      simp [lastOrZero, List.getLast?_eq_some_getLast hp]

theorem mem_directedEdges_stepPath {X Y C : Finset G} (M : PhysicalDifferenceMatching X Y C)
    (p : List G) (hp : p ≠ []) (e : G × G) :
    e ∈ directedEdges (stepPath M p) ↔ e ∈ directedEdges p ∨
      ∃ x : X, x.val = lastOrZero p ∧ (x.val, (M.endpoint x).val) = e := by
  unfold stepPath
  split_ifs with hx
  · rw [directedEdges_append_one p hp]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨⟨lastOrZero p,hx⟩, rfl, h.symm⟩
    · rintro (h | ⟨x,hx',h⟩)
      · exact Or.inl h
      · right
        have he : x = ⟨lastOrZero p,hx⟩ := Subtype.ext hx'
        simpa only [he] using h.symm
  · constructor
    · exact Or.inl
    · rintro (h | ⟨x,hx',_⟩)
      · exact h
      · exact False.elim (hx (hx' ▸ x.property))

namespace Family
variable (F : Family G)

def edges : Finset (G × G) := Finset.univ.biUnion (fun i => (directedEdges (F.path i)).toFinset)

@[simp] theorem mem_edges (e : G × G) : e ∈ F.edges ↔ ∃ i, e ∈ directedEdges (F.path i) := by
  simp [edges]
@[simp] theorem lists_edges : (F.lists.flatMap directedEdges).toFinset = F.edges := by
  ext e
  simp [lists, edges]

@[simp] theorem extend_edges {X Y C : Finset G} (M : PhysicalDifferenceMatching X Y C)
    (N : Finset G) (hX : X ⊆ F.ends) (hYN : Y ⊆ N)
    (hNV : Disjoint N F.vertices) (hCF : Disjoint C F.colors) :
    (F.extend M N hX hYN hNV hCF).edges = F.edges ∪ matchingEdges M := by
  ext e
  rw [mem_edges, Finset.mem_union, F.mem_edges, mem_matchingEdges]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | inl i =>
      rcases (mem_directedEdges_stepPath M _ (F.nonempty i) _).mp hi with hi | ⟨x,hx,he⟩
      · exact Or.inl ⟨i,hi⟩
      · exact Or.inr ⟨x,he⟩
    | inr x => simp [extend, directedEdges, edgeLabels] at hi
  · rintro (⟨i,hi⟩ | ⟨x,hx⟩)
    · exact ⟨Sum.inl i, (mem_directedEdges_stepPath M _ (F.nonempty i) _).mpr (Or.inl hi)⟩
    · obtain ⟨i,hi⟩ := (F.mem_ends x.val).mp (hX x.property)
      exact ⟨Sum.inl i, (mem_directedEdges_stepPath M _ (F.nonempty i) _).mpr
        (Or.inr ⟨x,hi.symm,hx⟩)⟩

@[simp] theorem addIsolates_edges (L : Finset G) (hfresh : Disjoint L F.vertices) :
    (F.addIsolates L hfresh).edges = F.edges := by
  rw [addIsolates, extend_edges]
  have he : matchingEdges (emptyMatching (G := G)) = ∅ := by
    ext e
    simp [matchingEdges]
  rw [he, Finset.union_empty]

end Family

@[simp] theorem singletons_edges (S : Finset G) : (singletons S).edges = ∅ := by
  ext e
  simp [Family.edges, singletons, directedEdges, edgeLabels]

namespace LayerData
variable {j ℓ : ℕ} (D : LayerData G j ℓ)

def edges : Finset (G × G) := Finset.univ.biUnion (fun i => matchingEdges (D.matching i))

/-- Every actual ordinary matching edge occurs, and no additional edge is
introduced. This stronger version makes the literal decomposition explicit. -/
theorem exists_family_with_edges (D : LayerData G j ℓ) :
    ∃ F : Family G, F.vertices = D.vertices ∧ F.colors = D.colors ∧ F.edges = D.edges ∧
      D.layer 0 ⊆ F.starts ∧ D.layer (Fin.last j) ⊆ F.ends ∧
      Fintype.card F.Index = ℓ+D.deficit := by
  induction j with
  | zero =>
    refine ⟨singletons (D.layer 0), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [vertices]
    · simp [colors]
    · simp [edges]
    · simp
    · simp
    · simp [deficit, D.size]
  | succ j ih =>
    obtain ⟨F,hV,hC,hEdges,hS,hE,hcard⟩ := ih D.initial
    let M := D.matching (Fin.last j)
    let N := D.layer (Fin.last (j+1))
    have hX : D.tail (Fin.last j) ⊆ F.ends := (D.tail_subset (Fin.last j)).trans hE
    have hYN : D.head (Fin.last j) ⊆ N := D.head_subset (Fin.last j)
    have hNV : Disjoint N F.vertices := by rw [hV]; exact D.last_layer_fresh
    have hCF : Disjoint (D.color (Fin.last j)) F.colors := by rw [hC]; exact D.last_color_fresh
    let F' := F.extend M N hX hYN hNV hCF
    refine ⟨F', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Family.extend_vertices, hV, ← D.vertices_initial]
    · rw [Family.extend_colors, hC, ← D.colors_initial]
    · rw [Family.extend_edges, hEdges]
      change D.initial.edges ∪ matchingEdges (D.matching (Fin.last j)) = D.edges
      ext e
      simp only [edges, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨i,hi⟩ | hi)
        · exact ⟨i.castSucc,hi⟩
        · exact ⟨Fin.last j,hi⟩
      · rintro ⟨i,hi⟩
        by_cases hlt : i.val < j
        · let k : Fin j := ⟨i.val,hlt⟩
          have he : k.castSucc = i := Fin.ext rfl
          apply Or.inl
          refine ⟨k, ?_⟩
          change e ∈ matchingEdges (D.matching k.castSucc)
          rw [he]
          exact hi
        · have he : i = Fin.last j := Fin.ext (by simp; omega)
          exact Or.inr (he ▸ hi)
    · rw [Family.extend_starts]
      exact hS.trans Finset.subset_union_left
    · rw [Family.extend_ends]
      exact Finset.subset_union_right
    · have hcount := F.extend_count M N hX hYN hNV hCF
      have ht := D.tail_card_le (Fin.last j)
      have hc := D.matching_card (Fin.last j)
      have hn : N.card = ℓ := D.size _
      change Fintype.card (F.extend M N hX hYN hNV hCF).Index = ℓ+D.deficit
      rw [D.deficit_initial]
      rw [hcard,hn,hc] at hcount
      omega

/-- Literal matching-edge coverage survives adding every remainder singleton. -/
theorem exists_with_leftovers_with_edges (L : Finset G) (hL : Disjoint L D.vertices) :
    ∃ F₀ F : Family G,
      F₀.vertices = D.vertices ∧ F₀.colors = D.colors ∧
      D.layer 0 ⊆ F₀.starts ∧ D.layer (Fin.last j) ⊆ F₀.ends ∧
      Fintype.card F₀.Index = ℓ+D.deficit ∧
      F.vertices = D.vertices ∪ L ∧ F.colors = D.colors ∧ F.edges = D.edges ∧
      D.layer 0 ⊆ F.starts ∧ D.layer (Fin.last j) ⊆ F.ends ∧
      Fintype.card F.Index = ℓ+D.deficit+L.card ∧
      (F.primary (D.layer 0)).card = ℓ ∧
      F.primaryEnds (D.layer 0) = F₀.primaryEnds (D.layer 0) ∧
      (D.layer (Fin.last j) \ F.goodPrimaryEnds (D.layer 0) (D.layer (Fin.last j))).card ≤ D.deficit := by
  obtain ⟨F₀,hV,hC,hEdges,hS,hE,hcount⟩ := D.exists_family_with_edges
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
    exact (D.mem_vertices _).mpr ⟨0,hg⟩
  have hp : F.primaryEnds (D.layer 0) = F₀.primaryEnds (D.layer 0) :=
    F₀.addIsolates_primaryEnds L (D.layer 0) hLf hB
  refine ⟨F₀,F,hV,hC,hS,hE,hcount,?_,?_,?_,hS',hE',?_,?_,hp,?_⟩
  · rw [Family.addIsolates_vertices,hV]
  · rw [Family.addIsolates_colors,hC]
  · rw [Family.addIsolates_edges,hEdges]
  · rw [Family.addIsolates_count,hcount]
  · rw [F.primary_card _ hS',D.size]
  · rw [Family.goodPrimaryEnds,hp]
    exact F₀.goodPrimaryEnds_large _ _ hS hE ℓ D.deficit (D.size _) (D.size _) hcount

end LayerData
end
end EndpointFactor.OrdinaryFragments
