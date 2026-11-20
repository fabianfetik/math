import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.SourceBite

/-!
# Transporting a finite hypergraph to its actual vertex subtype

The source states its bite for a finite vertex type. An iteration has a
finite subset of the original ambient type. These maps make the comparison
explicit without identifying distinct vertices or edge sets.
-/

open scoped Classical BigOperators
open EndpointMatching.Fractional.Rounding AKSSourceBite

namespace AKSSubsetTransport
noncomputable section
universe u

variable {V : Type u} [Fintype V]

abbrev Vertices (U : Finset V) := {v : V // v ∈ U}

def vertexEmbedding (U : Finset V) : Vertices U ↪ V := ⟨Subtype.val, Subtype.val_injective⟩

def edgeEmbedding (U : Finset V) : Finset (Vertices U) ↪ Finset V :=
  (Finset.mapEmbedding (vertexEmbedding U)).toEmbedding

def restrictEdge (U e : Finset V) : Finset (Vertices U) :=
  Finset.univ.filter (fun x => x.1 ∈ e)

def restrictFamily (U : Finset V) (H : Finset (Finset V)) : Finset (Finset (Vertices U)) :=
  H.image (restrictEdge U)

omit [Fintype V] in
theorem mem_restrictEdge (U e : Finset V) (x : Vertices U) :
    x ∈ restrictEdge U e ↔ x.1 ∈ e := by simp [restrictEdge]

omit [Fintype V] in
/-- An edge contained in U survives restriction to the subtype and mapping
back to the original ambient type without any change. -/
theorem map_restrictEdge (U e : Finset V) (he : e ⊆ U) :
    (restrictEdge U e).map (vertexEmbedding U) = e := by
  ext v
  constructor
  · intro hv
    obtain ⟨x,hx,hxv⟩ := Finset.mem_map.mp hv
    have hx' : x.1 ∈ e := (mem_restrictEdge U e x).1 hx
    simpa [vertexEmbedding] using hxv ▸ hx'
  · intro hv
    have hvU : v ∈ U := he hv
    refine Finset.mem_map.mpr ⟨⟨v,hvU⟩, ?_, rfl⟩
    exact (mem_restrictEdge U e ⟨v,hvU⟩).2 hv

theorem map_restrictFamily (U : Finset V) (H : Finset (Finset V))
    (hinside : ∀ e ∈ H, e ⊆ U) :
    (restrictFamily U H).map (edgeEmbedding U) = H := by
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,hfe⟩ := Finset.mem_map.mp he
    obtain ⟨g,hg,hgf⟩ := Finset.mem_image.mp hf
    subst f
    have hh : edgeEmbedding U (restrictEdge U g) = g := map_restrictEdge U g (hinside g hg)
    rw [← hfe, hh]
    exact hg
  · intro he
    refine Finset.mem_map.mpr ⟨restrictEdge U e, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨e,he,rfl⟩
    · exact map_restrictEdge U e (hinside e he)

theorem restrictFamily_uniform (U : Finset V) (H : Finset (Finset V))
    (hinside : ∀ e ∈ H, e ⊆ U) (huniform : ∀ e ∈ H, e.card = 3) :
    ∀ e ∈ restrictFamily U H, e.card = 3 := by
  intro e he
  have hem : edgeEmbedding U e ∈ H := by
    rw [← map_restrictFamily U H hinside]
    exact Finset.mem_map.mpr ⟨e,he,rfl⟩
  have hh := huniform (edgeEmbedding U e) hem
  simpa [edgeEmbedding] using hh

theorem restrictFamily_linear (U : Finset V) (H : Finset (Finset V))
    (hinside : ∀ e ∈ H, e ⊆ U)
    (hlinear : (H : Set (Finset V)).Pairwise (fun e f => (e ∩ f).card ≤ 1)) :
    ((restrictFamily U H : Finset (Finset (Vertices U))) : Set (Finset (Vertices U))).Pairwise
      (fun e f => (e ∩ f).card ≤ 1) := by
  intro e he f hf hne
  have heH : edgeEmbedding U e ∈ H := by
    rw [← map_restrictFamily U H hinside]
    exact Finset.mem_map.mpr ⟨e,he,rfl⟩
  have hfH : edgeEmbedding U f ∈ H := by
    rw [← map_restrictFamily U H hinside]
    exact Finset.mem_map.mpr ⟨f,hf,rfl⟩
  have hne' : edgeEmbedding U e ≠ edgeEmbedding U f := fun h => hne ((edgeEmbedding U).injective h)
  calc
    (e ∩ f).card = ((e ∩ f).map (vertexEmbedding U)).card := (Finset.card_map _).symm
    _ = ((edgeEmbedding U e) ∩ (edgeEmbedding U f)).card := by
      rw [Finset.map_inter]
      rfl
    _ ≤ 1 := hlinear heH hfH hne'

omit [Fintype V] in
theorem mem_edgeEmbedding (U : Finset V) (e : Finset (Vertices U)) (x : Vertices U) :
    x.1 ∈ edgeEmbedding U e ↔ x ∈ e := by
  exact Finset.mem_map' (vertexEmbedding U)

theorem restrictEdge_map (U : Finset V) (e : Finset (Vertices U)) :
    restrictEdge U (edgeEmbedding U e) = e := by
  ext x
  exact (mem_restrictEdge U (edgeEmbedding U e) x).trans (mem_edgeEmbedding U e x)

theorem restrictFamily_map (U : Finset V) (X : Finset (Finset (Vertices U))) :
    restrictFamily U (X.map (edgeEmbedding U)) = X := by
  ext e
  constructor
  · intro he
    obtain ⟨g,hg,hge⟩ := Finset.mem_image.mp he
    obtain ⟨f,hf,hfg⟩ := Finset.mem_map.mp hg
    subst g
    rw [restrictEdge_map] at hge
    simpa [hge] using hf
  · intro he
    refine Finset.mem_image.mpr ⟨edgeEmbedding U e, ?_, restrictEdge_map U e⟩
    exact Finset.mem_map.mpr ⟨e,he,rfl⟩

theorem mapped_edges_inside (U : Finset V) (X : Finset (Finset (Vertices U))) :
    ∀ e ∈ X.map (edgeEmbedding U), e ⊆ U := by
  intro e he v hv
  obtain ⟨f,hf,rfl⟩ := Finset.mem_map.mp he
  obtain ⟨x,hx,hxv⟩ := Finset.mem_map.mp hv
  simpa [vertexEmbedding] using hxv ▸ x.2

theorem map_univ (U : Finset V) :
    (Finset.univ : Finset (Vertices U)).map (vertexEmbedding U) = U := by
  ext v
  constructor
  · intro hv
    obtain ⟨x,hx,hxv⟩ := Finset.mem_map.mp hv
    simpa [vertexEmbedding] using hxv ▸ x.2
  · intro hv
    exact Finset.mem_map.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩

/-- Isolated selected edges are preserved by the injective vertex map. -/
theorem isolated_map (U : Finset V) (X : Finset (Finset (Vertices U))) :
    isolated (X.map (edgeEmbedding U)) = (isolated X).map (edgeEmbedding U) := by
  classical
  ext e
  constructor
  · intro he
    simp only [isolated,Finset.mem_filter] at he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_map.mp he.1
    refine Finset.mem_map.mpr ⟨f, ?_, rfl⟩
    simp only [isolated,Finset.mem_filter]
    refine ⟨hf,?_⟩
    intro g hg hne
    have hgmap : edgeEmbedding U g ∈ X.map (edgeEmbedding U) :=
      Finset.mem_map.mpr ⟨g,hg,rfl⟩
    have hnemap : edgeEmbedding U g ≠ edgeEmbedding U f :=
      fun h => hne ((edgeEmbedding U).injective h)
    have hdis := he.2 (edgeEmbedding U g) hgmap hnemap
    exact (Finset.disjoint_map (vertexEmbedding U)).mp hdis
  · intro he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_map.mp he
    simp only [isolated,Finset.mem_filter] at hf ⊢
    refine ⟨Finset.mem_map.mpr ⟨f,hf.1,rfl⟩,?_⟩
    intro g hg hne
    obtain ⟨g',hg',rfl⟩ := Finset.mem_map.mp hg
    have hne' : g' ≠ f := by
      intro heq
      exact hne (congrArg (edgeEmbedding U) heq)
    exact (Finset.disjoint_map (vertexEmbedding U)).mpr (hf.2 g' hg' hne')

/-- The union of the mapped edges is exactly the mapped union of vertices. -/
theorem covered_map (U : Finset V) (X : Finset (Finset (Vertices U))) :
    covered (X.map (edgeEmbedding U)) = (covered X).map (vertexEmbedding U) := by
  ext v
  constructor
  · intro hv
    obtain ⟨e,he,hve⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨f,hf,rfl⟩ := Finset.mem_map.mp he
    change v ∈ f.map (vertexEmbedding U) at hve
    obtain ⟨x,hx,hxv⟩ := Finset.mem_map.mp hve
    refine Finset.mem_map.mpr ⟨x,?_,hxv⟩
    simp only [covered,Finset.mem_biUnion]
    exact ⟨f,hf,hx⟩
  · intro hv
    obtain ⟨x,hx,hxv⟩ := Finset.mem_map.mp hv
    simp only [covered,Finset.mem_biUnion] at hx
    obtain ⟨f,hf,hxf⟩ := hx
    refine Finset.mem_biUnion.mpr ⟨edgeEmbedding U f,Finset.mem_map.mpr ⟨f,hf,rfl⟩,?_⟩
    change v ∈ f.map (vertexEmbedding U)
    exact Finset.mem_map.mpr ⟨x,hxf,hxv⟩

/-- Removing the mapped matching and waste gives the mapped remainder. -/
theorem remaining_map (U : Finset V) (M : Finset (Finset (Vertices U)))
    (W : Finset (Vertices U)) :
    remaining U (M.map (edgeEmbedding U)) (W.map (vertexEmbedding U)) =
      (remaining Finset.univ M W).map (vertexEmbedding U) := by
  classical
  ext v
  constructor
  · intro hv
    have hvU := (Finset.mem_sdiff.mp hv).1
    have hvnot := (Finset.mem_sdiff.mp hv).2
    let x : Vertices U := ⟨v,hvU⟩
    refine Finset.mem_map.mpr ⟨x,?_,rfl⟩
    have hnotM : x ∉ covered M := by
      intro hx
      apply hvnot
      apply Finset.mem_union_left
      rw [covered_map]
      exact Finset.mem_map.mpr ⟨x,hx,rfl⟩
    have hnotW : x ∉ W := by
      intro hx
      apply hvnot
      exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨x,hx,rfl⟩)
    simp only [remaining,Finset.mem_sdiff,Finset.mem_union,Finset.mem_univ,true_and,not_or]
    exact ⟨hnotM,hnotW⟩
  · intro hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hv
    have hxnot : x ∉ covered M ∧ x ∉ W := by
      simpa only [remaining,Finset.mem_sdiff,Finset.mem_union,Finset.mem_univ,true_and,not_or] using hx
    apply Finset.mem_sdiff.mpr
    refine ⟨x.2,?_⟩
    intro hbad
    rcases Finset.mem_union.mp hbad with hM | hW
    · rw [covered_map] at hM
      exact hxnot.1 ((Finset.mem_map' (vertexEmbedding U)).1 hM)
    · exact hxnot.2 ((Finset.mem_map' (vertexEmbedding U)).1 hW)

/-- Inducing a subtype graph and mapping back commute on actual edge sets. -/
theorem induced_map (U : Finset V) (H : Finset (Finset (Vertices U)))
    (R : Finset (Vertices U)) :
    (induced H R).map (edgeEmbedding U) =
      induced (H.map (edgeEmbedding U)) (R.map (vertexEmbedding U)) := by
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_map.mp he
    simp only [induced,Finset.mem_filter] at hf
    have hfH := hf.1
    have hfR := hf.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_map.mpr ⟨f,hfH,rfl⟩,?_⟩
    exact Finset.map_subset_map.mpr hfR
  · intro he
    have heH := (Finset.mem_filter.mp he).1
    have heR := (Finset.mem_filter.mp he).2
    obtain ⟨f,hf,rfl⟩ := Finset.mem_map.mp heH
    refine Finset.mem_map.mpr ⟨f,?_,rfl⟩
    simp only [induced,Finset.mem_filter]
    exact ⟨hf, Finset.map_subset_map.mp heR⟩

/-- Every actual vertex has the same degree after restricting the ambient
graph to the subtype of its active vertex set. -/
theorem degreeAt_restrictFamily (U : Finset V) (H : Finset (Finset V))
    (hinside : ∀ e ∈ H, e ⊆ U) (x : Vertices U) :
    degreeAt (restrictFamily U H) x = degreeAt H x.1 := by
  classical
  unfold degreeAt
  apply Finset.card_bij (fun e _ => edgeEmbedding U e)
  · intro e he
    simp only [Finset.mem_filter] at he
    have hef := he.1
    have hxe := he.2
    have heH : edgeEmbedding U e ∈ H := by
      rw [← map_restrictFamily U H hinside]
      exact Finset.mem_map.mpr ⟨e,hef,rfl⟩
    exact Finset.mem_filter.mpr ⟨heH,(mem_edgeEmbedding U e x).2 hxe⟩
  · intro e he f hf hef
    exact (edgeEmbedding U).injective hef
  · intro e he
    have heH := (Finset.mem_filter.mp he).1
    have hxe := (Finset.mem_filter.mp he).2
    refine ⟨restrictEdge U e, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      exact ⟨Finset.mem_image.mpr ⟨e,heH,rfl⟩,
        (mem_restrictEdge U e x).2 hxe⟩
    · exact map_restrictEdge U e (hinside e heH)

omit [Fintype V] in
theorem subtype_card (U : Finset V) : Fintype.card (Vertices U) = U.card := Fintype.card_coe U

/-- Mapping a subtype edge family back to the ambient type preserves the
degree of each vertex of the subtype. -/
theorem degreeAt_mapFamily (U : Finset V) (X : Finset (Finset (Vertices U)))
    (x : Vertices U) :
    degreeAt X x = degreeAt (X.map (edgeEmbedding U)) x.1 := by
  have h := degreeAt_restrictFamily U (X.map (edgeEmbedding U)) (mapped_edges_inside U X) x
  simpa [restrictFamily_map U X] using h

/-- Restriction preserves the exact 3-uniformity, pair-codegree and degree
window hypotheses on every remaining vertex. -/
theorem window_on_vertex_subtype (U : Finset V) (H : Finset (Finset V))
    (D K : ℝ) (hwindow : Window U H D K) :
    Window (Finset.univ : Finset (Vertices U)) (restrictFamily U H) D K := by
  have hinside : ∀ e ∈ H, e ⊆ U := fun e he => (hwindow.1 e he).1
  have huniform : ∀ e ∈ H, e.card = 3 := fun e he => (hwindow.1 e he).2
  refine ⟨?_,?_,?_⟩
  · intro e he
    exact ⟨Finset.subset_univ e, restrictFamily_uniform U H hinside huniform e he⟩
  · intro e he f hf hne
    have hlin := restrictFamily_linear U H hinside hwindow.2.1 he hf hne
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact Finset.card_le_one.mp hlin x (by simpa only [Finset.mem_inter] using hx)
      y (by simpa only [Finset.mem_inter] using hy)
  · intro x hx
    have h := hwindow.2.2 x.1 x.2
    simpa [degreeAt_restrictFamily U H hinside x] using h

/-- Transport an entire source witness from the active vertex subtype back
to the original ambient type. Selected edges, waste, remainder, degree
window and both numerical relations are preserved. -/
theorem witness_from_vertex_subtype (U : Finset V) (H : Finset (Finset V))
    (D K Dmin C Cw : ℝ) (hinside : ∀ e ∈ H, e ⊆ U)
    (b : Witness (Finset.univ : Finset (Vertices U)) (restrictFamily U H) D K Dmin C Cw) :
    Nonempty (Witness U H D K Dmin C Cw) := by
  have hIso : isolated (b.selected.map (edgeEmbedding U)) =
      (isolated b.selected).map (edgeEmbedding U) := isolated_map U b.selected
  have hRest : remaining U (isolated (b.selected.map (edgeEmbedding U)))
        (b.waste.map (vertexEmbedding U)) =
      (remaining Finset.univ (isolated b.selected) b.waste).map (vertexEmbedding U) := by
    rw [hIso]
    exact remaining_map U (isolated b.selected) b.waste
  have hRestCard :
      (remaining U (isolated (b.selected.map (edgeEmbedding U))) (b.waste.map (vertexEmbedding U))).card =
        (remaining Finset.univ (isolated b.selected) b.waste).card := by
    rw [hRest,Finset.card_map]
  have hFamily : (restrictFamily U H).map (edgeEmbedding U) = H := map_restrictFamily U H hinside
  have hGraph :
      induced H (remaining U (isolated (b.selected.map (edgeEmbedding U))) (b.waste.map (vertexEmbedding U))) =
        (induced (restrictFamily U H) (remaining Finset.univ (isolated b.selected) b.waste)).map
          (edgeEmbedding U) := by
    rw [hRest]
    calc
      induced H ((remaining Finset.univ (isolated b.selected) b.waste).map (vertexEmbedding U)) =
          induced ((restrictFamily U H).map (edgeEmbedding U))
            ((remaining Finset.univ (isolated b.selected) b.waste).map (vertexEmbedding U)) :=
        congrArg (fun family => induced family
          ((remaining Finset.univ (isolated b.selected) b.waste).map (vertexEmbedding U))) hFamily.symm
      _ = _ := (induced_map U (restrictFamily U H)
        (remaining Finset.univ (isolated b.selected) b.waste)).symm
  refine ⟨{
    selected := b.selected.map (edgeEmbedding U)
    waste := b.waste.map (vertexEmbedding U)
    nextDegree := b.nextDegree
    vertexError := b.vertexError
    degreeError := b.degreeError
    selected_subset := ?_
    waste_subset := ?_
    waste_bound := ?_
    vertex_error_bound := b.vertex_error_bound
    degree_error_bound := b.degree_error_bound
    vertex_bound := ?_
    degree_relation := ?_
    next_window := ?_ }⟩
  · calc
      b.selected.map (edgeEmbedding U) ⊆ (restrictFamily U H).map (edgeEmbedding U) :=
        Finset.map_subset_map.mpr b.selected_subset
      _ = H := hFamily
  · calc
      b.waste.map (vertexEmbedding U) ⊆ (Finset.univ : Finset (Vertices U)).map (vertexEmbedding U) :=
        Finset.map_subset_map.mpr (Finset.subset_univ _)
      _ = U := map_univ U
  · simpa only [Finset.card_map,Finset.card_univ,subtype_card] using b.waste_bound
  · simpa only [hRestCard,Finset.card_univ,subtype_card] using b.vertex_bound
  · simpa only [hRestCard,Finset.card_univ,subtype_card] using b.degree_relation
  · intro hmin hone v hv
    rw [hRest] at hv
    obtain ⟨x,hx,hxv⟩ := Finset.mem_map.mp hv
    have hwin := b.next_window hmin hone x hx
    have hdeg :
        degreeAt (induced H (remaining U (isolated (b.selected.map (edgeEmbedding U)))
          (b.waste.map (vertexEmbedding U)))) v =
        degreeAt (induced (restrictFamily U H) (remaining Finset.univ (isolated b.selected) b.waste)) x := by
      rw [hGraph, ← hxv]
      exact (degreeAt_mapFamily U _ x).symm
    simpa only [hdeg] using hwin

/-- The full-vertex source formulation quantifies over every finite vertex
type. Its statement remains an explicit external theorem assumption. -/
def NativeBiteTheorem (K Dmin C Cw : ℝ) : Prop :=
  ∀ (V : Type u) [Fintype V] (H : Finset (Finset V)) (D : ℝ),
    (Finset.univ : Finset V).Nonempty → Dmin ≤ D → Real.exp 1 ≤ D →
    Window (Finset.univ : Finset V) H D K →
    Nonempty (Witness (Finset.univ : Finset V) H D K Dmin C Cw)

/-- A native source bite on each finite vertex type supplies the ambient
subset formulation needed for iteration, without adding graph hypotheses. -/
theorem source_bite_from_native (K Dmin C Cw : ℝ)
    (hsource : NativeBiteTheorem.{u} K Dmin C Cw) :
    SourceBiteTheorem.{u} K Dmin C Cw := by
  intro V _ U H D hU hmin hexp hwindow
  have hinside : ∀ e ∈ H, e ⊆ U := fun e he => (hwindow.1 e he).1
  have hU' : (Finset.univ : Finset (Vertices U)).Nonempty := by
    obtain ⟨v,hv⟩ := hU
    exact ⟨⟨v,hv⟩,Finset.mem_univ _⟩
  have hwindow' := window_on_vertex_subtype U H D K hwindow
  obtain ⟨b⟩ := hsource (Vertices U) (restrictFamily U H) D hU' hmin hexp hwindow'
  exact witness_from_vertex_subtype U H D K Dmin C Cw hinside b

end
end AKSSubsetTransport
