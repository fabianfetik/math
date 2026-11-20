import CorralFormalization.EndpointProof.Router.GlobalGeometry.Support

namespace EndpointRouter
open EndpointFactor
open scoped Classical
noncomputable section
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {G : Type v} [AddCommGroup G]

namespace LayerGeometry
variable {L : MatchingLayer α} {input output : α → G}
variable (D : LayerGeometry L input output)

private theorem path_field_support (field : Segment G → List G)
    (hS : ∀ S : Switch G, ∀ cross track z, z ∈ field (S.path cross track) →
      z ∈ S.interior ∨ z ∈ S.colors)
    (hI : ∀ I : Idle G, ∀ z, z ∈ field I.path → z ∈ I.interior ∨ z ∈ I.colors)
    (chosen : List (α × α)) (i : α) {z : G} (hz : z ∈ field (D.path chosen i)) :
    z ∈ D.unitSupport (L.unitOf i) := by
  by_cases hi : L.Isolated i
  · rw [MatchingLayer.unitOf, dif_pos hi, unitSupport]
    rw [D.path_isolated chosen i hi] at hz
    simpa only [List.mem_toFinset, List.mem_append] using hI (D.idle i) z hz
  · rw [MatchingLayer.unitOf, dif_neg hi, unitSupport]
    simp only [LayerGeometry.path, dif_neg hi] at hz
    simpa only [List.mem_toFinset, List.mem_append] using
      hS (D.exchange (L.incidentEdge i hi)) _ _ z hz

theorem path_interior_support (chosen : List (α × α)) (i : α)
    {z : G} (hz : z ∈ (D.path chosen i).interior) :
    z ∈ D.unitSupport (L.unitOf i) := by
  apply D.path_field_support Segment.interior ?_ ?_ chosen i hz
  · intro S cross track z hz
    left
    apply (S.interior_inventory cross z).mp
    cases track
    · exact Or.inl hz
    · exact Or.inr hz
  · intro I z hz
    exact Or.inl hz

theorem path_color_support (chosen : List (α × α)) (i : α)
    {z : G} (hz : z ∈ (D.path chosen i).colors (fun a b : G => b-a)) :
    z ∈ D.unitSupport (L.unitOf i) := by
  apply D.path_field_support (fun P => P.colors (fun a b : G => b-a)) ?_ ?_ chosen i hz
  · intro S cross track z hz
    right
    apply (S.color_inventory cross z).mp
    cases track
    · exact Or.inl hz
    · exact Or.inr hz
  · intro I z hz
    exact Or.inr hz

private theorem same_unit_disjoint (field : Segment G → List G)
    (hS : ∀ e ∈ L.edges, ∀ cross,
      List.Disjoint (field ((D.exchange e).path cross false))
        (field ((D.exchange e).path cross true)))
    (chosen : List (α × α)) (i j : α) (hij : i ≠ j)
    (hu : L.unitOf i = L.unitOf j) :
    List.Disjoint (field (D.path chosen i)) (field (D.path chosen j)) := by
  by_cases hi : L.Isolated i
  · by_cases hj : L.Isolated j
    · have he : i = j := by
        simpa only [MatchingLayer.unitOf, dif_pos hi, dif_pos hj,
          Sum.inr.injEq, Subtype.mk.injEq] using hu
      exact (hij he).elim
    · simp only [MatchingLayer.unitOf, dif_pos hi, dif_neg hj] at hu
      cases hu
  · by_cases hj : L.Isolated j
    · simp only [MatchingLayer.unitOf, dif_neg hi, dif_pos hj] at hu
      cases hu
    · have heq : L.incidentEdge i hi = L.incidentEdge j hj := by
        simpa only [MatchingLayer.unitOf, dif_neg hi, dif_neg hj,
          Sum.inl.injEq, Subtype.mk.injEq] using hu
      let e := L.incidentEdge i hi
      have he : e ∈ L.edges := L.incidentEdge_mem i hi
      have hie : L.Incident i e := L.incidentEdge_incident i hi
      have hje : L.Incident j e := by
        rw [show e = L.incidentEdge j hj from heq]
        exact L.incidentEdge_incident j hj
      rcases hie with hi' | hi' <;> rcases hje with hj' | hj'
      · exact (hij (hi'.trans hj'.symm)).elim
      · rw [hi', hj', D.path_left chosen e he, D.path_right chosen e he]
        exact hS e he _
      · rw [hi', hj', D.path_right chosen e he, D.path_left chosen e he]
        exact (hS e he _).symm
      · exact (hij (hi'.trans hj'.symm)).elim

/-- Local switch validity handles two tracks in one unit; the raw numerical
certificate handles tracks in different units. -/
theorem interiors_pairwise
    (hdisj : Pairwise (fun u v : L.Unit => Disjoint (D.unitSupport u) (D.unitSupport v)))
    (chosen : List (α × α)) :
    Pairwise (fun i j => List.Disjoint (D.path chosen i).interior (D.path chosen j).interior) := by
  intro i j hij
  by_cases hu : L.unitOf i = L.unitOf j
  · apply D.same_unit_disjoint Segment.interior ?_ chosen i j hij hu
    intro e he cross
    have hn := ((D.exchange e).interior_perm cross).nodup_iff.mpr
      (D.exchange_valid e he).1.of_append_right
    exact hn.disjoint
  · exact List.disjoint_left.mpr fun z hzi hzj =>
      Finset.disjoint_left.mp (hdisj hu) (D.path_interior_support chosen i hzi)
        (D.path_interior_support chosen j hzj)

theorem colors_pairwise
    (hdisj : Pairwise (fun u v : L.Unit => Disjoint (D.unitSupport u) (D.unitSupport v)))
    (chosen : List (α × α)) :
    Pairwise (fun i j => List.Disjoint
      ((D.path chosen i).colors (fun a b : G => b-a))
      ((D.path chosen j).colors (fun a b : G => b-a))) := by
  intro i j hij
  by_cases hu : L.unitOf i = L.unitOf j
  · apply D.same_unit_disjoint (fun P => P.colors (fun a b : G => b-a)) ?_ chosen i j hij hu
    intro e he cross
    exact ((D.exchange e).setting_valid (D.exchange_valid e he) cross).2.1.disjoint
  · exact List.disjoint_left.mpr fun z hzi hzj =>
      Finset.disjoint_left.mp (hdisj hu) (D.path_color_support chosen i hzi)
        (D.path_color_support chosen j hzj)

theorem path_colors_nonzero (chosen : List (α × α)) (i : α) :
    ∀ z ∈ (D.path chosen i).colors (fun a b : G => b-a), z ≠ 0 :=
  difference_labels_nonzero _ (D.path_valid chosen i).2.1

end LayerGeometry
end
end EndpointRouter
