import CorralFormalization.EndpointProof.Selector.TwoPairSwitch

/-!
Finite, actual zero-sum matchings, tag permutations, and exact disjoint union.
The tags are permuted without changing any numerical coordinate.
-/

open scoped Classical BigOperators

namespace EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [DecidableEq G]

/-- A finite family of genuine, disjoint hyperedges with exact cover. -/
structure MatchingOn (S : Finset (Vertex G)) where
  edges : Finset (Finset (Vertex G))
  valid : ∀ E ∈ edges, IsHyperedge E
  disjoint : (edges : Set (Finset (Vertex G))).Pairwise Disjoint
  cover : edges.biUnion id = S

theorem MatchingOn.edge_subset {S : Finset (Vertex G)} (M : MatchingOn S)
    {E : Finset (Vertex G)} (hE : E ∈ M.edges) : E ⊆ S := by
  intro v hv
  rw [← M.cover]
  exact Finset.mem_biUnion.mpr ⟨E,hE,hv⟩

def MatchingOn.empty : MatchingOn (∅ : Finset (Vertex G)) where
  edges := ∅
  valid := by simp
  disjoint := by simp
  cover := by simp

def MatchingOn.two {E : Fin 2 → Finset (Vertex G)} {S : Finset (Vertex G)}
    (h : IsTwoEdgeMatchingOn E S) : MatchingOn S where
  edges := {E 0,E 1}
  valid := by intro e he; simp only [Finset.mem_insert,Finset.mem_singleton] at he
              rcases he with rfl | rfl <;> exact h.1 _
  disjoint := by
    intro e he f hf hef
    change e ∈ ({E 0,E 1} : Finset _) at he
    change f ∈ ({E 0,E 1} : Finset _) at hf
    simp only [Finset.mem_insert,Finset.mem_singleton] at he hf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · exact False.elim (hef rfl)
    · exact h.2.1
    · exact h.2.1.symm
    · exact False.elim (hef rfl)
  cover := by simpa using h.2.2

def MatchingOn.union {S T : Finset (Vertex G)} (M : MatchingOn S)
    (N : MatchingOn T) (hST : Disjoint S T) : MatchingOn (S ∪ T) where
  edges := M.edges ∪ N.edges
  valid := by
    intro E hE
    rcases Finset.mem_union.mp hE with hE | hE
    · exact M.valid E hE
    · exact N.valid E hE
  disjoint := by
    intro E hE F hF hEF
    rcases Finset.mem_union.mp hE with hE | hE <;>
      rcases Finset.mem_union.mp hF with hF | hF
    · exact M.disjoint hE hF hEF
    · exact hST.mono (M.edge_subset hE) (N.edge_subset hF)
    · exact hST.symm.mono (N.edge_subset hE) (M.edge_subset hF)
    · exact N.disjoint hE hF hEF
  cover := by rw [Finset.union_biUnion, M.cover,N.cover]

/-- The complete permutation group of the three parts is legal for zero-sum
edges. Reservoir labels must be permuted separately in the sampling event. -/
def tagEquiv (σ : Equiv.Perm (Fin 3)) : Vertex G ≃ Vertex G :=
  Equiv.prodCongr σ (Equiv.refl G)

def rotate (σ : Equiv.Perm (Fin 3)) (S : Finset (Vertex G)) : Finset (Vertex G) :=
  S.image (tagEquiv σ)

@[simp] theorem rotate_union (σ : Equiv.Perm (Fin 3)) (S T : Finset (Vertex G)) :
    rotate σ (S ∪ T) = rotate σ S ∪ rotate σ T := by
  exact Finset.image_union _ _

@[simp] theorem rotate_card (σ : Equiv.Perm (Fin 3)) (S : Finset (Vertex G)) :
    (rotate σ S).card = S.card :=
  Finset.card_image_of_injective S (tagEquiv σ).injective

theorem rotate_disjoint (σ : Equiv.Perm (Fin 3)) {S T : Finset (Vertex G)}
    (h : Disjoint S T) : Disjoint (rotate σ S) (rotate σ T) := by
  exact (Finset.disjoint_image (tagEquiv σ).injective).2 h

theorem edge_eq_image (x y z : G) :
    edge x y z = Finset.univ.image (fun i : Fin 3 ↦ (i, ![x,y,z] i)) := by
  ext v
  simp [edge,Fin.exists_fin_succ,eq_comm]

theorem rotate_edge (σ : Equiv.Perm (Fin 3)) (x y z : G) :
    rotate σ (edge x y z) =
      edge (![x,y,z] (σ.symm 0)) (![x,y,z] (σ.symm 1)) (![x,y,z] (σ.symm 2)) := by
  rw [edge_eq_image,edge_eq_image]
  simp only [rotate,Finset.image_image]
  have hf : ![![x,y,z] (σ.symm 0),![x,y,z] (σ.symm 1),![x,y,z] (σ.symm 2)] =
      (fun j ↦ ![x,y,z] (σ.symm j)) := by
    funext j
    fin_cases j <;> rfl
  rw [hf]
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨σ i,?_⟩
    simp [tagEquiv]
  · rintro ⟨i,rfl⟩
    refine ⟨σ.symm i,?_⟩
    simp [tagEquiv]

theorem hyperedge_rotate (σ : Equiv.Perm (Fin 3)) {E : Finset (Vertex G)}
    (hE : IsHyperedge E) : IsHyperedge (rotate σ E) := by
  obtain ⟨x,y,z,h,rfl⟩ := hE
  refine ⟨![x,y,z] (σ.symm 0),![x,y,z] (σ.symm 1),![x,y,z] (σ.symm 2),?_,rotate_edge σ x y z⟩
  have hs := Equiv.sum_comp σ.symm (fun i : Fin 3 ↦ ![x,y,z] i)
  simp [Fin.sum_univ_succ] at hs
  have hs₂ : ![x,y,z] (σ.symm 0) + ![x,y,z] (σ.symm 1) +
      ![x,y,z] (σ.symm 2) = x+y+z := by simpa only [add_assoc] using hs
  exact hs₂.trans h

def MatchingOn.rotated {S : Finset (Vertex G)} (M : MatchingOn S)
    (σ : Equiv.Perm (Fin 3)) : MatchingOn (rotate σ S) where
  edges := M.edges.image (rotate σ)
  valid := by
    intro E hE
    obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hE
    exact hyperedge_rotate σ (M.valid F hF)
  disjoint := by
    intro E hE F hF hEF
    change E ∈ M.edges.image (rotate σ) at hE
    change F ∈ M.edges.image (rotate σ) at hF
    obtain ⟨E₀,hE₀,rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨F₀,hF₀,rfl⟩ := Finset.mem_image.mp hF
    exact rotate_disjoint σ (M.disjoint hE₀ hF₀ (fun he ↦ hEF (congrArg _ he)))
  cover := by
    ext v
    constructor
    · intro hv
      obtain ⟨D,hD,hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hD
      change v ∈ E.image (tagEquiv σ) at hv
      obtain ⟨x,hx,hv⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨x,M.edge_subset hE hx,hv⟩
    · intro hv
      obtain ⟨x,hx,hv⟩ := Finset.mem_image.mp hv
      rw [← M.cover] at hx
      obtain ⟨E,hE,hx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_biUnion.mpr ⟨rotate σ E,Finset.mem_image.mpr ⟨E,hE,rfl⟩,
        Finset.mem_image.mpr ⟨x,hx,hv⟩⟩

/-- The inverse closure charged by the forbidden-support estimate, including signs not occupied as vertices. -/
def numericalSupport (S : Finset (Vertex G)) : Finset G :=
  S.image Prod.snd ∪ S.image (fun v ↦ -v.2)

theorem coordinate_mem_numericalSupport {S : Finset (Vertex G)} {v : Vertex G}
    (hv : v ∈ S) : v.2 ∈ numericalSupport S :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)

theorem numericalSupport_mono {S T : Finset (Vertex G)} (h : S ⊆ T) :
    numericalSupport S ⊆ numericalSupport T := by
  exact Finset.union_subset_union (Finset.image_subset_image h) (Finset.image_subset_image h)

@[simp] theorem numericalSupport_union (S T : Finset (Vertex G)) :
    numericalSupport (S ∪ T) = numericalSupport S ∪ numericalSupport T := by
  simp only [numericalSupport,Finset.image_union]
  ac_rfl

theorem disjoint_of_numericalSupport {S T : Finset (Vertex G)}
    (h : Disjoint (numericalSupport S) (numericalSupport T)) : Disjoint S T := by
  exact Finset.disjoint_left.mpr (fun _ hs ht ↦ Finset.disjoint_left.mp h
    (coordinate_mem_numericalSupport hs) (coordinate_mem_numericalSupport ht))

theorem numericalSupport_card_le (S : Finset (Vertex G)) :
    (numericalSupport S).card ≤ 2*S.card := by
  exact (Finset.card_union_le _ _).trans (by
    have h₁ := Finset.card_image_le (s := S) (f := Prod.snd)
    have h₂ := Finset.card_image_le (s := S) (f := fun v : Vertex G ↦ -v.2)
    omega)

@[simp] theorem numericalSupport_rotate (σ : Equiv.Perm (Fin 3))
    (S : Finset (Vertex G)) : numericalSupport (rotate σ S) = numericalSupport S := by
  simp [numericalSupport,rotate,Finset.image_image,tagEquiv,Function.comp_def]

theorem support_bound_3996 (I T : Finset (Vertex G))
    (hI : I.card ≤ 1798) (hT : T.card ≤ 200) :
    (numericalSupport (I ∪ T)).card ≤ 3996 := by
  have hu := Finset.card_union_le I T
  have hs := numericalSupport_card_le (I ∪ T)
  omega

end
end EndpointSelector.Assembly
