import CorralFormalization.EndpointProof.Flow.Matchings

/-! Exact paired and part inventories of the regular augmentation and outputs. -/

open scoped BigOperators

namespace EndpointFlow

set_option maxHeartbeats 1500000
set_option maxRecDepth 2048

section

variable {G : Type*} [CommRing G] [Fintype G] [DecidableEq G]

def partCard (S : Finset (Vertex G)) (p : Part) : ℕ := (S.filter (fun v ↦ v.1=p)).card

theorem augmentation_partCard (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G) (hv : Valid L r xy) (p : Part) :
    partCard (augmentation L r xy) p = 6 := by
  have he : (augmentation L r xy).filter (fun v ↦ v.1=p) =
      (Finset.univ.filter (fun jb : Fin 9 × Bool ↦ part L jb.1=p)).image (newVertex L r xy) := by
    ext v
    simp only [augmentation,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨jb,hjb⟩,hp⟩
      exact ⟨jb,by simpa [← hjb,newVertex] using hp,hjb⟩
    · rintro ⟨jb,hp,rfl⟩
      exact ⟨⟨jb,rfl⟩,hp⟩
  unfold partCard
  rw [he,Finset.card_image_of_injective _ (newVertex_injective hodd L r xy hv)]
  cases L <;> fin_cases p <;> decide

theorem initial_injective (L : Layout) : Function.Injective (initial L) := by
  change ∀ i j : Fin 3, initial L i = initial L j → i=j
  cases L <;> decide

theorem outputs_eq_image (L : Layout) (r : Fin 6 → G) (xy : G × G) :
    outputs L r xy = Finset.univ.image (fun p : Fin 3 ↦ newVertex L r xy (initial L p,false)) := by
  simp only [outputs,outputAtoms,Finset.image_image]
  rfl

theorem initialVertex_injective (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G) (hv : Valid L r xy) :
    Function.Injective (fun p : Fin 3 ↦ newVertex L r xy (initial L p,false)) := by
  intro p q he
  exact initial_injective L (congrArg Prod.fst (newVertex_injective hodd L r xy hv he))

theorem outputs_partCard (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G) (hv : Valid L r xy) (p : Part) :
    partCard (outputs L r xy) p = 1 := by
  have he : (outputs L r xy).filter (fun v ↦ v.1=p) =
      (Finset.univ.filter (fun j : Fin 3 ↦ part L (initial L j)=p)).image
        (fun j : Fin 3 ↦ newVertex L r xy (initial L j,false)) := by
    rw [outputs_eq_image]
    ext v
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨j,hj⟩,hp⟩
      exact ⟨j,by simpa [← hj,newVertex] using hp,hj⟩
    · rintro ⟨j,hp,rfl⟩
      exact ⟨⟨j,rfl⟩,hp⟩
  unfold partCard
  rw [he,Finset.card_image_of_injective _ (initialVertex_injective hodd L r xy hv)]
  cases L <;> fin_cases p <;> decide

theorem outputs_subset_augmentation (L : Layout) (r : Fin 6 → G) (xy : G × G) :
    outputs L r xy ⊆ augmentation L r xy := by
  rw [outputs_eq_image]
  intro v hv
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨(initial L p,false),Finset.mem_univ _,rfl⟩

theorem augmentation_nonzero (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (hv : Valid L r xy) (v : Vertex G) (hm : v ∈ augmentation L r xy) : v.2 ≠ 0 := by
  obtain ⟨⟨j,b⟩,_,rfl⟩ := Finset.mem_image.mp hm
  cases b <;> simpa [newVertex,signedFlow] using hv.1 j

theorem roots_disjoint_augmentation (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (hv : Valid L r xy) : Disjoint (roots L r) (augmentation L r xy) := by
  apply Finset.disjoint_left.mpr
  intro v hr hv'
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨jb,_,he⟩ := Finset.mem_image.mp hv'
  have hc : signedFlow L r xy jb = r i := congrArg Prod.snd he
  have hm : signedFlow L r xy jb ∈ orbitSupport L r xy :=
    Finset.mem_image.mpr ⟨jb,Finset.mem_univ _,rfl⟩
  exact Finset.disjoint_left.mp hv.2.2 hm (hc ▸ rootSupport_mem r i)

theorem augmentation_numerical_mem (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (v : Vertex G) (hv : v ∈ augmentation L r xy) : v.2 ∈ orbitSupport L r xy := by
  obtain ⟨jb,_,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨jb,Finset.mem_univ _,rfl⟩

theorem outputs_sum (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G) (hv : Valid L r xy) :
    ∑ v ∈ outputs L r xy, v.2 = rootSum r := by
  rw [outputs_eq_image,Finset.sum_image]
  · exact output_sum L r xy
  · exact fun _ _ _ _ h ↦ initialVertex_injective hodd L r xy hv h

theorem roots_sum (L : Layout) (r : Fin 6 → G) (hr : RootLegal L r) :
    ∑ v ∈ roots L r, v.2 = rootSum r := by
  rw [roots,Finset.sum_image]
  · rfl
  · exact fun _ _ _ _ h ↦ hr.2 h

def matchingEdges (L : Layout) (r : Fin 6 → G) (xy : G × G) :
    Finset (Finset (Vertex G)) := Finset.univ.image (state L r xy)

theorem matchingEdges_hyperedge (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (E : Finset (Vertex G)) (hE : E ∈ matchingEdges L r xy) :
    EndpointSelector.IsHyperedge E := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hE
  exact state_hyperedge L r xy i

theorem matchingEdges_disjoint (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (hr : RootLegal L r) (hv : Valid L r xy) :
    (matchingEdges L r xy : Set (Finset (Vertex G))).Pairwise Disjoint := by
  intro E hE F hF hne
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hE
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hF
  apply (regular_flow_matching hodd L r xy hr hv).2.1
  intro he
  exact hne (congrArg (state L r xy) he)

theorem matchingEdges_cover (L : Layout) (r : Fin 6 → G) (xy : G × G) :
    (matchingEdges L r xy).biUnion id ∪ outputs L r xy =
      roots L r ∪ augmentation L r xy := by
  simpa only [matchingEdges,Finset.image_biUnion,id_eq] using state_cover_with_outputs L r xy

theorem matchingEdges_disjoint_outputs (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (hr : RootLegal L r) (hv : Valid L r xy) :
    Disjoint ((matchingEdges L r xy).biUnion id) (outputs L r xy) := by
  rw [matchingEdges,Finset.image_biUnion]
  apply (Finset.disjoint_biUnion_left _ _ _).mpr
  intro i _
  exact (regular_flow_matching hodd L r xy hr hv).2.2.1 i

end

end EndpointFlow
