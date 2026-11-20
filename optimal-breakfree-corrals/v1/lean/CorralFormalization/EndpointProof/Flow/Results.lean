import CorralFormalization.EndpointProof.Flow.LayoutSelection
import CorralFormalization.EndpointProof.Flow.Cover.Partition

/-! MatchingOn, OnePerPart and balanced-inventory adapters for the actual flows. -/

open scoped Classical BigOperators

namespace EndpointFlow

set_option maxHeartbeats 1500000
set_option maxRecDepth 2048

open EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

theorem union_eq_of_disjoint_eq {A O B : Finset (Vertex G)}
    (he : A ∪ O = B) (hd : Disjoint A O) : A = B \ O := by
  ext v
  have hh : v ∈ A ∨ v ∈ O ↔ v ∈ B := by
    simpa only [Finset.mem_union] using Iff.of_eq (congrArg (fun S ↦ v ∈ S) he)
  have hdis : ¬(v ∈ A ∧ v ∈ O) := fun h ↦ Finset.disjoint_left.mp hd h.1 h.2
  simp only [Finset.mem_sdiff]
  tauto

def regularMatchingOn (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (hr : RootLegal L r) (hv : Valid L r xy) :
    MatchingOn ((roots L r ∪ augmentation L r xy) \ outputs L r xy) where
  edges := matchingEdges L r xy
  valid := matchingEdges_hyperedge L r xy
  disjoint := matchingEdges_disjoint hodd L r xy hr hv
  cover := union_eq_of_disjoint_eq (matchingEdges_cover L r xy)
    (matchingEdges_disjoint_outputs hodd L r xy hr hv)

theorem onePerPart_of_partCard (S : Finset (Vertex G)) (hS : ∀ p, partCard S p=1) :
    Cover.OnePerPart S := by
  intro p
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (hS p)
  have hvm : v ∈ S.filter (fun w ↦ w.1=p) := by rw [hv]; exact Finset.mem_singleton_self v
  have hm : v ∈ S ∧ v.1=p := Finset.mem_filter.mp hvm
  refine ⟨v.2,?_,?_⟩
  · simpa only [← hm.2,Prod.eta] using hm.1
  · intro x hx
    have hmem : (p,x) ∈ S.filter (fun w ↦ w.1=p) := Finset.mem_filter.mpr ⟨hx,rfl⟩
    rw [hv] at hmem
    exact congrArg Prod.snd (Finset.mem_singleton.mp hmem)

theorem regular_outputs_onePerPart (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G) (hv : Valid L r xy) :
    Cover.OnePerPart (outputs L r xy) :=
  onePerPart_of_partCard _ (outputs_partCard hodd L r xy hv)

theorem regular_augmentation_balanced (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G) (hv : Valid L r xy) :
    Cover.Balanced (augmentation L r xy) := by
  intro p
  change partCard _ p = partCard _ 0
  rw [augmentation_partCard hodd L r xy hv p,augmentation_partCard hodd L r xy hv 0]

theorem rotate_partCard (σ : Equiv.Perm Part) (S : Finset (Vertex G)) (p : Part) :
    partCard (rotate σ S) p = partCard S (σ.symm p) := by
  unfold partCard rotate
  rw [Finset.filter_image,Finset.card_image_of_injective _ (tagEquiv σ).injective]
  congr 1
  apply Finset.filter_congr
  intro v _
  change σ v.1=p ↔ v.1=σ.symm p
  constructor
  · intro he; simpa using congrArg σ.symm he
  · intro he; rw [he]; simp

theorem rotate_balanced (σ : Equiv.Perm Part) (S : Finset (Vertex G))
    (hb : Cover.Balanced S) : Cover.Balanced (rotate σ S) := by
  intro p
  change partCard _ p = partCard _ 0
  rw [rotate_partCard,rotate_partCard]
  exact (hb (σ.symm p)).trans (hb (σ.symm 0)).symm

theorem rotate_regular_outputs_onePerPart (hodd : Odd (Fintype.card G))
    (σ : Equiv.Perm Part) (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (hv : Valid L r xy) : Cover.OnePerPart (rotate σ (outputs L r xy)) := by
  apply onePerPart_of_partCard
  intro p
  rw [rotate_partCard,outputs_partCard hodd L r xy hv]

def exceptionalMatchingEdges (a : G) (xy : G × G) : Finset (Finset (Vertex G)) :=
  Finset.univ.image (exceptionalState a xy)

def exceptionalMatchingOn (hodd : Odd (Fintype.card G)) (a : G) (ha : a ≠ 0)
    (h3a : a+a+a=0) (xy : G × G) (hv : Valid .first (dummyRoots a) xy) :
    MatchingOn ((exceptionalRoots a ∪ exceptionalAugmentation xy) \ exceptionalOutputs xy) where
  edges := exceptionalMatchingEdges a xy
  valid := by
    intro E hE
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hE
    exact exceptional_edges a h3a xy i
  disjoint := by
    intro E hE F hF hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hF
    apply (exceptional_disjoint hodd a ha h3a xy hv).1
    intro he
    exact hne (congrArg (exceptionalState a xy) he)
  cover := by
    have hc : (exceptionalMatchingEdges a xy).biUnion id ∪ exceptionalOutputs xy =
        exceptionalRoots a ∪ exceptionalAugmentation xy := by
      simpa only [exceptionalMatchingEdges,Finset.image_biUnion,id_eq] using
        exceptional_cover a xy
    apply union_eq_of_disjoint_eq hc
    rw [exceptionalMatchingEdges,Finset.image_biUnion]
    apply (Finset.disjoint_biUnion_left _ _ _).mpr
    intro i _
    exact (exceptional_disjoint hodd a ha h3a xy hv).2 i

theorem exceptional_outputs_onePerPart (xy : G × G) : Cover.OnePerPart (exceptionalOutputs xy) := by
  intro p
  refine ⟨exceptionalRep xy p,?_,?_⟩
  · fin_cases p <;> simp [exceptionalOutputs,EndpointSelector.edge]
  · intro x hx
    fin_cases p <;> simpa [exceptionalOutputs,EndpointSelector.edge] using hx

theorem exceptional_outputs_subset (xy : G × G) :
    exceptionalOutputs xy ⊆ exceptionalAugmentation xy := by
  intro v hv
  simp only [exceptionalOutputs,EndpointSelector.edge,Finset.mem_insert,
    Finset.mem_singleton] at hv
  rcases hv with rfl|rfl|rfl
  · exact Finset.mem_image.mpr ⟨(0,false),Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨(1,false),Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨(2,false),Finset.mem_univ _,rfl⟩

theorem exceptional_slot_injective : Function.Injective exceptionalSlot := by
  intro p q he
  fin_cases p <;> fin_cases q <;> simp_all [exceptionalSlot]

theorem exceptionalVertex_eq (a : G) (h3a : a+a+a=0) (xy : G × G) (pb : Part × Bool) :
    (pb.1,if pb.2 then -exceptionalRep xy pb.1 else exceptionalRep xy pb.1) =
      newVertex .first (dummyRoots a) xy (exceptionalSlot pb.1,pb.2) := by
  rcases pb with ⟨p,b⟩
  cases b <;> simp [newVertex,signedFlow,exceptionalSlot_part,← exceptionalRep_eq_flow a h3a]

theorem exceptionalVertex_injective (hodd : Odd (Fintype.card G))
    (a : G) (h3a : a+a+a=0) (xy : G × G) (hv : Valid .first (dummyRoots a) xy) :
    Function.Injective (fun pb : Part × Bool ↦
      (pb.1,if pb.2 then -exceptionalRep xy pb.1 else exceptionalRep xy pb.1)) := by
  intro pb qc he
  dsimp only at he
  rw [exceptionalVertex_eq a h3a xy pb,exceptionalVertex_eq a h3a xy qc] at he
  have hh := newVertex_injective hodd .first (dummyRoots a) xy hv he
  exact Prod.ext (exceptional_slot_injective (congrArg Prod.fst hh))
    (congrArg (fun z : Fin 9 × Bool ↦ z.2) hh)

theorem exceptional_augmentation_partCard (hodd : Odd (Fintype.card G))
    (a : G) (h3a : a+a+a=0) (xy : G × G) (hv : Valid .first (dummyRoots a) xy) (p : Part) :
    partCard (exceptionalAugmentation xy) p = 2 := by
  unfold partCard exceptionalAugmentation
  rw [Finset.filter_image,Finset.card_image_of_injective _
    (exceptionalVertex_injective hodd a h3a xy hv)]
  change (Finset.univ.filter (fun pb : Part × Bool ↦ pb.1=p)).card = 2
  fin_cases p <;> decide

theorem exceptional_augmentation_balanced (hodd : Odd (Fintype.card G))
    (a : G) (h3a : a+a+a=0) (xy : G × G) (hv : Valid .first (dummyRoots a) xy) :
    Cover.Balanced (exceptionalAugmentation xy) := by
  intro p
  change partCard _ p = partCard _ 0
  rw [exceptional_augmentation_partCard hodd a h3a xy hv p,
    exceptional_augmentation_partCard hodd a h3a xy hv 0]

theorem exceptional_augmentation_nonzero (a : G) (h3a : a+a+a=0) (xy : G × G)
    (hv : Valid .first (dummyRoots a) xy) (v : Vertex G)
    (hm : v ∈ exceptionalAugmentation xy) : v.2 ≠ 0 := by
  have hs := exceptional_support_subset a h3a xy v hm
  obtain ⟨j,hj|hj⟩ := (mem_orbitSupport _ _ _ _).mp hs
  · rw [hj]; exact hv.1 j
  · rw [hj]; exact neg_ne_zero.mpr (hv.1 j)

theorem exceptional_augmentation_subset (a : G) (h3a : a+a+a=0) (xy : G × G) :
    exceptionalAugmentation xy ⊆ augmentation .first (dummyRoots a) xy := by
  intro v hv
  obtain ⟨pb,_,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨(exceptionalSlot pb.1,pb.2),Finset.mem_univ _,
    (exceptionalVertex_eq a h3a xy pb).symm⟩

theorem exceptional_roots_disjoint (a : G) (h3a : a+a+a=0) (xy : G × G)
    (hv : Valid .first (dummyRoots a) xy) :
    Disjoint (exceptionalRoots a) (exceptionalAugmentation xy) := by
  apply Finset.disjoint_left.mpr
  intro v hr ht
  have hs := exceptional_support_subset a h3a xy v ht
  obtain ⟨⟨p,b⟩,_,he⟩ := Finset.mem_image.mp hr
  apply Finset.disjoint_left.mp hv.2.2 hs
  have hc := congrArg Prod.snd he
  exact Finset.mem_image.mpr ⟨(0,b),Finset.mem_univ _,by simpa [dummyRoots] using hc⟩

theorem augmentation_numericalSupport (L : Layout) (r : Fin 6 → G) (xy : G × G) :
    numericalSupport (augmentation L r xy) = orbitSupport L r xy := by
  have hpos : (augmentation L r xy).image Prod.snd = orbitSupport L r xy := by
    simp only [augmentation,orbitSupport,Finset.image_image]
    rfl
  have hneg : (augmentation L r xy).image (fun v ↦ -v.2) ⊆ orbitSupport L r xy := by
    intro x hx
    obtain ⟨v,hv,hx⟩ := Finset.mem_image.mp hx
    rw [← hpos]
    exact Finset.mem_image.mpr ⟨(v.1,-v.2),augmentation_paired L r xy v hv,hx⟩
  unfold numericalSupport
  rw [hpos]
  exact Finset.union_eq_left.mpr hneg

theorem roots_numericalSupport (L : Layout) (r : Fin 6 → G) :
    numericalSupport (roots L r) = rootSupport r := by
  unfold numericalSupport roots rootSupport
  simp only [Finset.image_image]
  ext x
  simp only [Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (⟨i,hi⟩|⟨i,hi⟩)
    · exact ⟨(i,false),hi⟩
    · exact ⟨(i,true),hi⟩
  · rintro ⟨⟨i,b⟩,hi⟩
    cases b
    · exact Or.inl ⟨i,hi⟩
    · exact Or.inr ⟨i,hi⟩

theorem exceptional_numericalSupport_subset (a : G) (h3a : a+a+a=0) (xy : G × G) :
    numericalSupport (exceptionalAugmentation xy) ⊆ orbitSupport .first (dummyRoots a) xy := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx|hx
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    exact exceptional_support_subset a h3a xy v hv
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    exact exceptional_support_subset a h3a xy (v.1,-v.2) (exceptional_paired xy v hv)

theorem exceptional_roots_numericalSupport (a : G) :
    numericalSupport (exceptionalRoots a) = rootSupport (dummyRoots a) := by
  ext x
  simp only [numericalSupport,exceptionalRoots,rootSupport,Finset.image_image,
    Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (⟨⟨p,b⟩,hx⟩|⟨⟨p,b⟩,hx⟩)
    · exact ⟨(0,b),hx⟩
    · refine ⟨(0,!b),?_⟩
      cases b <;> simpa [dummyRoots] using hx
  · rintro ⟨⟨i,b⟩,hx⟩
    exact Or.inl ⟨(0,b),hx⟩

end

end EndpointFlow
