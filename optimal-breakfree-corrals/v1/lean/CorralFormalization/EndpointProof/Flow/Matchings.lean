import CorralFormalization.EndpointProof.Flow.Algebra

/-!
The seven actual zero-sum edges of each regular layout.  The proof first
partitions 24 combinatorial atoms (six roots and eighteen incidences), then
uses the proved numerical freshness to show that their realization is
injective.  Thus the coverage and disjointness are genuine set statements.
-/

open scoped BigOperators

namespace EndpointFlow

set_option maxHeartbeats 1500000
set_option maxRecDepth 2048

section

variable {G : Type*} [CommRing G] [DecidableEq G]

def IsMatchingOn {I : Type*} [Fintype I]
    (E : I → Finset (Vertex G)) (S : Finset (Vertex G)) : Prop :=
  (∀ i, EndpointSelector.IsHyperedge (E i)) ∧
  Pairwise (fun i j ↦ Disjoint (E i) (E j)) ∧ Finset.univ.biUnion E = S

def taggedTriple (p q t : Part) (x y z : G) : Finset (Vertex G) :=
  {(p,x),(q,y),(t,z)}

theorem taggedTriple_hyperedge (p q t : Part) (x y z : G)
    (hpq : p ≠ q) (hpt : p ≠ t) (hqt : q ≠ t) (hs : x+y+z=0) :
    EndpointSelector.IsHyperedge (taggedTriple p q t x y z) := by
  fin_cases p <;> fin_cases q <;> fin_cases t
  all_goals simp_all only [ne_eq,not_true_eq_false]
  all_goals first
    | (refine ⟨x,y,z,hs,?_⟩; ext v; simp [taggedTriple,EndpointSelector.edge] <;> tauto)
    | (refine ⟨x,z,y,by linear_combination hs,?_⟩;
       ext v; simp [taggedTriple,EndpointSelector.edge] <;> tauto)
    | (refine ⟨y,x,z,by linear_combination hs,?_⟩;
       ext v; simp [taggedTriple,EndpointSelector.edge] <;> tauto)
    | (refine ⟨y,z,x,by linear_combination hs,?_⟩;
       ext v; simp [taggedTriple,EndpointSelector.edge] <;> tauto)
    | (refine ⟨z,x,y,by linear_combination hs,?_⟩;
       ext v; simp [taggedTriple,EndpointSelector.edge] <;> tauto)
    | (refine ⟨z,y,x,by linear_combination hs,?_⟩;
       ext v; simp [taggedTriple,EndpointSelector.edge] <;> tauto)

theorem root_tags_distinct (L : Layout) (i : Fin 6) :
    rootPart L i ≠ part L (incoming L i) ∧
    rootPart L i ≠ part L (outgoing L i) ∧
    part L (incoming L i) ≠ part L (outgoing L i) := by
  cases L <;> fin_cases i <;> decide

theorem terminal_tags_distinct (L : Layout) :
    part L (terminal L 0) ≠ part L (terminal L 1) ∧
    part L (terminal L 0) ≠ part L (terminal L 2) ∧
    part L (terminal L 1) ≠ part L (terminal L 2) := by
  cases L <;> decide

theorem state_root (L : Layout) (r : Fin 6 → G) (xy : G × G) (i : Fin 6) :
    state L r xy ⟨i.val,by omega⟩ =
      taggedTriple (rootPart L i) (part L (incoming L i)) (part L (outgoing L i))
        (r i) (-flow L r xy (incoming L i)) (flow L r xy (outgoing L i)) := by
  simp [state,nodeAtoms,taggedTriple,atomVertex,rootVertex,newVertex,signedFlow,i.isLt]

theorem state_terminal (L : Layout) (r : Fin 6 → G) (xy : G × G) :
    state L r xy 6 =
      taggedTriple (part L (terminal L 0)) (part L (terminal L 1))
        (part L (terminal L 2)) (-flow L r xy (terminal L 0))
        (-flow L r xy (terminal L 1)) (-flow L r xy (terminal L 2)) := by
  ext v
  simp [state,nodeAtoms,taggedTriple,atomVertex,newVertex,signedFlow,
    Fin.exists_fin_succ]
  simp only [eq_comm]

theorem state_hyperedge (L : Layout) (r : Fin 6 → G) (xy : G × G) (i : Fin 7) :
    EndpointSelector.IsHyperedge (state L r xy i) := by
  by_cases hi : i.val < 6
  · let k : Fin 6 := ⟨i.val,hi⟩
    have hi' : i = ⟨k.val,by omega⟩ := Fin.ext rfl
    rw [hi',state_root]
    have htags := root_tags_distinct L k
    apply taggedTriple_hyperedge _ _ _ _ _ _ htags.1 htags.2.1 htags.2.2
    linear_combination flow_step L r xy k
  · have hi' : i = 6 := Fin.ext (by omega)
    rw [hi',state_terminal]
    have htags := terminal_tags_distinct L
    apply taggedTriple_hyperedge _ _ _ _ _ _ htags.1 htags.2.1 htags.2.2
    have hs := terminal_sum L r xy
    simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero] at hs
    norm_num only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two] at hs
    linear_combination hs

theorem signedFlow_injective [Fintype G] (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G) (hv : Valid L r xy) :
    Function.Injective (signedFlow L r xy) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  have hij : i = j := by
    by_contra hij
    have hd := hv.2.1 i j hij
    cases b <;> cases c <;> simp only [signedFlow,Bool.false_eq_true,
      ↓reduceIte] at h
    · exact hd.1 h
    · exact hd.2 h
    · apply hd.2; linear_combination -h
    · exact hd.1 (neg_inj.mp h)
  subst j
  have hbc : b = c := by
    have hn := EndpointSelector.ne_neg_of_odd hodd (hv.1 i)
    cases b <;> cases c
    · rfl
    · exact False.elim (hn h)
    · apply False.elim; apply hn; simpa [signedFlow] using h.symm
    · rfl
  exact Prod.ext rfl hbc

theorem newVertex_injective [Fintype G] (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G) (hv : Valid L r xy) :
    Function.Injective (newVertex L r xy) := by
  intro i j h
  exact signedFlow_injective hodd L r xy hv (congrArg Prod.snd h)

theorem atomVertex_injective [Fintype G] (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (hr : RootLegal L r) (hv : Valid L r xy) :
    Function.Injective (atomVertex L r xy) := by
  intro a b h
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (hr.2 h)
    | inr jb =>
      have hm : signedFlow L r xy jb ∈ orbitSupport L r xy :=
        Finset.mem_image.mpr ⟨jb,Finset.mem_univ _,rfl⟩
      have he : r i = signedFlow L r xy jb := congrArg Prod.snd h
      exact False.elim (Finset.disjoint_left.mp hv.2.2 hm
        (he ▸ rootSupport_mem r i))
  | inr ia =>
    cases b with
    | inl j =>
      have hm : signedFlow L r xy ia ∈ orbitSupport L r xy :=
        Finset.mem_image.mpr ⟨ia,Finset.mem_univ _,rfl⟩
      have he : signedFlow L r xy ia = r j := congrArg Prod.snd h
      exact False.elim (Finset.disjoint_left.mp hv.2.2 hm
        (he ▸ rootSupport_mem r j))
    | inr jb => exact congrArg Sum.inr (newVertex_injective hodd L r xy hv h)

theorem allAtoms_image (L : Layout) (r : Fin 6 → G) (xy : G × G) :
    Finset.univ.image (atomVertex L r xy) = roots L r ∪ augmentation L r xy := by
  ext v
  simp [roots,augmentation,atomVertex]

theorem state_cover_with_outputs (L : Layout) (r : Fin 6 → G) (xy : G × G) :
    Finset.univ.biUnion (state L r xy) ∪ outputs L r xy =
      roots L r ∪ augmentation L r xy := by
  rw [← allAtoms_image L r xy,← nodeAtoms_cover L]
  simp only [Finset.image_union,Finset.biUnion_image,outputs]
  rfl

theorem regular_flow_matching [Fintype G] (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (hr : RootLegal L r) (hv : Valid L r xy) :
    (∀ i, EndpointSelector.IsHyperedge (state L r xy i)) ∧
    Pairwise (fun i j ↦ Disjoint (state L r xy i) (state L r xy j)) ∧
    (∀ i, Disjoint (state L r xy i) (outputs L r xy)) ∧
    Finset.univ.biUnion (state L r xy) ∪ outputs L r xy =
      roots L r ∪ augmentation L r xy := by
  have hinj := atomVertex_injective hodd L r xy hr hv
  refine ⟨state_hyperedge L r xy,?_,?_,state_cover_with_outputs L r xy⟩
  · intro i j hij
    exact (Finset.disjoint_image hinj).2 (nodeAtoms_disjoint L hij)
  · intro i
    exact (Finset.disjoint_image hinj).2 (nodeAtoms_disjoint_outputAtoms L i)

theorem augmentation_card [Fintype G] (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G) (hv : Valid L r xy) :
    (augmentation L r xy).card = 18 := by
  rw [augmentation,Finset.card_image_of_injective _ (newVertex_injective hodd L r xy hv)]
  simp

theorem augmentation_paired (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (v : Vertex G) : v ∈ augmentation L r xy → (v.1,-v.2) ∈ augmentation L r xy := by
  rintro hv
  obtain ⟨⟨j,b⟩,_,rfl⟩ := Finset.mem_image.mp hv
  refine Finset.mem_image.mpr ⟨(j,!b),Finset.mem_univ _,?_⟩
  cases b <;> simp [newVertex,signedFlow]

theorem outputs_card [Fintype G] (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (hr : RootLegal L r) (hv : Valid L r xy) : (outputs L r xy).card = 3 := by
  rw [outputs,Finset.card_image_of_injective _ (atomVertex_injective hodd L r xy hr hv)]
  exact outputAtoms_card L

end

end EndpointFlow
