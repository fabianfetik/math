import CorralFormalization.EndpointProof.Flow.Cases
import CorralFormalization.EndpointProof.Flow.PackedOrbitSupply

/-!
# The genuine 3a=0 exception in the paired cover construction

The nine-orbit candidate is padded using the three translates 0,a,2a on
each path.  Only its three initial inverse pairs occur in the actual
augmentation.  The other six orbits are explicit unused Q demands.  No
RootLegal assertion is made for the artificial constant root list.
-/

open scoped Classical BigOperators NNReal

namespace EndpointFlow

set_option maxHeartbeats 1500000
set_option maxRecDepth 2048

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

def dummyRoots (a : G) : Fin 6 → G := fun _ ↦ a

theorem dummyRoots_offsetDistinct (hodd : Odd (Fintype.card G))
    (a : G) (ha : a ≠ 0) : OffsetDistinct .first (dummyRoots a) := by
  have h2a : a+a ≠ 0 := by
    intro h
    apply ha
    exact EndpointSelector.doubling_injective_of_odd hodd (by simpa using h)
  exact two_block_offsetDistinct .first (by decide) (dummyRoots a) (fun _ ↦ ha)
    h2a h2a h2a

theorem dummyRoots_sum (a : G) (h3a : a+a+a=0) : rootSum (dummyRoots a) = 0 := by
  simp [rootSum,dummyRoots,Fin.sum_univ_succ]
  linear_combination 2*h3a

def exceptionalRep (xy : G × G) : Fin 3 → G := ![-xy.1-xy.2,xy.1,xy.2]
def exceptionalSlot : Fin 3 → Fin 9 := ![6,0,3]

theorem exceptionalRep_eq_flow (a : G) (h3a : a+a+a=0) (xy : G × G) (p : Fin 3) :
    exceptionalRep xy p = flow .first (dummyRoots a) xy (exceptionalSlot p) := by
  fin_cases p <;> simp [exceptionalRep,exceptionalSlot,flow,path,offset,
    base,dummyRoots_sum a h3a]

theorem exceptionalSlot_part (p : Fin 3) : part .first (exceptionalSlot p) = p := by
  fin_cases p <;> decide

def exceptionalRoots (a : G) : Finset (Vertex G) :=
  Finset.univ.image (fun pb : Fin 3 × Bool ↦ (pb.1,if pb.2 then -a else a))

def exceptionalAugmentation (xy : G × G) : Finset (Vertex G) :=
  Finset.univ.image (fun pb : Fin 3 × Bool ↦
    (pb.1,if pb.2 then -exceptionalRep xy pb.1 else exceptionalRep xy pb.1))

def exceptionalOutputs (xy : G × G) : Finset (Vertex G) :=
  EndpointSelector.edge (exceptionalRep xy 0) (exceptionalRep xy 1) (exceptionalRep xy 2)

def exceptionalState (a : G) (xy : G × G) : Fin 3 → Finset (Vertex G) :=
  ![EndpointSelector.edge a a a,EndpointSelector.edge (-a) (-a) (-a),
    EndpointSelector.edge (-exceptionalRep xy 0) (-exceptionalRep xy 1) (-exceptionalRep xy 2)]

theorem exceptional_edges (a : G) (h3a : a+a+a=0) (xy : G × G) (i : Fin 3) :
    EndpointSelector.IsHyperedge (exceptionalState a xy i) := by
  fin_cases i
  · exact ⟨a,a,a,h3a,rfl⟩
  · exact ⟨-a,-a,-a,by linear_combination -h3a,rfl⟩
  · exact ⟨_,_,_,by simp [exceptionalRep] <;> ring,rfl⟩

theorem exceptional_cover (a : G) (xy : G × G) :
    Finset.univ.biUnion (exceptionalState a xy) ∪ exceptionalOutputs xy =
      exceptionalRoots a ∪ exceptionalAugmentation xy := by
  ext v
  simp [exceptionalState,exceptionalOutputs,exceptionalRoots,exceptionalAugmentation,
    EndpointSelector.edge,Fin.exists_fin_succ]
  tauto

theorem exceptional_support_subset (a : G) (h3a : a+a+a=0) (xy : G × G)
    (v : Vertex G) (hv : v ∈ exceptionalAugmentation xy) :
    v.2 ∈ orbitSupport .first (dummyRoots a) xy := by
  obtain ⟨⟨p,b⟩,_,rfl⟩ := Finset.mem_image.mp hv
  apply (mem_orbitSupport _ _ _ _).2
  refine ⟨exceptionalSlot p,?_⟩
  cases b <;> simp [exceptionalRep_eq_flow a h3a]

theorem exceptional_disjoint (hodd : Odd (Fintype.card G)) (a : G) (ha : a ≠ 0)
    (h3a : a+a+a=0) (xy : G × G) (hv : Valid .first (dummyRoots a) xy) :
    Pairwise (fun i j ↦ Disjoint (exceptionalState a xy i) (exceptionalState a xy j)) ∧
    (∀ i, Disjoint (exceptionalState a xy i) (exceptionalOutputs xy)) := by
  have hn := EndpointSelector.ne_neg_of_odd hodd ha
  have hrep (p : Fin 3) : exceptionalRep xy p ≠ 0 := by
    rw [exceptionalRep_eq_flow a h3a]
    exact hv.1 _
  have hpair (p : Fin 3) : exceptionalRep xy p ≠ -exceptionalRep xy p :=
    EndpointSelector.ne_neg_of_odd hodd (hrep p)
  have hroot (p : Fin 3) :
      exceptionalRep xy p ≠ a ∧ exceptionalRep xy p ≠ -a := by
    have hs : exceptionalRep xy p ∈ orbitSupport .first (dummyRoots a) xy := by
      rw [exceptionalRep_eq_flow a h3a]; exact flow_mem_orbitSupport _ _ _ _
    constructor
    · intro he
      apply Finset.disjoint_left.mp hv.2.2 hs
      rw [he]
      exact rootSupport_mem (dummyRoots a) 0
    · intro he
      apply Finset.disjoint_left.mp hv.2.2 hs
      exact Finset.mem_image.mpr ⟨(0,true),Finset.mem_univ _,he.symm⟩
  have hnegroot (p : Fin 3) :
      -exceptionalRep xy p ≠ a ∧ -exceptionalRep xy p ≠ -a := by
    constructor
    · intro he; apply (hroot p).2; linear_combination -he
    · intro he; exact (hroot p).1 (neg_inj.mp he)
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try exact False.elim (hij rfl)
    all_goals simp only [exceptionalState,Matrix.cons_val_succ',Matrix.cons_val_zero']
    all_goals apply (EndpointSelector.edge_disjoint_iff _ _ _ _ _ _).mpr
    all_goals first
      | exact ⟨hn,hn,hn⟩
      | exact ⟨Ne.symm hn,Ne.symm hn,Ne.symm hn⟩
      | exact ⟨(hnegroot 0).1.symm,(hnegroot 1).1.symm,(hnegroot 2).1.symm⟩
      | exact ⟨(hnegroot 0).2.symm,(hnegroot 1).2.symm,(hnegroot 2).2.symm⟩
      | exact ⟨(hnegroot 0).1,(hnegroot 1).1,(hnegroot 2).1⟩
      | exact ⟨(hnegroot 0).2,(hnegroot 1).2,(hnegroot 2).2⟩
  · intro i
    fin_cases i
    all_goals simp only [exceptionalState,exceptionalOutputs,
      Matrix.cons_val_succ',Matrix.cons_val_zero']
    all_goals apply (EndpointSelector.edge_disjoint_iff _ _ _ _ _ _).mpr
    · exact ⟨(hroot 0).1.symm,(hroot 1).1.symm,(hroot 2).1.symm⟩
    · exact ⟨(hroot 0).2.symm,(hroot 1).2.symm,(hroot 2).2.symm⟩
    · exact ⟨(hpair 0).symm,(hpair 1).symm,(hpair 2).symm⟩

theorem exceptional_paired (xy : G × G) (v : Vertex G)
    (hv : v ∈ exceptionalAugmentation xy) :
    (v.1,-v.2) ∈ exceptionalAugmentation xy := by
  obtain ⟨⟨p,b⟩,_,rfl⟩ := Finset.mem_image.mp hv
  refine Finset.mem_image.mpr ⟨(p,!b),Finset.mem_univ _,?_⟩
  cases b <;> simp

theorem exceptionalAugmentation_card_le (xy : G × G) :
    (exceptionalAugmentation xy).card ≤ 6 :=
  Finset.card_image_le.trans (by simp)

abbrev ExceptionalQuery (G : Type*) [CommRing G] := {a : G // a ≠ 0 ∧ a+a+a=0}

theorem exceptionalQuery_card_le : Fintype.card (ExceptionalQuery G) ≤ Fintype.card G :=
  Fintype.card_le_of_injective (fun r : ExceptionalQuery G ↦ r.val) Subtype.val_injective

def exceptionalPacking (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (r : ExceptionalQuery G) : PackedFlows .first (dummyRoots r.val) (Fintype.card G/1000) :=
  Classical.choice (exists_packedFlows hodd .first (dummyRoots r.val)
    (dummyRoots_offsetDistinct hodd r.val r.property.1) _ (by omega))

def exceptionalEmbedding (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (r : ExceptionalQuery G) :
    Fin (Fintype.card G/1000) × Fin 9 ↪ EndpointOriginalReservoir.OddOrbit G :=
  (exceptionalPacking hodd hn r).orbitEmbedding hodd

theorem exceptional_augmentation_Q
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (r : ExceptionalQuery G) (ω : EndpointFullProduct.FullSample G)
    (i : Fin (Fintype.card G/1000))
    (hs : ∀ j, EndpointFullProduct.fullLabels ω (exceptionalEmbedding hodd hn r (i,j)) =
      flowDemand .first j) :
    ∀ v ∈ exceptionalAugmentation ((exceptionalPacking hodd hn r).parameter i), QVertex ω v := by
  intro v hv
  apply candidate_augmentation_Q (exceptionalPacking hodd hn r) hodd ω i hs
  obtain ⟨⟨p,b⟩,_,rfl⟩ := Finset.mem_image.mp hv
  apply Finset.mem_image.mpr
  refine ⟨(exceptionalSlot p,b),Finset.mem_univ _,?_⟩
  have hp := exceptionalSlot_part p
  cases b <;> simp [newVertex,signedFlow,hp,← exceptionalRep_eq_flow r.val r.property.2]

end

end EndpointFlow
