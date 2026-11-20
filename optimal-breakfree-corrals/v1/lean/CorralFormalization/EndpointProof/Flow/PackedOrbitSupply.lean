import CorralFormalization.EndpointProof.Flow.Packing
import CorralFormalization.EndpointProof.Selector.PackedOrbitSupply
import CorralFormalization.EndpointProof.Probability.FlowAvailability

/-!
The actual regular-flow candidates supply their own inverse-orbit embedding
and Q demands to the maintained common-sample law.  A query here includes a
specific regular layout, with its proved legality and nonzero root blocks.
The separate layout-selection obligation is not hidden in this query type.
-/

open scoped Classical BigOperators NNReal

namespace EndpointFlow

set_option maxHeartbeats 1500000
set_option maxRecDepth 2048

open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

structure PackedFlows (L : Layout) (r : Fin 6 → G) (M : ℕ) where
  parameter : Fin M ↪ G × G
  valid : ∀ i, Valid L r (parameter i)
  disjoint : Pairwise fun i j ↦
    Disjoint (orbitSupport L r (parameter i)) (orbitSupport L r (parameter j))

theorem exists_packedFlows (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (hr : OffsetDistinct L r) (M : ℕ)
    (hsize : 189+324*M < Fintype.card G) : Nonempty (PackedFlows L r M) := by
  obtain ⟨U,hU,hvalid,hdisj⟩ := exists_disjoint_packing hodd L r hr M hsize
  let eqv : U ≃ Fin M := Fintype.equivFinOfCardEq (by simpa using hU)
  let f : Fin M ↪ G × G :=
    ⟨fun i ↦ (eqv.symm i).val,Subtype.val_injective.comp eqv.symm.injective⟩
  refine ⟨⟨f,fun i ↦ hvalid (f i) (eqv.symm i).property,?_⟩⟩
  intro i j hij
  exact hdisj (eqv.symm i).property (eqv.symm j).property (fun h ↦ hij (f.injective h))

def PackedFlows.orbitEmbedding {L : Layout} {r : Fin 6 → G} {M : ℕ}
    (P : PackedFlows L r M) (hodd : Odd (Fintype.card G)) :
    Fin M × Fin 9 ↪ OddOrbit G where
  toFun ij := EndpointSelector.actualOrbit hodd (flow L r (P.parameter ij.1) ij.2)
    ((P.valid ij.1).1 ij.2)
  inj' := by
    rintro ⟨i,j⟩ ⟨k,l⟩ he
    have hs := EndpointSelector.signed_of_actualOrbit_eq hodd
      (flow L r (P.parameter i) j) (flow L r (P.parameter k) l)
      ((P.valid i).1 j) ((P.valid k).1 l) he
    have hik : i = k := by
      by_contra hik
      have hd := P.disjoint hik
      have hj := flow_mem_orbitSupport L r (P.parameter i) j
      have hl : flow L r (P.parameter i) j ∈ orbitSupport L r (P.parameter k) :=
        (mem_orbitSupport _ _ _ _).2 ⟨l,hs⟩
      exact Finset.disjoint_left.mp hd hj hl
    subst k
    have hjl : j = l := by
      by_contra hjl
      have hd := (P.valid i).2.1 j l hjl
      exact hs.elim hd.1 hd.2
    exact Prod.ext rfl hjl

theorem PackedFlows.support_eq {L : Layout} {r : Fin 6 → G} {M : ℕ}
    (P : PackedFlows L r M) (hodd : Odd (Fintype.card G)) (i : Fin M) :
    support (P.orbitEmbedding hodd) orbitPlace i = orbitSupport L r (P.parameter i) := by
  ext x
  simp only [support,Finset.mem_image,Finset.mem_univ,true_and,mem_orbitSupport]
  constructor
  · rintro ⟨⟨j,t⟩,hx⟩
    exact ⟨j,(EndpointSelector.orbitPlace_actualOrbit_iff hodd
      (flow L r (P.parameter i) j) ((P.valid i).1 j) x).1 ⟨t,hx⟩⟩
  · rintro ⟨j,hx⟩
    obtain ⟨t,ht⟩ := (EndpointSelector.orbitPlace_actualOrbit_iff hodd
      (flow L r (P.parameter i) j) ((P.valid i).1 j) x).2 hx
    exact ⟨(j,t),ht⟩

abbrev RegularQuery (G : Type*) [CommRing G] :=
  {Lr : Layout × (Fin 6 → G) // RootLegal Lr.1 Lr.2 ∧ OffsetDistinct Lr.1 Lr.2}

theorem regularQuery_card_le :
    Fintype.card (RegularQuery G) ≤ 3*(Fintype.card G)^6 := by
  have hc : Fintype.card Layout = 3 := by decide
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,hc] using
    Fintype.card_le_of_injective (fun r : RegularQuery G ↦ r.val) Subtype.val_injective

def linearOrbitPacking (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (r : RegularQuery G) : PackedFlows r.val.1 r.val.2 (Fintype.card G/1000) :=
  Classical.choice (exists_packedFlows hodd r.val.1 r.val.2 r.property.2
    (Fintype.card G/1000) (by omega))

def queryEmbedding (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (r : RegularQuery G) : Fin (Fintype.card G/1000) × Fin 9 ↪ OddOrbit G :=
  (linearOrbitPacking hodd hn r).orbitEmbedding hodd

def flowDemand (L : Layout) (j : Fin 9) : Label :=
  EndpointReservoirAvailability.encodeChild (some (part L j,true))

theorem flowDemand_probability (p τ : ℝ≥0) (L : Layout) :
    successProbability p τ (flowDemand L) = (τ : ℝ)^9 := by
  cases L <;> simp [successProbability,flowDemand,part,
    EndpointReservoirAvailability.encodeChild,labelWeights,Fin.prod_univ_succ] <;> ring

/-- The literal child-Q membership in the actual shared augmentation. -/
def QVertex (ω : EndpointFullProduct.FullSample G) (v : Vertex G) : Prop :=
  ∃ (o : OddOrbit G) (side : Bool), orbitPlace (o,side) = v.2 ∧
    childLabel ((EndpointFullProduct.regroup ω).1 o) = some (v.1,true)

theorem qVertex_originalSigned (ω : EndpointFullProduct.FullSample G)
    (v : Vertex G) (hv : QVertex ω v) :
    EndpointFullProduct.originalSigned v.1 (EndpointFullProduct.originalProcess ω) v.2 := by
  obtain ⟨o,side,hcoord,hchild⟩ := hv
  apply EndpointFullProduct.signedMinus_subset_originalSigned
  rw [← hcoord]
  exact EndpointFullProduct.child_signed_containment v.1 true side ω o hchild

theorem candidate_augmentation_Q {L : Layout} {r : Fin 6 → G} {M : ℕ}
    (P : PackedFlows L r M) (hodd : Odd (Fintype.card G))
    (ω : EndpointFullProduct.FullSample G) (i : Fin M)
    (hs : ∀ j, EndpointFullProduct.fullLabels ω (P.orbitEmbedding hodd (i,j)) =
      flowDemand L j) : ∀ v ∈ augmentation L r (P.parameter i), QVertex ω v := by
  intro v hv
  obtain ⟨⟨j,b⟩,_,rfl⟩ := Finset.mem_image.mp hv
  have hc : childLabel ((EndpointFullProduct.regroup ω).1 (P.orbitEmbedding hodd (i,j))) =
      some (part L j,true) := by
    apply EndpointReservoirAvailability.encodeChild_bijective.injective
    exact hs j
  have hsign : signedFlow L r (P.parameter i) (j,b) = flow L r (P.parameter i) j ∨
      signedFlow L r (P.parameter i) (j,b) = -flow L r (P.parameter i) j := by
    cases b <;> simp [signedFlow]
  obtain ⟨t,ht⟩ := (EndpointSelector.orbitPlace_actualOrbit_iff hodd
    (flow L r (P.parameter i) j) ((P.valid i).1 j) _).2 hsign
  exact ⟨P.orbitEmbedding hodd (i,j),t,ht,hc⟩

theorem successful_regular_flow
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hg : EndpointFullProduct.FullAvailable (queryEmbedding hodd hn)
      (fun r _ ↦ flowDemand r.val.1) budget ω)
    (r : RegularQuery G) (F : Finset G) (hF : F.card ≤ budget) :
    ∃ xy : G × G, Valid r.val.1 r.val.2 xy ∧
      Disjoint (orbitSupport r.val.1 r.val.2 xy) F ∧
      (∀ v ∈ augmentation r.val.1 r.val.2 xy, QVertex ω v ∧
        EndpointFullProduct.originalSigned v.1 (EndpointFullProduct.originalProcess ω) v.2) ∧
      (∀ i, EndpointSelector.IsHyperedge (state r.val.1 r.val.2 xy i)) ∧
      Pairwise (fun i j ↦ Disjoint (state r.val.1 r.val.2 xy i) (state r.val.1 r.val.2 xy j)) ∧
      (∀ i, Disjoint (state r.val.1 r.val.2 xy i) (outputs r.val.1 r.val.2 xy)) ∧
      Finset.univ.biUnion (state r.val.1 r.val.2 xy) ∪ outputs r.val.1 r.val.2 xy =
        roots r.val.1 r.val.2 ∪ augmentation r.val.1 r.val.2 xy := by
  obtain ⟨i,hi,hd⟩ := hg r F hF
  have hv := (linearOrbitPacking hodd hn r).valid i
  have hm := regular_flow_matching hodd r.val.1 r.val.2
    ((linearOrbitPacking hodd hn r).parameter i) r.property.1 hv
  have hQ := candidate_augmentation_Q (linearOrbitPacking hodd hn r) hodd ω i
    (fun j ↦ congrFun hi j)
  have hd' : Disjoint (orbitSupport r.val.1 r.val.2 ((linearOrbitPacking hodd hn r).parameter i)) F := by
    change Disjoint (support ((linearOrbitPacking hodd hn r).orbitEmbedding hodd) orbitPlace i) F at hd
    rw [(linearOrbitPacking hodd hn r).support_eq hodd i] at hd
    exact hd
  exact ⟨_,hv,hd',fun v hv ↦ ⟨hQ v hv,qVertex_originalSigned ω v (hQ v hv)⟩,hm⟩

end

end EndpointFlow
