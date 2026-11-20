import CorralFormalization.EndpointProof.Flow.Exceptional
import CorralFormalization.EndpointProof.Flow.Inventories
import CorralFormalization.EndpointProof.Selector.Assembly.Matchings

/-!
One finite query family for all tag permutations of regular flows and the
explicit nine-orbit padding used for the exceptional case.  Only numerical
offset separation is required for packing.  Root legality is checked when
the actual matching is constructed, never for an artificial padding list.
-/

open scoped Classical BigOperators NNReal

namespace EndpointFlow

set_option maxHeartbeats 1500000
set_option maxRecDepth 2048

open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

abbrev AffineQuery (G : Type*) [CommRing G] :=
  {s : Equiv.Perm Part × Layout × (Fin 6 → G) // OffsetDistinct s.2.1 s.2.2}

theorem affineQuery_card_le : Fintype.card (AffineQuery G) ≤ 18*(Fintype.card G)^6 := by
  have hσ : Fintype.card (Equiv.Perm Part) = 6 := by norm_num [Fintype.card_perm,Part]
  have hL : Fintype.card Layout = 3 := by decide
  have h := Fintype.card_le_of_injective (fun r : AffineQuery G ↦ r.val) Subtype.val_injective
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,hσ,hL,
    ← Nat.mul_assoc] using h

def affinePacking (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (r : AffineQuery G) : PackedFlows r.val.2.1 r.val.2.2 (Fintype.card G/1000) :=
  Classical.choice (exists_packedFlows hodd r.val.2.1 r.val.2.2 r.property _ (by omega))

def affineEmbedding (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (r : AffineQuery G) : Fin (Fintype.card G/1000) × Fin 9 ↪ OddOrbit G :=
  (affinePacking hodd hn r).orbitEmbedding hodd

def affineDemand (r : AffineQuery G) (j : Fin 9) : Label :=
  EndpointReservoirAvailability.encodeChild (some (r.val.1 (part r.val.2.1 j),true))

theorem qLabel_weight (p τ : ℝ≥0) (t : Part) :
    labelWeights p τ (EndpointReservoirAvailability.encodeChild (some (t,true))) = τ := by
  fin_cases t <;> rfl

theorem affineDemand_probability (p τ : ℝ≥0) (r : AffineQuery G) :
    successProbability p τ (affineDemand r) = (τ : ℝ)^9 := by
  simp [successProbability,affineDemand,qLabel_weight]

def regularAffine (r : RegularQuery G) (σ : Equiv.Perm Part) : AffineQuery G :=
  ⟨(σ,r.val.1,r.val.2),r.property.2⟩

def exceptionalAffine (hodd : Odd (Fintype.card G)) (r : ExceptionalQuery G) : AffineQuery G :=
  ⟨(Equiv.refl Part,.first,dummyRoots r.val),dummyRoots_offsetDistinct hodd r.val r.property.1⟩

theorem affine_candidate_Q (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (r : AffineQuery G) (ω : EndpointFullProduct.FullSample G)
    (i : Fin (Fintype.card G/1000))
    (hs : ∀ j, EndpointFullProduct.fullLabels ω (affineEmbedding hodd hn r (i,j)) =
      affineDemand r j) :
    ∀ v ∈ rotate r.val.1 (augmentation r.val.2.1 r.val.2.2
      ((affinePacking hodd hn r).parameter i)), QVertex ω v := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨⟨j,b⟩,_,rfl⟩ := Finset.mem_image.mp hw
  have hc : childLabel ((EndpointFullProduct.regroup ω).1
      (affineEmbedding hodd hn r (i,j))) =
      some (r.val.1 (part r.val.2.1 j),true) := by
    apply EndpointReservoirAvailability.encodeChild_bijective.injective
    exact hs j
  have hsign : signedFlow r.val.2.1 r.val.2.2 ((affinePacking hodd hn r).parameter i) (j,b) =
      flow r.val.2.1 r.val.2.2 ((affinePacking hodd hn r).parameter i) j ∨
      signedFlow r.val.2.1 r.val.2.2 ((affinePacking hodd hn r).parameter i) (j,b) =
      -flow r.val.2.1 r.val.2.2 ((affinePacking hodd hn r).parameter i) j := by
    cases b <;> simp [signedFlow]
  obtain ⟨t,ht⟩ := (EndpointSelector.orbitPlace_actualOrbit_iff hodd _
    (((affinePacking hodd hn r).valid i).1 j) _).2 hsign
  exact ⟨affineEmbedding hodd hn r (i,j),t,ht,hc⟩

/-- A single common event precedes the root query and the numerical forbidden
set, which may both be chosen using the already sampled reservoirs. -/
theorem successful_affine_candidate
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hg : EndpointFullProduct.FullAvailable (affineEmbedding hodd hn)
      (fun r _ ↦ affineDemand r) budget ω)
    (r : AffineQuery G) (F : Finset G) (hF : F.card ≤ budget) :
    ∃ xy : G × G, Valid r.val.2.1 r.val.2.2 xy ∧
      Disjoint (orbitSupport r.val.2.1 r.val.2.2 xy) F ∧
      (∀ v ∈ rotate r.val.1 (augmentation r.val.2.1 r.val.2.2 xy), QVertex ω v) := by
  obtain ⟨i,hi,hd⟩ := hg r F hF
  refine ⟨(affinePacking hodd hn r).parameter i,(affinePacking hodd hn r).valid i,?_,
    affine_candidate_Q hodd hn r ω i (fun j ↦ congrFun hi j)⟩
  change Disjoint (support ((affinePacking hodd hn r).orbitEmbedding hodd) orbitPlace i) F at hd
  rw [(affinePacking hodd hn r).support_eq hodd i] at hd
  exact hd

end

end EndpointFlow
