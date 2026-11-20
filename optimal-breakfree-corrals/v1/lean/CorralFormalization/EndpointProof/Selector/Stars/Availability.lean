import CorralFormalization.EndpointProof.Selector.Stars.Packing
import CorralFormalization.EndpointProof.Selector.SwitchAvailability

/-!
# Actual P-reservoir availability for the coloured selector construction stars

These are new star queries, with B,C,...,C demand, on the maintained orbit
sample.  The theorem does not infer this event from the distinct B,B,C,C
switch event.  Both events may be joined before projecting to the original
sample; the augmentation in their separate projections must not be conflated.
-/

open scoped Classical BigOperators NNReal

namespace EndpointSelector.Stars

open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open CorralFormalization.EndpointProof.RateBudget

set_option maxHeartbeats 1500000
set_option maxRecDepth 2048

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G] {k : ℕ}

structure PackedStars (a : Fin k → G) (M : ℕ) where
  parameter : Fin M ↪ G
  valid : ∀ i, StarValid a (parameter i)
  disjoint : Pairwise fun i j ↦ Disjoint (starSupport a (parameter i)) (starSupport a (parameter j))

theorem exists_packedStars (a : Fin k → G) (hr : StarRoots a) (hk : k ≤ 3)
    (hodd : Odd (Fintype.card G)) (M : ℕ) (hsize : 40+64*M < Fintype.card G) :
    Nonempty (PackedStars a M) := by
  obtain ⟨U,hU,hvalid,hdisj⟩ := exists_star_disjoint_packing a hr hk hodd M hsize
  let eqv : U ≃ Fin M := Fintype.equivFinOfCardEq (by simpa using hU)
  let f : Fin M ↪ G :=
    ⟨fun i ↦ (eqv.symm i).val,Subtype.val_injective.comp eqv.symm.injective⟩
  refine ⟨⟨f,fun i ↦ hvalid (f i) (eqv.symm i).property,?_⟩⟩
  intro i j hij
  exact hdisj (eqv.symm i).property (eqv.symm j).property (fun h ↦ hij (f.injective h))

def PackedStars.orbitEmbedding {a : Fin k → G} {M : ℕ}
    (P : PackedStars a M) (hodd : Odd (Fintype.card G)) :
    Fin M × Option (Fin k) ↪ OddOrbit G where
  toFun ij := actualOrbit hodd (starRepresentative a (P.parameter ij.1) ij.2)
    ((P.valid ij.1).1 ij.2)
  inj' := by
    rintro ⟨i,j⟩ ⟨l,m⟩ he
    have hs := signed_of_actualOrbit_eq hodd
      (starRepresentative a (P.parameter i) j) (starRepresentative a (P.parameter l) m)
      ((P.valid i).1 j) ((P.valid l).1 m) he
    have hil : i = l := by
      by_contra hil
      have hd := P.disjoint hil
      have hj := starRepresentative_mem_support a (P.parameter i) j
      have hm : starRepresentative a (P.parameter i) j ∈ starSupport a (P.parameter l) :=
        (mem_starSupport _ _ _).2 ⟨m,hs⟩
      exact Finset.disjoint_left.mp hd hj hm
    subst l
    have hjm : j = m := by
      by_contra hjm
      have hd := (P.valid i).2.1 j m hjm
      exact hs.elim hd.1 hd.2
    exact Prod.ext rfl hjm

theorem PackedStars.support_eq {a : Fin k → G} {M : ℕ}
    (P : PackedStars a M) (hodd : Odd (Fintype.card G)) (i : Fin M) :
    support (P.orbitEmbedding hodd) orbitPlace i = starSupport a (P.parameter i) := by
  ext x
  simp only [support,Finset.mem_image,Finset.mem_univ,true_and,mem_starSupport]
  constructor
  · rintro ⟨⟨j,t⟩,hx⟩
    exact ⟨j,(orbitPlace_actualOrbit_iff hodd
      (starRepresentative a (P.parameter i) j) ((P.valid i).1 j) x).1 ⟨t,hx⟩⟩
  · rintro ⟨j,hx⟩
    obtain ⟨t,ht⟩ := (orbitPlace_actualOrbit_iff hodd
      (starRepresentative a (P.parameter i) j) ((P.valid i).1 j) x).2 hx
    exact ⟨(j,t),ht⟩

abbrev StarQuery (G : Type*) [CommRing G] (k : ℕ) :=
  {a : Fin k → G // StarRoots a}

theorem starQuery_card_le : Fintype.card (StarQuery G k) ≤ (Fintype.card G)^k := by
  simpa only [Fintype.card_fun,Fintype.card_fin] using
    Fintype.card_le_of_injective (fun r : StarQuery G k ↦ r.val) Subtype.val_injective

def starOrbitPacking (hk : k ≤ 3) (hodd : Odd (Fintype.card G))
    (hn : 1000 ≤ Fintype.card G) (r : StarQuery G k) :
    PackedStars r.val (Fintype.card G/1000) :=
  Classical.choice (exists_packedStars r.val r.property hk hodd (Fintype.card G/1000) (by omega))

def starQueryEmbedding (hk : k ≤ 3) (hodd : Odd (Fintype.card G))
    (hn : 1000 ≤ Fintype.card G) (r : StarQuery G k) :
    Fin (Fintype.card G/1000) × Option (Fin k) ↪ OddOrbit G :=
  (starOrbitPacking hk hodd hn r).orbitEmbedding hodd

def starPart : Option (Fin k) → Part
  | none => 1
  | some _ => 2

def starDemand : Option (Fin k) → Label
  | none => 1
  | some _ => 2

theorem starDemand_encode (j : Option (Fin k)) :
    EndpointReservoirAvailability.encodeChild (some (starPart j,false)) = starDemand j := by
  cases j <;> rfl

theorem starDemand_probability (p τ : ℝ≥0) :
    successProbability p τ (starDemand (k := k)) = (p : ℝ)^(k+1) := by
  simp [successProbability,Fintype.prod_option,starDemand,labelWeights,pow_succ,mul_comm]

theorem starDemand_probability_ge_four (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (hk : k ≤ 3) :
    (p : ℝ)^4 ≤ successProbability p τ (starDemand (k := k)) := by
  rw [starDemand_probability]
  have hp1 : (p : ℝ) ≤ 1 := by
    have hreal : 3*(p : ℝ)+3*(τ : ℝ) ≤ 1 := by exact_mod_cast h
    have hτ := τ.coe_nonneg
    linarith
  exact pow_le_pow_of_le_one p.coe_nonneg hp1 (by omega)

/-- The rotated demand is relabelled in the *actual* categorical P parts. -/
def rotatedStarDemand (σ : Equiv.Perm Part) (j : Option (Fin k)) : Label :=
  EndpointReservoirAvailability.encodeChild (some (σ (starPart j),false))

theorem labelWeights_encode_P (p τ : ℝ≥0) (c : Part) :
    labelWeights p τ (EndpointReservoirAvailability.encodeChild (some (c,false))) = p := by
  fin_cases c <;> rfl

theorem rotatedStarDemand_probability (p τ : ℝ≥0) (σ : Equiv.Perm Part) :
    successProbability p τ (rotatedStarDemand (k := k) σ) = (p : ℝ)^(k+1) := by
  simp [successProbability,rotatedStarDemand,labelWeights_encode_P]

theorem rotatedStarDemand_probability_ge_four (p τ : ℝ≥0)
    (h : 3*p+3*τ ≤ 1) (hk : k ≤ 3) (σ : Equiv.Perm Part) :
    (p : ℝ)^4 ≤ successProbability p τ (rotatedStarDemand (k := k) σ) := by
  simpa only [rotatedStarDemand_probability,starDemand_probability] using
    (starDemand_probability_ge_four (k := k) p τ h hk)

omit [Fintype G] in
theorem starInterior_taggedCoordinates (a : Fin k → G) (u : G) {v : Vertex G}
    (hv : v ∈ starInterior a u) :
    ∃ j : Option (Fin k), ∃ b : Bool, v = (starPart j,starSignedRepresentative a u (j,b)) := by
  simp only [starInterior,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and,
    starCommonPair,starPair,Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with hv | ⟨i,hv⟩
  · rcases hv with rfl | rfl
    · exact ⟨none,false,rfl⟩
    · exact ⟨none,true,rfl⟩
  · rcases hv with rfl | rfl
    · exact ⟨some i,false,rfl⟩
    · exact ⟨some i,true,by simp [starPart,starSignedRepresentative,starRepresentative,add_comm]⟩

/-- Both signs in every occupied B/C pair lie in the actual P child reservoir. -/
theorem candidate_starInterior_P {a : Fin k → G} {M : ℕ}
    (P : PackedStars a M) (hodd : Odd (Fintype.card G))
    (ω : EndpointFullProduct.FullSample G) (i : Fin M)
    (hsuccess : ∀ j, EndpointFullProduct.fullLabels ω (P.orbitEmbedding hodd (i,j)) = starDemand j) :
    ∀ v ∈ starInterior a (P.parameter i), PVertex ω v := by
  intro v hv
  obtain ⟨j,b,rfl⟩ := starInterior_taggedCoordinates a (P.parameter i) hv
  have hc : childLabel ((EndpointFullProduct.regroup ω).1 (P.orbitEmbedding hodd (i,j))) =
      some (starPart j,false) := by
    apply EndpointReservoirAvailability.encodeChild_bijective.injective
    change EndpointFullProduct.fullLabels ω (P.orbitEmbedding hodd (i,j)) =
      EndpointReservoirAvailability.encodeChild (some (starPart j,false))
    exact (hsuccess j).trans (starDemand_encode j).symm
  have hs : starSignedRepresentative a (P.parameter i) (j,b) =
        starRepresentative a (P.parameter i) j ∨
      starSignedRepresentative a (P.parameter i) (j,b) =
        -starRepresentative a (P.parameter i) j := by
    cases b <;> simp [starSignedRepresentative]
  obtain ⟨t,ht⟩ := (orbitPlace_actualOrbit_iff hodd
    (starRepresentative a (P.parameter i) j) ((P.valid i).1 j)
    (starSignedRepresentative a (P.parameter i) (j,b))).2 hs
  exact ⟨P.orbitEmbedding hodd (i,j),t,ht,hc⟩

/-- A genuine P witness after tag rotation, paid by the rotated demand word. -/
theorem candidate_rotated_starInterior_P {a : Fin k → G} {M : ℕ}
    (P : PackedStars a M) (hodd : Odd (Fintype.card G)) (σ : Equiv.Perm Part)
    (ω : EndpointFullProduct.FullSample G) (i : Fin M)
    (hsuccess : ∀ j, EndpointFullProduct.fullLabels ω (P.orbitEmbedding hodd (i,j)) =
      rotatedStarDemand σ j) :
    ∀ v ∈ starInterior a (P.parameter i), PVertex ω (σ v.1,v.2) := by
  intro v hv
  obtain ⟨j,b,rfl⟩ := starInterior_taggedCoordinates a (P.parameter i) hv
  have hc : childLabel ((EndpointFullProduct.regroup ω).1 (P.orbitEmbedding hodd (i,j))) =
      some (σ (starPart j),false) := by
    apply EndpointReservoirAvailability.encodeChild_bijective.injective
    exact hsuccess j
  have hs : starSignedRepresentative a (P.parameter i) (j,b) =
        starRepresentative a (P.parameter i) j ∨
      starSignedRepresentative a (P.parameter i) (j,b) =
        -starRepresentative a (P.parameter i) j := by
    cases b <;> simp [starSignedRepresentative]
  obtain ⟨t,ht⟩ := (orbitPlace_actualOrbit_iff hodd
    (starRepresentative a (P.parameter i) j) ((P.valid i).1 j)
    (starSignedRepresentative a (P.parameter i) (j,b))).2 hs
  exact ⟨P.orbitEmbedding hodd (i,j),t,ht,hc⟩

/-- All six tag permutations are a fixed finite query family, before sampling. -/
abbrev RotatedStarQuery (G : Type*) [CommRing G] (k : ℕ) :=
  Equiv.Perm Part × StarQuery G k

def rotatedStarQueryEmbedding (hk : k ≤ 3) (hodd : Odd (Fintype.card G))
    (hn : 1000 ≤ Fintype.card G) (r : RotatedStarQuery G k) :
    Fin (Fintype.card G/1000) × Option (Fin k) ↪ OddOrbit G :=
  starQueryEmbedding hk hodd hn r.2

theorem rotatedStarQuery_card_le :
    Fintype.card (RotatedStarQuery G k) ≤ 6*(Fintype.card G)^k := by
  have hp : Fintype.card (Equiv.Perm Part) = 6 := by
    norm_num [Fintype.card_perm,EndpointOriginalReservoir.Part]
  simpa only [Fintype.card_prod,hp] using
    Nat.mul_le_mul_left 6 (starQuery_card_le (G := G) (k := k))

/-- Explicit new B,C,...,C primitive event, with all later numerical exclusions. -/
theorem full_sample_star_budget (hk : k ≤ 3)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η α β : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α+β ≤ 1) (p τ : ℝ≥0) (hp : 0 < (p : ℝ)) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*α) (hQ : (τ : ℝ) = rho q η*β) :
    (EndpointFullProduct.fullMeasure q η α β hq0 hq1 hη0 hη1 hα hβ hαβ).real
      {ω : EndpointFullProduct.FullSample G |
        ¬ EndpointFullProduct.FullAvailable (starQueryEmbedding hk hodd (by omega))
          (fun _ _ ↦ starDemand) (selectorBudget p (Fintype.card G)) ω} ≤
      (Fintype.card G : ℝ)^k *
        Real.exp (-((p : ℝ)^8/32000)*(Fintype.card G : ℝ)) := by
  have hh := EndpointFullProduct.full_sample_four_orbit_budget hodd hn
    q η α β hq0 hq1 hη0 hη1 hα hβ hαβ p τ hp h hP hQ
    (starQueryEmbedding hk hodd (by omega)) (fun _ _ ↦ starDemand)
    (by simp) (fun _ _ ↦ starDemand_probability_ge_four p τ h hk)
  have hc : (Fintype.card (StarQuery G k) : ℝ) ≤ (Fintype.card G : ℝ)^k := by
    exact_mod_cast (starQuery_card_le (G := G) (k := k))
  exact hh.trans (mul_le_mul_of_nonneg_right hc (le_of_lt (Real.exp_pos _)))

/-- The same actual candidate packings support every part rotation simultaneously.
The factor six is the proved query count for all permutations, not a new sample. -/
theorem full_sample_rotated_star_budget (hk : k ≤ 3)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η α β : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α+β ≤ 1) (p τ : ℝ≥0) (hp : 0 < (p : ℝ)) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*α) (hQ : (τ : ℝ) = rho q η*β) :
    (EndpointFullProduct.fullMeasure q η α β hq0 hq1 hη0 hη1 hα hβ hαβ).real
      {ω : EndpointFullProduct.FullSample G |
        ¬ EndpointFullProduct.FullAvailable (rotatedStarQueryEmbedding hk hodd (by omega))
          (fun r _ ↦ rotatedStarDemand r.1) (selectorBudget p (Fintype.card G)) ω} ≤
      6*(Fintype.card G : ℝ)^k *
        Real.exp (-((p : ℝ)^8/32000)*(Fintype.card G : ℝ)) := by
  have hh := EndpointFullProduct.full_sample_four_orbit_budget hodd hn
    q η α β hq0 hq1 hη0 hη1 hα hβ hαβ p τ hp h hP hQ
    (rotatedStarQueryEmbedding hk hodd (by omega)) (fun r _ ↦ rotatedStarDemand r.1)
    (by simp) (fun r _ ↦ rotatedStarDemand_probability_ge_four p τ h hk r.1)
  have hc : (Fintype.card (RotatedStarQuery G k) : ℝ) ≤ 6*(Fintype.card G : ℝ)^k := by
    exact_mod_cast (rotatedStarQuery_card_le (G := G) (k := k))
  exact hh.trans (mul_le_mul_of_nonneg_right hc (le_of_lt (Real.exp_pos _)))

/-- Unpack the concrete event into an actual star and all its genuine states. -/
theorem successful_star_of_fullAvailable (hk : k ≤ 3)
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : EndpointFullProduct.FullAvailable (starQueryEmbedding hk hodd hn)
      (fun _ _ ↦ starDemand) budget ω)
    (r : StarQuery G k) (F : Finset G) (hF : F.card ≤ budget) :
    ∃ u : G, StarValid r.val u ∧ Disjoint (starSupport r.val u) F ∧
      (∀ v ∈ starInterior r.val u, PVertex ω v ∧
        EndpointFullProduct.originalSigned v.1 (EndpointFullProduct.originalProcess ω) v.2) ∧
      (starInterior r.val u).card ≤ 2+2*k ∧
      ∀ i, IsTwoEdgeMatchingOn (starState r.val u i)
        ((starCommonPair u ∪ starPair r.val u i) ∪ target (r.val i)) := by
  obtain ⟨i,hi,hd⟩ := hgood r F hF
  let P := starOrbitPacking hk hodd hn r
  have hv := P.valid i
  have hP := candidate_starInterior_P P hodd ω i (fun j ↦ congrFun hi j)
  change Disjoint (support (P.orbitEmbedding hodd) orbitPlace i) F at hd
  rw [P.support_eq hodd i] at hd
  refine ⟨P.parameter i,hv,hd,?_,starInterior_card_le _ _,?_⟩
  · intro v hv
    exact ⟨hP v hv,pVertex_originalSigned ω v (hP v hv)⟩
  · exact star_state_matching hodd r.val r.property _ hv

/-- An actual star for every later legal root list, tag permutation and numerical
forbidden set, inside one full sample carrying the simultaneous rotated event. -/
theorem successful_rotated_star_of_fullAvailable (hk : k ≤ 3)
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : EndpointFullProduct.FullAvailable (rotatedStarQueryEmbedding hk hodd hn)
      (fun r _ ↦ rotatedStarDemand r.1) budget ω)
    (r : StarQuery G k) (σ : Equiv.Perm Part) (F : Finset G) (hF : F.card ≤ budget) :
    ∃ u : G, StarValid r.val u ∧ Disjoint (starSupport r.val u) F ∧
      (∀ v ∈ starInterior r.val u, PVertex ω (σ v.1,v.2) ∧
        EndpointFullProduct.originalSigned (σ v.1) (EndpointFullProduct.originalProcess ω) v.2) ∧
      (starInterior r.val u).card ≤ 2+2*k ∧
      ∀ i, IsTwoEdgeMatchingOn (starState r.val u i)
        ((starCommonPair u ∪ starPair r.val u i) ∪ target (r.val i)) := by
  obtain ⟨i,hi,hd⟩ := hgood (σ,r) F hF
  let P := starOrbitPacking hk hodd hn r
  have hv := P.valid i
  have hP := candidate_rotated_starInterior_P P hodd σ ω i (fun j ↦ congrFun hi j)
  change Disjoint (support (P.orbitEmbedding hodd) orbitPlace i) F at hd
  rw [P.support_eq hodd i] at hd
  refine ⟨P.parameter i,hv,hd,?_,starInterior_card_le _ _,?_⟩
  · intro v hv
    exact ⟨hP v hv,pVertex_originalSigned ω (σ v.1,v.2) (hP v hv)⟩
  · exact star_state_matching hodd r.val r.property _ hv

end
end EndpointSelector.Stars
