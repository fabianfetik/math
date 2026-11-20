import CorralFormalization.EndpointProof.Selector.TwoPairSwitch
import CorralFormalization.EndpointProof.Probability.SelectorAvailability

/-!
# Concrete inverse-orbit packings for the shared availability theorem

The two-pair queries here supply their own deterministic candidates, their
own `Fin M × Fin 4` orbit embedding, and the exact B,B,C,C demand word.
The remaining probability inequalities are stated explicitly.
-/

open scoped Classical BigOperators NNReal

namespace EndpointSelector

set_option maxRecDepth 2048
set_option maxHeartbeats 1500000

open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

/-- The orbit of a concrete nonzero coordinate, using the concrete inverse-orbit type. -/
def locate (hodd : Odd (Fintype.card G)) (x : G) (hx : x ≠ 0) : OddOrbit G × Bool :=
  Classical.choose (orbitPlace_covers_nonzero hodd hx)

theorem locate_spec (hodd : Odd (Fintype.card G)) (x : G) (hx : x ≠ 0) :
    orbitPlace (locate hodd x hx) = x :=
  Classical.choose_spec (orbitPlace_covers_nonzero hodd hx)

def actualOrbit (hodd : Odd (Fintype.card G)) (x : G) (hx : x ≠ 0) : OddOrbit G :=
  (locate hodd x hx).1

theorem actualOrbit_signed (hodd : Odd (Fintype.card G)) (x : G) (hx : x ≠ 0) :
    x = (actualOrbit hodd x hx).val ∨ x = -(actualOrbit hodd x hx).val := by
  have h := locate_spec hodd x hx
  change (if (locate hodd x hx).2 then -(actualOrbit hodd x hx).val
    else (actualOrbit hodd x hx).val) = x at h
  cases ht : (locate hodd x hx).2 <;> simp only [ht, Bool.false_eq_true,
    ↓reduceIte] at h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem signed_of_actualOrbit_eq (hodd : Odd (Fintype.card G)) (x y : G)
    (hx : x ≠ 0) (hy : y ≠ 0) (h : actualOrbit hodd x hx = actualOrbit hodd y hy) :
    x = y ∨ x = -y := by
  have hxs := actualOrbit_signed hodd x hx
  have hys := actualOrbit_signed hodd y hy
  rw [h] at hxs
  rcases hxs with hxs | hxs
  · rcases hys with hys | hys
    · exact Or.inl (hxs.trans hys.symm)
    · right; rw [hys,neg_neg]; exact hxs
  · rcases hys with hys | hys
    · right; rw [hys]; exact hxs
    · exact Or.inl (hxs.trans hys.symm)

theorem orbitPlace_actualOrbit_iff (hodd : Odd (Fintype.card G))
    (x : G) (hx : x ≠ 0) (y : G) :
    (∃ t, orbitPlace (actualOrbit hodd x hx,t) = y) ↔ y = x ∨ y = -x := by
  have hp : orbitPlace (actualOrbit hodd x hx, (locate hodd x hx).2) = x :=
    locate_spec hodd x hx
  constructor
  · rintro ⟨t,ht⟩
    have hb : t = (locate hodd x hx).2 ∨ t = !(locate hodd x hx).2 := by
      cases t <;> cases (locate hodd x hx).2 <;> simp
    rcases hb with hb | hb
    · rw [hb,hp] at ht
      exact Or.inl ht.symm
    · rw [hb,orbitPlace_neg,hp] at ht
      exact Or.inr ht.symm
  · rintro (hy | hy)
    · exact ⟨(locate hodd x hx).2,hp.trans hy.symm⟩
    · refine ⟨!(locate hodd x hx).2,?_⟩
      rw [orbitPlace_neg,hp]
      exact hy.symm


/-- A deterministic packing of actual affine switches indexed by one fixed Fin M. -/
structure PackedSwitches (a b : G) (M : ℕ) where
  parameter : Fin M ↪ G
  valid : ∀ i, Valid a b (parameter i)
  disjoint : Pairwise fun i j ↦
    Disjoint (orbitSupport a b (parameter i)) (orbitSupport a b (parameter j))

theorem exists_packedSwitches (a b : G) (hr : RootCondition a b)
    (hodd : Odd (Fintype.card G)) (M : ℕ)
    (hsize : 17 + 64 * M < Fintype.card G) : Nonempty (PackedSwitches a b M) := by
  obtain ⟨U,hU,hvalid,hdisj⟩ := exists_disjoint_packing a b hr hodd M hsize
  let eqv : U ≃ Fin M := Fintype.equivFinOfCardEq (by simpa using hU)
  let f : Fin M ↪ G :=
    ⟨fun i ↦ (eqv.symm i).val, Subtype.val_injective.comp eqv.symm.injective⟩
  refine ⟨⟨f, fun i ↦ hvalid (f i) (eqv.symm i).property, ?_⟩⟩
  intro i j hij
  exact hdisj (eqv.symm i).property (eqv.symm j).property (fun h ↦ hij (f.injective h))

def PackedSwitches.orbitEmbedding {a b : G} {M : ℕ}
    (P : PackedSwitches a b M) (hodd : Odd (Fintype.card G)) :
    Fin M × Fin 4 ↪ OddOrbit G where
  toFun ij := actualOrbit hodd (representative a b (P.parameter ij.1) ij.2)
    ((P.valid ij.1).1 ij.2)
  inj' := by
    rintro ⟨i,j⟩ ⟨k,l⟩ he
    have hs := signed_of_actualOrbit_eq hodd
      (representative a b (P.parameter i) j) (representative a b (P.parameter k) l)
      ((P.valid i).1 j) ((P.valid k).1 l) he
    have hik : i = k := by
      by_contra hik
      have hd := P.disjoint hik
      have hj := representative_mem_support a b (P.parameter i) j
      have hl : representative a b (P.parameter i) j ∈ orbitSupport a b (P.parameter k) :=
        (mem_orbitSupport _ _ _ _).2 ⟨l,hs⟩
      exact Finset.disjoint_left.mp hd hj hl
    subst k
    have hjl : j = l := by
      by_contra hjl
      have hd := (P.valid i).2.1 j l hjl
      exact hs.elim hd.1 hd.2
    exact Prod.ext rfl hjl

/-- The availability module's numerical support is exactly the reserved inverse
closure, despite the arbitrary orientation of its canonical orbit representative. -/
theorem PackedSwitches.support_eq {a b : G} {M : ℕ}
    (P : PackedSwitches a b M) (hodd : Odd (Fintype.card G)) (i : Fin M) :
    support (P.orbitEmbedding hodd) orbitPlace i = orbitSupport a b (P.parameter i) := by
  ext x
  simp only [support, Finset.mem_image, Finset.mem_univ, true_and, mem_orbitSupport]
  constructor
  · rintro ⟨⟨j,t⟩,hx⟩
    exact ⟨j,(orbitPlace_actualOrbit_iff hodd
      (representative a b (P.parameter i) j) ((P.valid i).1 j) x).1 ⟨t,hx⟩⟩
  · rintro ⟨j,hx⟩
    obtain ⟨t,ht⟩ := (orbitPlace_actualOrbit_iff hodd
      (representative a b (P.parameter i) j) ((P.valid i).1 j) x).2 hx
    exact ⟨(j,t),ht⟩

/-- Every ordered pair of distinct nonzero inverse pairs is a root query. -/
abbrev RootQuery (G : Type*) [CommRing G] :=
  {ab : G × G // RootCondition ab.1 ab.2}

theorem rootQuery_card_le : Fintype.card (RootQuery G) ≤ (Fintype.card G)^2 := by
  simpa only [Fintype.card_prod, pow_two] using
    Fintype.card_le_of_injective (fun r : RootQuery G ↦ r.val) Subtype.val_injective

/-- This choice is a function of the finite group and root query alone. -/
def linearOrbitPacking (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (r : RootQuery G) : PackedSwitches r.val.1 r.val.2 (Fintype.card G / 1000) :=
  Classical.choice (exists_packedSwitches r.val.1 r.val.2 r.property hodd
    (Fintype.card G / 1000) (by omega))

def queryEmbedding (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (r : RootQuery G) : Fin (Fintype.card G / 1000) × Fin 4 ↪ OddOrbit G :=
  (linearOrbitPacking hodd hn r).orbitEmbedding hodd

/-- P_B,P_B,P_C,P_C: P labels are 0,1,2 and Q labels are 3,4,5.
An inverse orbit carries one label shared by both numerical signs. -/
def switchDemand : Fin 4 → Label := ![1,1,2,2]

def switchPart : Fin 4 → Part := ![1,1,2,2]

theorem switchDemand_encode (j : Fin 4) :
    EndpointReservoirAvailability.encodeChild (some (switchPart j,false)) = switchDemand j := by
  fin_cases j <;> rfl

omit [Fintype G] in
theorem interior_image (a b u : G) :
    interior a b u = Finset.univ.image (fun j : Fin 4 ↦
      (switchPart j,representative a b u j)) := by
  ext v
  simp [interior,switchPart,representative,Fin.exists_fin_succ]
  tauto

/-- Membership in the actual P child reservoir. The second argument is a
signed group coordinate, with A=-R1, B=R2 and C=-R3 as in the supplement. -/
def PVertex (ω : EndpointFullProduct.FullSample G) (v : Vertex G) : Prop :=
  ∃ (o : OddOrbit G) (side : Bool), orbitPlace (o,side) = v.2 ∧
    childLabel ((EndpointFullProduct.regroup ω).1 o) = some (v.1,false)

theorem pVertex_signedMinus (ω : EndpointFullProduct.FullSample G) (v : Vertex G)
    (hv : PVertex ω v) : EndpointFullProduct.signedMinus v.1 ω v.2 := by
  obtain ⟨o,side,hcoord,hchild⟩ := hv
  rw [← hcoord]
  exact EndpointFullProduct.child_signed_containment v.1 false side ω o hchild

theorem pVertex_originalSigned (ω : EndpointFullProduct.FullSample G) (v : Vertex G)
    (hv : PVertex ω v) :
    EndpointFullProduct.originalSigned v.1 (EndpointFullProduct.originalProcess ω) v.2 :=
  EndpointFullProduct.signedMinus_subset_originalSigned v.1 ω v.2
    (pVertex_signedMinus ω v hv)

/-- Every occupied interior vertex is in its demanded P_B or P_C reservoir.
Both signs of one canonical orbit have the identical P label. -/
theorem candidate_interior_P {a b : G} {M : ℕ}
    (P : PackedSwitches a b M) (hodd : Odd (Fintype.card G))
    (ω : EndpointFullProduct.FullSample G) (i : Fin M)
    (hsuccess : ∀ j, EndpointFullProduct.fullLabels ω (P.orbitEmbedding hodd (i,j)) =
      switchDemand j) :
    ∀ v ∈ interior a b (P.parameter i), PVertex ω v := by
  intro v hv
  rw [interior_image] at hv
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
  have hc : childLabel ((EndpointFullProduct.regroup ω).1 (P.orbitEmbedding hodd (i,j))) =
      some (switchPart j,false) := by
    apply EndpointReservoirAvailability.encodeChild_bijective.injective
    change EndpointFullProduct.fullLabels ω (P.orbitEmbedding hodd (i,j)) =
      EndpointReservoirAvailability.encodeChild (some (switchPart j,false))
    exact (hsuccess j).trans (switchDemand_encode j).symm
  exact ⟨P.orbitEmbedding hodd (i,j),
    (locate hodd (representative a b (P.parameter i) j) ((P.valid i).1 j)).2,
    locate_spec hodd (representative a b (P.parameter i) j) ((P.valid i).1 j),hc⟩

theorem switchDemand_probability (p τ : ℝ≥0) :
    successProbability p τ switchDemand = (p : ℝ)^4 := by
  simp [successProbability,switchDemand,labelWeights,Fin.prod_univ_succ]
  ring

theorem switchDemand_mean (p τ : ℝ≥0) (M : ℕ) :
    (∑ _i : Fin M, successProbability p τ switchDemand) = (M : ℝ) * (p : ℝ)^4 := by
  simp [switchDemand_probability]

/-- An application to the original G-indexed source law with concrete queries,
actual orbit embeddings, and the exactly computed four-label mean.
The sole extra analytic input is the displayed numerical budget separation. -/
theorem full_sample_switch_availability
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (q η α β : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α+β ≤ 1) (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*α) (hQ : (τ : ℝ) = rho q η*β)
    (budget : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hmean : (budget : ℝ) ≤
      ((Fintype.card G / 1000 : ℕ) : ℝ) * (p : ℝ)^4 - t) :
    (EndpointFullProduct.fullMeasure q η α β hq0 hq1 hη0 hη1 hα hβ hαβ).real
      {ω : EndpointFullProduct.FullSample G |
        ¬ EndpointFullProduct.FullAvailable (queryEmbedding hodd hn)
          (fun _ _ ↦ switchDemand) budget ω} ≤
      (Fintype.card (RootQuery G) : ℝ) *
        Real.exp (-t^2 / (2 * ((Fintype.card G / 1000 : ℕ) : ℝ) * (1/4))) := by
  have hh := EndpointFullProduct.full_sample_universal_availability hodd
    q η α β hq0 hq1 hη0 hη1 hα hβ hαβ p τ h hP hQ
    (queryEmbedding hodd hn) (fun _ _ ↦ switchDemand) budget t ht
    (fun r ↦ by simpa only [switchDemand_mean] using hmean)
  simpa only [Fintype.card_fin] using hh

/-- All legal switch queries and every later forbidden set, with paired cover construction's actual
primitive budget and a finite error bound. No packing, success-probability,
mean, or union-size hypothesis remains. -/
theorem full_sample_switch_budget
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η α β : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α+β ≤ 1) (p τ : ℝ≥0) (hp : 0 < (p : ℝ)) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*α) (hQ : (τ : ℝ) = rho q η*β) :
    (EndpointFullProduct.fullMeasure q η α β hq0 hq1 hη0 hη1 hα hβ hαβ).real
      {ω : EndpointFullProduct.FullSample G |
        ¬ EndpointFullProduct.FullAvailable (queryEmbedding hodd (by omega))
          (fun _ _ ↦ switchDemand)
          (CorralFormalization.EndpointProof.RateBudget.selectorBudget p (Fintype.card G)) ω} ≤
      ((Fintype.card G : ℝ)^2) *
        Real.exp (-((p : ℝ)^8 / 32000) * (Fintype.card G : ℝ)) := by
  have hh := EndpointFullProduct.full_sample_four_orbit_budget hodd hn
    q η α β hq0 hq1 hη0 hη1 hα hβ hαβ p τ hp h hP hQ
    (queryEmbedding hodd (by omega)) (fun _ _ ↦ switchDemand)
    (by simp) (fun _ _ ↦ (switchDemand_probability p τ).ge)
  have hqcard : (Fintype.card (RootQuery G) : ℝ) ≤ (Fintype.card G : ℝ)^2 := by
    exact_mod_cast (rootQuery_card_le (G := G))
  exact hh.trans (mul_le_mul_of_nonneg_right hqcard (le_of_lt (Real.exp_pos _)))

/-- The same concrete switch event under the original categorical vertex and
independent colour process, after one existentially chosen augmentation. -/
theorem original_sample_switch_budget
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η α β : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α+β ≤ 1) (p τ : ℝ≥0) (hp : 0 < (p : ℝ)) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*α) (hQ : (τ : ℝ) = rho q η*β) :
    (EndpointFullProduct.originalMeasure q hq0 hq1).real
      {s : EndpointFullProduct.OriginalSample G |
        ¬ EndpointFullProduct.OriginalAdmitsAvailable (queryEmbedding hodd (by omega))
          (fun _ _ ↦ switchDemand)
          (CorralFormalization.EndpointProof.RateBudget.selectorBudget p (Fintype.card G)) s} ≤
      ((Fintype.card G : ℝ)^2) *
        Real.exp (-((p : ℝ)^8 / 32000) * (Fintype.card G : ℝ)) := by
  have hh := EndpointFullProduct.original_sample_four_orbit_budget hodd hn
    q η α β hq0 hq1 hη0 hη1 hα hβ hαβ p τ hp h hP hQ
    (queryEmbedding hodd (by omega)) (fun _ _ ↦ switchDemand)
    (by simp) (fun _ _ ↦ (switchDemand_probability p τ).ge)
  have hqcard : (Fintype.card (RootQuery G) : ℝ) ≤ (Fintype.card G : ℝ)^2 := by
    exact_mod_cast (rootQuery_card_le (G := G))
  exact hh.trans (mul_le_mul_of_nonneg_right hqcard (le_of_lt (Real.exp_pos _)))


/-- Unpack a successful query into its actual coordinate u and the exact two
alternative matchings. The forbidden set may have been chosen after the sample. -/
theorem successful_switch_of_fullAvailable
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : EndpointFullProduct.FullAvailable (queryEmbedding hodd hn)
      (fun _ _ ↦ switchDemand) budget ω)
    (r : RootQuery G) (F : Finset G) (hF : F.card ≤ budget) :
    ∃ i : Fin (Fintype.card G / 1000),
      let u := (linearOrbitPacking hodd hn r).parameter i
      Valid r.val.1 r.val.2 u ∧
      (∀ j, EndpointFullProduct.fullLabels ω (queryEmbedding hodd hn r (i,j)) =
        switchDemand j) ∧
      Disjoint (orbitSupport r.val.1 r.val.2 u) F ∧
      IsTwoEdgeMatchingOn (leftState r.val.1 r.val.2 u)
        (interior r.val.1 r.val.2 u ∪ target r.val.1) ∧
      IsTwoEdgeMatchingOn (rightState r.val.1 r.val.2 u)
        (interior r.val.1 r.val.2 u ∪ target r.val.2) := by
  obtain ⟨i,hi,hd⟩ := hgood r F hF
  have hv := (linearOrbitPacking hodd hn r).valid i
  have hm := two_pair_switch r.val.1 r.val.2 ((linearOrbitPacking hodd hn r).parameter i)
    r.property hodd hv
  refine ⟨i,hv,fun j ↦ congrFun hi j,?_,hm.2.2.2⟩
  change Disjoint (support ((linearOrbitPacking hodd hn r).orbitEmbedding hodd) orbitPlace i) F at hd
  rw [(linearOrbitPacking hodd hn r).support_eq hodd i] at hd
  exact hd

/-- The resulting selector lives in actual P reservoirs and hence in the
original signed vertex/colour sets, and covers exactly either A root pair. -/
theorem successful_switch_in_original_model
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : EndpointFullProduct.FullAvailable (queryEmbedding hodd hn)
      (fun _ _ ↦ switchDemand) budget ω)
    (r : RootQuery G) (F : Finset G) (hF : F.card ≤ budget) :
    ∃ u : G, Valid r.val.1 r.val.2 u ∧
      Disjoint (orbitSupport r.val.1 r.val.2 u) F ∧
      (∀ v ∈ interior r.val.1 r.val.2 u, PVertex ω v ∧
        EndpointFullProduct.originalSigned v.1 (EndpointFullProduct.originalProcess ω) v.2) ∧
      IsTwoEdgeMatchingOn (leftState r.val.1 r.val.2 u)
        (interior r.val.1 r.val.2 u ∪ target r.val.1) ∧
      IsTwoEdgeMatchingOn (rightState r.val.1 r.val.2 u)
        (interior r.val.1 r.val.2 u ∪ target r.val.2) := by
  obtain ⟨i,hv,hs,hd,hl,hr⟩ :=
    successful_switch_of_fullAvailable hodd hn budget ω hgood r F hF
  have hp := candidate_interior_P (linearOrbitPacking hodd hn r) hodd ω i hs
  refine ⟨(linearOrbitPacking hodd hn r).parameter i,hv,hd,?_,hl,hr⟩
  intro v hv
  exact ⟨hp v hv,pVertex_originalSigned ω v (hp v hv)⟩

end

end EndpointSelector
