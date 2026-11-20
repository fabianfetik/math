import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.Candidates

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
namespace EndpointMatching.UniversalCore.Buffer
open EndpointFlow.AbelianTransport
open EndpointFullProduct EndpointOriginalReservoir
open EndpointBlockAvailability EndpointSharedSample EndpointReservoirAvailability
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

def recoverAscending (i j : Fin 3) (g h : G) : Parameters G :=
  match i.val, j.val with
  | 0,1 => (g,h)
  | 0,2 => (g,-g-h)
  | 1,2 => (-g-h,g)
  | _,_ => (0,0)

def recoverCoordinates (i j : Fin 3) (g h : G) : Parameters G :=
  if i.val < j.val then recoverAscending i j g h else recoverAscending j i h g

omit [Fintype G] in
theorem recoverCoordinates_correct (i j : Fin 3) (hij : i ≠ j) (t : Parameters G) :
    recoverCoordinates i j (coordinate t i) (coordinate t j) = t := by
  rcases t with ⟨u,v⟩
  fin_cases i <;> fin_cases j <;>
    simp_all [recoverCoordinates, recoverAscending, coordinate]
  all_goals abel

/-- Two distinct fixed coordinates determine the buffer parameter pair. -/
theorem twoCoordinates_section_card_le (i j : Fin 3) (hij : i ≠ j) (g h : G) :
    ((Finset.univ : Finset (Parameters G)).filter
      (fun t => coordinate t i = g ∧ coordinate t j = h)).card ≤ 1 := by
  let C : Finset (Parameters G) := Finset.univ.filter
    (fun t => coordinate t i = g ∧ coordinate t j = h)
  have hinj : Set.InjOn (fun _ : Parameters G => ()) (C : Set (Parameters G)) := by
    intro t ht u hu _
    have ht' := (Finset.mem_filter.mp ht).2
    have hu' := (Finset.mem_filter.mp hu).2
    calc
      t = recoverCoordinates i j (coordinate t i) (coordinate t j) :=
        (recoverCoordinates_correct i j hij t).symm
      _ = recoverCoordinates i j (coordinate u i) (coordinate u j) := by
        rw [ht'.1,ht'.2,hu'.1,hu'.2]
      _ = u := recoverCoordinates_correct i j hij u
  have hc := Finset.card_le_card_of_injOn (s := C) (t := (Finset.univ : Finset Unit))
    (fun _ : Parameters G => ()) (by intro t ht; simp) hinj
  simpa [C] using hc

def activeParts (i : Fin 3) : Finset (Fin 3) := Finset.univ.erase i

theorem activeParts_card (i : Fin 3) : (activeParts i).card = 2 := by
  fin_cases i <;> decide

abbrev ActivePart (i : Fin 3) := {j : Fin 3 // j ∈ activeParts i}

theorem activePart_card (i : Fin 3) : Fintype.card (ActivePart i) = 2 := by
  simp [ActivePart, activeParts_card]

def activeOrbitEmbedding (hodd : Odd (Fintype.card G)) (t : Parameters G)
    (hv : GeometricallyValid t) (i : Fin 3) : Unit × ActivePart i ↪ OddOrbit G where
  toFun := fun k => (orbitPoint hodd t hv k.2.1).1
  inj' := by
    intro x y he
    have hxy := orbitPoint_injective hodd t hv he
    cases x with | mk x xj =>
      cases y with | mk y yj =>
        cases x; cases y
        have : xj = yj := Subtype.ext hxy
        subst yj
        rfl

def activeDemand (i : Fin 3) (_ : Unit) (j : ActivePart i) : Label := demand () j.1

theorem demand_weight (p τ : ℝ≥0) (i : Fin 3) :
    (labelWeights p τ (demand () i) : ℝ) = τ := by
  fin_cases i <;> simp [demand,encodeChild,labelWeights]

theorem activeDemand_probability (p τ : ℝ≥0) (i : Fin 3) :
    successProbability p τ (activeDemand i ()) = (τ : ℝ)^2 := by
  simp only [successProbability, activeDemand, demand_weight]
  simp [activeParts_card]

theorem two_labels_probability (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (i : Fin 3) :
    (sampleMeasure (I := Unit) (J := ActivePart i) p τ h).real
      {w | w () = activeDemand i ()} = (τ : ℝ)^2 := by
  have hI := integral_successIndicator (I := Unit) (J := ActivePart i) p τ h (activeDemand i) ()
  have hfun : successIndicator (activeDemand i) () =
      Set.indicator {w : Unit → ActivePart i → Label | w () = activeDemand i ()} 1 := by
    funext w
    simp [successIndicator, Set.indicator_apply]
  rw [hfun, integral_indicator_one (by measurability)] at hI
  exact hI.trans (activeDemand_probability p τ i)

/-- The two nonconstant Q requirements of a valid section candidate have
probability τ² in the actual shared sample. -/
theorem validActiveLabels_probability (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (t : Parameters G) (hv : GeometricallyValid t) (i : Fin 3) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ∀ j ∈ activeParts i, ReservoirVertex ω true (j,coordinate t j)} = (τ : ℝ)^2 := by
  let e := activeOrbitEmbedding hodd t hv i
  let ev : Set (Unit → ActivePart i → Label) := {w | w () = activeDemand i ()}
  have hevent : {ω : FullSample G | ∀ j ∈ activeParts i,
      ReservoirVertex ω true (j,coordinate t j)} = (fun ω => project e (fullLabels ω)) ⁻¹' ev := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · intro hlabels
      funext j
      change fullLabels ω ((orbitPoint hodd t hv j.1).1) = demand () j.1
      exact (coordinate_Q_iff_encoded hodd t hv ω j.1).mp (hlabels j.1 j.2)
    · intro hlabels j hj
      apply (coordinate_Q_iff_encoded hodd t hv ω j).mpr
      have hj' := congrFun hlabels ⟨j,hj⟩
      change fullLabels ω ((orbitPoint hodd t hv j).1) = demand () j at hj'
      exact hj'
  have hp := (project_measurePreserving (I := Unit) (J := ActivePart i) p τ h e).comp
    (fullLabels_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ)
  rw [hevent]
  change (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
    ((project e ∘ fullLabels) ⁻¹' ev) = (τ : ℝ)^2
  rw [hp.measureReal_preimage (by measurability)]
  exact two_labels_probability p τ h i

def sectionParameters (i : Fin 3) (g : G) : Finset (Parameters G) :=
  validParameters.filter (fun t => coordinate t i = g)

def activeLabels (Q : Vertex G → Prop) (t : Parameters G) (i : Fin 3) : Prop :=
  ∀ j ∈ activeParts i, Q (j,coordinate t j)

/-- In the fixed-coordinate section omit only the constant label, while
retaining the full geometric validity and the other two Q labels. -/
def sectionMajorant (Q : Vertex G → Prop) (i : Fin 3) (g : G) :
    Finset (Parameters G) :=
  (sectionParameters i g).filter (fun t => activeLabels Q t i)

theorem goodSection_subset_majorant (Q : Vertex G → Prop) (i : Fin 3) (g : G) :
    (goodCandidates Q).filter (fun t => coordinate t i = g) ⊆ sectionMajorant Q i g := by
  intro t ht
  obtain ⟨ht,hcoord⟩ := Finset.mem_filter.mp ht
  obtain ⟨hvalid,hlabels⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hvalid,hcoord⟩,
    fun j _ => hlabels j⟩

theorem sectionParameters_card_le (i : Fin 3) (g : G) :
    (sectionParameters i g : Finset (Parameters G)).card ≤ Fintype.card G := by
  have hsub : (sectionParameters i g : Finset (Parameters G)) ⊆
      (Finset.univ : Finset (Parameters G)).filter (fun t => coordinate t i = g) := by
    intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ht).2⟩
  exact (Finset.card_le_card hsub).trans (coordinate_fiber_card_le i g)

def activeIndicator (t : Parameters G) (i : Fin 3) (ω : FullSample G) : ℝ :=
  if activeLabels (ReservoirVertex ω true) t i then 1 else 0

theorem sectionMajorant_card_sum (i : Fin 3) (g : G) (ω : FullSample G) :
    ((sectionMajorant (ReservoirVertex ω true) i g).card : ℝ) =
      ∑ t ∈ (sectionParameters i g : Finset (Parameters G)), activeIndicator t i ω := by
  exact (Finset.sum_boole (R := ℝ)
    (fun t => activeLabels (ReservoirVertex ω true) t i) (sectionParameters i g)).symm

/-- The exact mean of the two-label section majorant. -/
theorem sectionMajorant_expectation (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (i : Fin 3) (g : G) :
    (∫ ω : FullSample G, ((sectionMajorant (ReservoirVertex ω true) i g).card : ℝ)
      ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)) =
      ((sectionParameters i g : Finset (Parameters G)).card : ℝ) * (τ : ℝ)^2 := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  have hfun (t : Parameters G) : activeIndicator t i =
      Set.indicator {ω : FullSample G | activeLabels (ReservoirVertex ω true) t i} 1 := by
    funext ω
    simp [activeIndicator, Set.indicator_apply]
  have hint (t : Parameters G) : Integrable (activeIndicator t i) μ := by
    rw [hfun]
    exact (integrable_const 1).indicator (by measurability)
  calc
    _ = ∫ ω : FullSample G, ∑ t ∈ (sectionParameters i g : Finset (Parameters G)),
        activeIndicator t i ω ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ (sectionMajorant_card_sum i g)
    _ = ∑ t ∈ (sectionParameters i g : Finset (Parameters G)),
        ∫ ω, activeIndicator t i ω ∂μ :=
      integral_finsetSum _ (fun t _ => hint t)
    _ = ∑ _t ∈ (sectionParameters i g : Finset (Parameters G)), (τ : ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro t ht
      have hv : GeometricallyValid t := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
      rw [hfun, integral_indicator_one (by measurability)]
      exact validActiveLabels_probability hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ t hv i
    _ = _ := by simp

theorem sectionMajorant_expectation_le (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (i : Fin 3) (g : G) :
    (∫ ω : FullSample G, ((sectionMajorant (ReservoirVertex ω true) i g).card : ℝ)
      ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)) ≤
      (τ : ℝ)^2 * (Fintype.card G : ℝ) := by
  rw [sectionMajorant_expectation hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ]
  have hc : ((sectionParameters i g : Finset (Parameters G)).card : ℝ) ≤ Fintype.card G := by
    exact_mod_cast sectionParameters_card_le i g
  nlinarith [mul_nonneg (show 0 ≤ (τ : ℝ)^2 by positivity) (sub_nonneg.mpr hc)]

def activePairSupport (i : Fin 3) (t : Parameters G) : Finset G :=
  ((activeParts i) ×ˢ (Finset.univ : Finset Bool)).image (fun jb =>
    if jb.2 then -coordinate t jb.1 else coordinate t jb.1)

/-- With one coordinate fixed, an inverse orbit appears in at most four
choices among the two remaining coordinates. -/
theorem active_orbit_incidence_on_section (i : Fin 3) (g z : G) :
    (((Finset.univ : Finset (Parameters G)).filter
      (fun t => coordinate t i = g ∧ z ∈ activePairSupport i t)).card : ℝ) ≤ 4 := by
  let C : Finset (Parameters G) := Finset.univ.filter (fun t => coordinate t i = g)
  let D : Finset (Fin 3 × Bool) := (activeParts i) ×ˢ Finset.univ
  let hit (jb : Fin 3 × Bool) : Finset (Parameters G) :=
    C.filter (fun t => (if jb.2 then -coordinate t jb.1 else coordinate t jb.1) = z)
  have hhit : ∀ jb ∈ D, ((hit jb).card : ℝ) ≤ 1 := by
    rintro ⟨j,b⟩ hj
    have hj' : j ≠ i := (Finset.mem_erase.mp (Finset.mem_product.mp hj).1).1
    cases b with
    | false =>
      have heq : hit (j,false) = (Finset.univ : Finset (Parameters G)).filter
          (fun t => coordinate t i = g ∧ coordinate t j = z) := by
        ext t; simp [hit,C]
      rw [heq]
      exact_mod_cast twoCoordinates_section_card_le i j hj'.symm g z
    | true =>
      have heq : hit (j,true) = (Finset.univ : Finset (Parameters G)).filter
          (fun t => coordinate t i = g ∧ coordinate t j = -z) := by
        ext t; simp [hit,C,neg_eq_iff_eq_neg]
      rw [heq]
      exact_mod_cast twoCoordinates_section_card_le i j hj'.symm g (-z)
  have hsub : (Finset.univ : Finset (Parameters G)).filter
      (fun t => coordinate t i = g ∧ z ∈ activePairSupport i t) ⊆ D.biUnion hit := by
    intro t ht
    obtain ⟨htdir,htsupp⟩ := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ht
    obtain ⟨jb,hj,hjt⟩ := Finset.mem_image.mp htsupp
    exact Finset.mem_biUnion.mpr ⟨jb,hj,Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,htdir⟩,hjt⟩⟩
  have hD : D.card = 4 := by simp [D, activeParts_card]
  calc
    _ ≤ ((D.biUnion hit).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ jb ∈ D, ((hit jb).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := D) (t := hit))
    _ ≤ ∑ _jb ∈ D, (1 : ℝ) := Finset.sum_le_sum hhit
    _ = _ := by simp [hD]

theorem sectionMajorant_mem_congr_off_orbit (Q Q' : Vertex G → Prop)
    (i : Fin 3) (g z : G) (t : Parameters G)
    (hQeq : ∀ v, v.2 ≠ z → v.2 ≠ -z → (Q v ↔ Q' v))
    (hz : z ∉ activePairSupport i t) :
    t ∈ sectionMajorant Q i g ↔ t ∈ sectionMajorant Q' i g := by
  have hvQ (j : Fin 3) (hj : j ∈ activeParts i) :
      Q (j,coordinate t j) ↔ Q' (j,coordinate t j) := by
    apply hQeq
    · intro he
      apply hz
      apply Finset.mem_image.mpr
      exact ⟨(j,false),Finset.mem_product.mpr ⟨hj,Finset.mem_univ _⟩,by simpa using he⟩
    · intro he
      apply hz
      apply Finset.mem_image.mpr
      change coordinate t j = -z at he
      exact ⟨(j,true),Finset.mem_product.mpr ⟨hj,Finset.mem_univ _⟩,by simp [he]⟩
  have hlab : activeLabels Q t i ↔ activeLabels Q' t i := by
    constructor <;> intro h j hj
    · exact (hvQ j hj).mp (h j hj)
    · exact (hvQ j hj).mpr (h j hj)
  simp only [sectionMajorant, Finset.mem_filter, hlab]

def sectionChangedCandidates (Q Q' : Vertex G → Prop) (i : Fin 3) (g : G) :
    Finset (Parameters G) :=
  (sectionMajorant Q i g \ sectionMajorant Q' i g) ∪
    (sectionMajorant Q' i g \ sectionMajorant Q i g)

/-- The same section majorant whose mean is at most τ²n changes by at
most four when one orbit's labels change. -/
theorem sectionMajorant_count_change_le (Q Q' : Vertex G → Prop)
    (i : Fin 3) (g z : G)
    (hQeq : ∀ v, v.2 ≠ z → v.2 ≠ -z → (Q v ↔ Q' v)) :
    |((sectionMajorant Q i g).card : ℝ) - ((sectionMajorant Q' i g).card : ℝ)| ≤ 4 := by
  let A := sectionMajorant Q i g
  let B := sectionMajorant Q' i g
  have hchanged : (sectionChangedCandidates Q Q' i g).card ≤ 4 := by
    have hsub : sectionChangedCandidates Q Q' i g ⊆
        (Finset.univ : Finset (Parameters G)).filter
          (fun t => coordinate t i = g ∧ z ∈ activePairSupport i t) := by
      intro t ht
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rcases Finset.mem_union.mp ht with ht | ht
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp ht).1).1).2
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp ht).1).1).2
      · by_contra hz
        have heq := sectionMajorant_mem_congr_off_orbit Q Q' i g z t hQeq hz
        rcases Finset.mem_union.mp ht with ht | ht
        · exact (Finset.mem_sdiff.mp ht).2 (heq.mp (Finset.mem_sdiff.mp ht).1)
        · exact (Finset.mem_sdiff.mp ht).2 (heq.mpr (Finset.mem_sdiff.mp ht).1)
    have hinc := active_orbit_incidence_on_section (G := G) i g z
    have hn : (((Finset.univ : Finset (Parameters G)).filter
        (fun t => coordinate t i = g ∧ z ∈ activePairSupport i t)).card) ≤ 4 := by
      exact_mod_cast hinc
    exact (Finset.card_le_card hsub).trans hn
  have hleft : A.card ≤ B.card + 4 := by
    have h₁ := Finset.card_sdiff_add_card_inter A B
    have h₂ := Finset.card_sdiff_add_card_inter B A
    have hd := Finset.card_le_card (s := A \ B) (t := sectionChangedCandidates Q Q' i g)
      Finset.subset_union_left
    rw [Finset.inter_comm B A] at h₂
    omega
  have hright : B.card ≤ A.card + 4 := by
    have h₁ := Finset.card_sdiff_add_card_inter A B
    have h₂ := Finset.card_sdiff_add_card_inter B A
    have hd := Finset.card_le_card (s := B \ A) (t := sectionChangedCandidates Q Q' i g)
      Finset.subset_union_right
    rw [Finset.inter_comm B A] at h₂
    omega
  have hl' : (A.card : ℝ) ≤ (B.card : ℝ) + 4 := by exact_mod_cast hleft
  have hr' : (B.card : ℝ) ≤ (A.card : ℝ) + 4 := by exact_mod_cast hright
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem sampled_sectionMajorant_count_change_le
    (ω ω' : FullSample G) (o : OddOrbit G)
    (hchild : ∀ o' : OddOrbit G, o' ≠ o →
      childLabel ((regroup ω).1 o') = childLabel ((regroup ω').1 o'))
    (i : Fin 3) (g : G) :
    |((sectionMajorant (ReservoirVertex ω true) i g).card : ℝ) -
      ((sectionMajorant (ReservoirVertex ω' true) i g).card : ℝ)| ≤ 4 :=
  sectionMajorant_count_change_le (ReservoirVertex ω true) (ReservoirVertex ω' true)
    i g (orbitPlace (o,false))
    (EndpointMatching.Tetrahedron.sampled_reservoir_agrees_off_orbit ω ω' o hchild)

end
end EndpointMatching.UniversalCore.Buffer
