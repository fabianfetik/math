import CorralFormalization.EndpointProof.Flow.Tetrahedron.TotalExpectation
import CorralFormalization.EndpointProof.Flow.Tetrahedron.SectionSensitivity
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
namespace EndpointMatching.Tetrahedron
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointFullProduct EndpointOriginalReservoir EndpointBlockAvailability
open EndpointSharedSample EndpointReservoirAvailability
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

abbrev ActiveIndex (i : Fin 6) := {j : Fin 12 // j ∈ activeRepresentatives i}

theorem activeIndex_card (i : Fin 6) : Fintype.card (ActiveIndex i) = 10 := by
  simp [ActiveIndex, activeRepresentatives_card]

def activeOrbitEmbedding (hodd : Odd (Fintype.card G)) (r : TetrahedronRoots G)
    (t : TetrahedronParameters G) (hv : geometricallyValid r t) (i : Fin 6) :
    Unit × ActiveIndex i ↪ OddOrbit G where
  toFun := fun k => (representativeOrbitPoint hodd r t hv k.2.1).1
  inj' := by
    intro x y he
    have hxy := representativeOrbit_injective hodd r t hv he
    cases x with | mk x xj =>
      cases y with | mk y yj =>
        cases x; cases y
        have : xj = yj := Subtype.ext hxy
        subst yj
        rfl

def activeDemand (i : Fin 6) (_ : Unit) (j : ActiveIndex i) : Label := qDemand () j.1

theorem qDemand_weight (p τ : ℝ≥0) (i : Fin 12) :
    (labelWeights p τ (qDemand () i) : ℝ) = τ := by
  fin_cases i <;> simp [qDemand, representativeSlot,encodeChild,labelWeights]

theorem activeDemand_probability (p τ : ℝ≥0) (i : Fin 6) :
    successProbability p τ (activeDemand i ()) = (τ : ℝ)^10 := by
  simp only [successProbability, activeDemand, qDemand_weight]
  simp [activeRepresentatives_card]

/-- A single admissible candidate meets the ten nonconstant categorical
label requirements with probability τ¹⁰. -/
theorem ten_labels_probability (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (i : Fin 6) :
    (sampleMeasure (I := Unit) (J := ActiveIndex i) p τ h).real
      {w | w () = activeDemand i ()} = (τ : ℝ)^10 := by
  have hI := integral_successIndicator (I := Unit) (J := ActiveIndex i) p τ h (activeDemand i) ()
  have hfun : successIndicator (activeDemand i) () =
      Set.indicator {w : Unit → ActiveIndex i → Label | w () = activeDemand i ()} 1 := by
    funext w
    simp [successIndicator, Set.indicator_apply]
  rw [hfun, integral_indicator_one (by measurability)] at hI
  exact hI.trans (activeDemand_probability p τ i)

theorem validActiveLabels_probability (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (r : TetrahedronRoots G) (t : TetrahedronParameters G) (hv : geometricallyValid r t)
    (i : Fin 6) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ∀ j ∈ activeRepresentatives i,
        ReservoirVertex ω true
          (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot j))} =
      (τ : ℝ)^10 := by
  let e := activeOrbitEmbedding hodd r t hv i
  let ev : Set (Unit → ActiveIndex i → Label) := {w | w () = activeDemand i ()}
  have hevent : {ω : FullSample G | ∀ j ∈ activeRepresentatives i,
      ReservoirVertex ω true
        (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot j))} =
      (fun ω => project e (fullLabels ω)) ⁻¹' ev := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · intro hlabels
      funext j
      change fullLabels ω ((representativeOrbitPoint hodd r t hv j.1).1) = qDemand () j.1
      exact (representative_Q_iff_encoded hodd r t hv ω j.1).mp (hlabels j.1 j.2)
    · intro hlabels j hj
      apply (representative_Q_iff_encoded hodd r t hv ω j).mpr
      have hj' := congrFun hlabels ⟨j,hj⟩
      change fullLabels ω ((representativeOrbitPoint hodd r t hv j).1) = qDemand () j at hj'
      exact hj'
  have hp := (project_measurePreserving (I := Unit) (J := ActiveIndex i) p τ h e).comp
    (fullLabels_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ)
  rw [hevent]
  change (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
    ((project e ∘ fullLabels) ⁻¹' ev) = (τ : ℝ)^10
  rw [hp.measureReal_preimage (by measurability)]
  exact ten_labels_probability p τ h i

/-- Geometry-valid triples in one of the six fixed direction sections. -/
def validSectionParameters (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    Finset (TetrahedronParameters G) :=
  (validParameterSet r).filter (fun t => tetrahedronDirection i t = g)

def activeLabels (Q : Vertex G → Prop) (r : TetrahedronRoots G)
    (t : TetrahedronParameters G) (i : Fin 6) : Prop :=
  ∀ j ∈ activeRepresentatives i,
    Q (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot j))

/-- The section-majorant keeps the ten active Q labels and omits the two
constant labels, while retaining the paper's full geometry test. -/
def validReducedSection (Q : Vertex G → Prop) (r : TetrahedronRoots G)
    (i : Fin 6) (g : G) : Finset (TetrahedronParameters G) :=
  (validSectionParameters r i g).filter (fun t => activeLabels Q r t i)

theorem goodSection_subset_validReduced (ω : FullSample G) (r : TetrahedronRoots G)
    (i : Fin 6) (g : G) :
    (goodCandidates (ReservoirVertex ω true) r).filter
      (fun t => tetrahedronDirection i t = g) ⊆
      validReducedSection (ReservoirVertex ω true) r i g := by
  intro t ht
  obtain ⟨ht,hdir⟩ := Finset.mem_filter.mp ht
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨sampled_goodCandidates_subset_valid ω r ht,hdir⟩, ?_⟩
  intro j hj
  have hQ := (Finset.mem_filter.mp ht).2.2.1
  exact hQ _ (Finset.mem_image.mpr ⟨representativeSlot j,representativeSlot_mem_added j,rfl⟩)

theorem validSectionParameters_card_le (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    (validSectionParameters r i g).card ≤ (Fintype.card G)^2 := by
  have hsub : validSectionParameters r i g ⊆
      (Finset.univ : Finset (TetrahedronParameters G)).filter
        (fun t => tetrahedronDirection i t = g) := by
    intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ht).2⟩
  exact (Finset.card_le_card hsub).trans (direction_section_card_le i g)

def activeLabelsIndicator (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (i : Fin 6) (ω : FullSample G) : ℝ :=
  if activeLabels (ReservoirVertex ω true) r t i then 1 else 0

theorem validReducedSection_card_sum (r : TetrahedronRoots G)
    (i : Fin 6) (g : G) (ω : FullSample G) :
    ((validReducedSection (ReservoirVertex ω true) r i g).card : ℝ) =
      ∑ t ∈ validSectionParameters r i g, activeLabelsIndicator r t i ω := by
  exact (Finset.sum_boole (R := ℝ)
    (fun t => activeLabels (ReservoirVertex ω true) r t i) (validSectionParameters r i g)).symm

/-- The exact mean of the ten-label section majorant. -/
theorem validReducedSection_expectation (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    (∫ ω : FullSample G, ((validReducedSection (ReservoirVertex ω true) r i g).card : ℝ)
      ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)) =
      ((validSectionParameters r i g).card : ℝ) * (τ : ℝ)^10 := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  have hfun (t : TetrahedronParameters G) : activeLabelsIndicator r t i =
      Set.indicator {ω : FullSample G | activeLabels (ReservoirVertex ω true) r t i} 1 := by
    funext ω
    simp [activeLabelsIndicator, Set.indicator_apply]
  have hint (t : TetrahedronParameters G) : Integrable (activeLabelsIndicator r t i) μ := by
    rw [hfun]
    exact (integrable_const 1).indicator (by measurability)
  calc
    _ = ∫ ω : FullSample G, ∑ t ∈ validSectionParameters r i g,
        activeLabelsIndicator r t i ω ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ (validReducedSection_card_sum r i g)
    _ = ∑ t ∈ validSectionParameters r i g, ∫ ω, activeLabelsIndicator r t i ω ∂μ :=
      integral_finsetSum _ (fun t _ => hint t)
    _ = ∑ _t ∈ validSectionParameters r i g, (τ : ℝ)^10 := by
      apply Finset.sum_congr rfl
      intro t ht
      have hv : geometricallyValid r t := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
      rw [hfun, integral_indicator_one (by measurability)]
      exact validActiveLabels_probability hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ r t hv i
    _ = _ := by simp

/-- Each majorant has mean at most τ¹⁰|G|², as required in the paired cover construction. -/
theorem validReducedSection_expectation_le (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    (∫ ω : FullSample G, ((validReducedSection (ReservoirVertex ω true) r i g).card : ℝ)
      ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)) ≤
      (τ : ℝ)^10 * (Fintype.card G : ℝ)^2 := by
  rw [validReducedSection_expectation hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ]
  have hc : ((validSectionParameters r i g).card : ℝ) ≤ (Fintype.card G : ℝ)^2 := by
    exact_mod_cast validSectionParameters_card_le r i g
  nlinarith [mul_nonneg (show 0 ≤ (τ : ℝ)^10 by positivity)
    (sub_nonneg.mpr hc)]

/-- Changing a single inverse orbit leaves a section-majorant candidate
unchanged whenever none of its ten active representatives uses that orbit. -/
theorem validReducedSection_mem_congr_off_orbit (Q Q' : Vertex G → Prop)
    (r : TetrahedronRoots G) (i : Fin 6) (g z : G) (t : TetrahedronParameters G)
    (hQeq : ∀ v, v.2 ≠ z → v.2 ≠ -z → (Q v ↔ Q' v))
    (hz : z ∉ activePairSupport r i t) :
    t ∈ validReducedSection Q r i g ↔ t ∈ validReducedSection Q' r i g := by
  have hvQ (j : Fin 12) (hj : j ∈ activeRepresentatives i) :
      Q (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot j)) ↔
      Q' (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot j)) := by
    apply hQeq
    · intro he
      apply hz
      apply Finset.mem_image.mpr
      refine ⟨(j,false), Finset.mem_product.mpr ⟨hj,Finset.mem_univ _⟩, ?_⟩
      simpa [representativeSlot_value] using he
    · intro he
      apply hz
      apply Finset.mem_image.mpr
      refine ⟨(j,true), Finset.mem_product.mpr ⟨hj,Finset.mem_univ _⟩, ?_⟩
      have he' : tetrahedronRepresentative r j t = -z := by
        simpa [representativeSlot_value] using he
      simp [he']
  have hlab : activeLabels Q r t i ↔ activeLabels Q' r t i := by
    constructor <;> intro h j hj
    · exact (hvQ j hj).mp (h j hj)
    · exact (hvQ j hj).mpr (h j hj)
  simp only [validReducedSection, Finset.mem_filter, hlab]

def validReducedChangedCandidates (Q Q' : Vertex G → Prop) (r : TetrahedronRoots G)
    (i : Fin 6) (g : G) : Finset (TetrahedronParameters G) :=
  (validReducedSection Q r i g \ validReducedSection Q' r i g) ∪
    (validReducedSection Q' r i g \ validReducedSection Q r i g)

/-- The same section majorant whose mean is controlled above changes by at
most 20|G| when the Q labels of one inverse orbit are changed. -/
theorem validReducedSection_count_change_le (Q Q' : Vertex G → Prop)
    (r : TetrahedronRoots G) (i : Fin 6) (g z : G)
    (hQeq : ∀ v, v.2 ≠ z → v.2 ≠ -z → (Q v ↔ Q' v)) :
    |((validReducedSection Q r i g).card : ℝ) -
      ((validReducedSection Q' r i g).card : ℝ)| ≤ 20 * (Fintype.card G : ℝ) := by
  let A := validReducedSection Q r i g
  let B := validReducedSection Q' r i g
  let N := 20 * Fintype.card G
  have hchanged : (validReducedChangedCandidates Q Q' r i g).card ≤ N := by
    have hsub : validReducedChangedCandidates Q Q' r i g ⊆
        (Finset.univ : Finset (TetrahedronParameters G)).filter
          (fun t => tetrahedronDirection i t = g ∧ z ∈ activePairSupport r i t) := by
      intro t ht
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rcases Finset.mem_union.mp ht with ht | ht
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp ht).1).1).2
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp ht).1).1).2
      · by_contra hz
        have heq := validReducedSection_mem_congr_off_orbit Q Q' r i g z t hQeq hz
        rcases Finset.mem_union.mp ht with ht | ht
        · exact (Finset.mem_sdiff.mp ht).2 (heq.mp (Finset.mem_sdiff.mp ht).1)
        · exact (Finset.mem_sdiff.mp ht).2 (heq.mpr (Finset.mem_sdiff.mp ht).1)
    have hinc := active_orbit_incidence_on_section r i g z
    have hn : (((Finset.univ : Finset (TetrahedronParameters G)).filter
        (fun t => tetrahedronDirection i t = g ∧ z ∈ activePairSupport r i t)).card) ≤ N := by
      dsimp [N]
      exact_mod_cast hinc
    exact (Finset.card_le_card hsub).trans hn
  have hleft : A.card ≤ B.card + N := by
    have h₁ := Finset.card_sdiff_add_card_inter A B
    have h₂ := Finset.card_sdiff_add_card_inter B A
    have hd := Finset.card_le_card (s := A \ B) (t := validReducedChangedCandidates Q Q' r i g)
      Finset.subset_union_left
    rw [Finset.inter_comm B A] at h₂
    omega
  have hright : B.card ≤ A.card + N := by
    have h₁ := Finset.card_sdiff_add_card_inter A B
    have h₂ := Finset.card_sdiff_add_card_inter B A
    have hd := Finset.card_le_card (s := B \ A) (t := validReducedChangedCandidates Q Q' r i g)
      Finset.subset_union_right
    rw [Finset.inter_comm B A] at h₂
    omega
  have hl' : (A.card : ℝ) ≤ (B.card : ℝ) + 20 * (Fintype.card G : ℝ) := by
    dsimp [N] at hleft; exact_mod_cast hleft
  have hr' : (B.card : ℝ) ≤ (A.card : ℝ) + 20 * (Fintype.card G : ℝ) := by
    dsimp [N] at hright; exact_mod_cast hright
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem sampled_validReducedSection_count_change_le
    (ω ω' : FullSample G) (o : OddOrbit G)
    (hchild : ∀ o' : OddOrbit G, o' ≠ o →
      childLabel ((regroup ω).1 o') = childLabel ((regroup ω').1 o'))
    (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    |((validReducedSection (ReservoirVertex ω true) r i g).card : ℝ) -
      ((validReducedSection (ReservoirVertex ω' true) r i g).card : ℝ)| ≤
        20 * (Fintype.card G : ℝ) :=
  validReducedSection_count_change_le (ReservoirVertex ω true) (ReservoirVertex ω' true)
    r i g (orbitPlace (o,false)) (sampled_reservoir_agrees_off_orbit ω ω' o hchild)

end
end EndpointMatching.Tetrahedron
