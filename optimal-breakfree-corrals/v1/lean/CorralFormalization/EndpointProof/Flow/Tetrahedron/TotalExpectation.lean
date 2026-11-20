import CorralFormalization.EndpointProof.Flow.Tetrahedron.ValidityBridge
import CorralFormalization.EndpointProof.Sampling.FullAvailability
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

def representativeOrbitPoint (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (hv : geometricallyValid r t) (i : Fin 12) : OddOrbit G × Bool :=
  Classical.choose (orbitPlace_covers_nonzero hodd (hv.1 i))

theorem representativeOrbitPoint_spec (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (hv : geometricallyValid r t) (i : Fin 12) :
    orbitPlace (representativeOrbitPoint hodd r t hv i) = tetrahedronRepresentative r i t :=
  Classical.choose_spec (orbitPlace_covers_nonzero hodd (hv.1 i))

theorem same_orbit_coordinates (o : OddOrbit G) (b c : Bool) :
    orbitPlace (o,b) = orbitPlace (o,c) ∨ orbitPlace (o,b) = -orbitPlace (o,c) := by
  cases b <;> cases c <;> simp [orbitPlace, orbitCoordinate]

theorem representativeOrbit_injective (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (t : TetrahedronParameters G) (hv : geometricallyValid r t) :
    Function.Injective (fun i => (representativeOrbitPoint hodd r t hv i).1) := by
  intro i j he
  by_contra hij
  have hp := geometricallyValid_pair r t hv i j hij
  have hi := representativeOrbitPoint_spec hodd r t hv i
  have hj := representativeOrbitPoint_spec hodd r t hv j
  let oi := representativeOrbitPoint hodd r t hv i
  let oj := representativeOrbitPoint hodd r t hv j
  have he' : oi.1 = oj.1 := he
  have hsign : orbitPlace oi = orbitPlace oj ∨ orbitPlace oi = -orbitPlace oj := by
    rcases oi with ⟨o,b⟩
    rcases oj with ⟨o',c⟩
    dsimp at he'
    subst o'
    exact same_orbit_coordinates o b c
  rcases hsign with hs | hs
  · exact hp.1 (hi.symm.trans (hs.trans hj))
  · exact hp.2 (hi.symm.trans (hs.trans (congrArg Neg.neg hj)))

def representativeOrbitEmbedding (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (t : TetrahedronParameters G) (hv : geometricallyValid r t) :
    Unit × Fin 12 ↪ OddOrbit G where
  toFun := fun k => (representativeOrbitPoint hodd r t hv k.2).1
  inj' := by
    intro x y he
    have hxy := representativeOrbit_injective hodd r t hv he
    cases x with | mk x i =>
      cases y with | mk y j =>
        cases x; cases y
        simp_all

def qDemand (_ : Unit) (i : Fin 12) : Label :=
  encodeChild (some ((representativeSlot i).1,true))

theorem qDemand_probability (p τ : ℝ≥0) :
    successProbability p τ (qDemand ()) = (τ : ℝ)^12 := by
  norm_num [successProbability, qDemand, representativeSlot, encodeChild, labelWeights,
    Fin.prod_univ_succ]
  ring

/-- Every representative Q label is exactly the encoded label of the
same chosen inverse orbit in the actual augmented sample. -/
theorem representative_Q_iff_encoded (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (t : TetrahedronParameters G) (hv : geometricallyValid r t)
    (ω : FullSample G) (i : Fin 12) :
    ReservoirVertex ω true
      (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot i)) ↔
    fullLabels ω ((representativeOrbitPoint hodd r t hv i).1) = qDemand () i := by
  let p := representativeSlot i
  let op := representativeOrbitPoint hodd r t hv i
  have hcoord : orbitPlace op = (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 p).2 := by
    rw [representativeOrbitPoint_spec, representativeSlot_value]
  have hlabel : fullLabels ω op.1 = qDemand () i ↔
      childLabel ((regroup ω).1 op.1) = some (p.1,true) := by
    change encodeChild (childLabel ((regroup ω).1 op.1)) = encodeChild (some (p.1,true)) ↔ _
    exact encodeChild_bijective.injective.eq_iff
  rw [hlabel]
  constructor
  · rintro ⟨o,side,ho,hl⟩
    have he : (o,side) = op := orbitPlace.injective (ho.trans hcoord.symm)
    have hfirst : o = op.1 := congrArg Prod.fst he
    simpa [hfirst, place] using hl
  · intro hl
    exact ⟨op.1,op.2,hcoord,hl⟩

/-- The probability of the prescribed twelve categorical labels, for one
candidate; no independence between different candidates is assumed. -/
theorem twelve_labels_probability (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) :
    (sampleMeasure (I := Unit) (J := Fin 12) p τ h).real
      {w | w () = qDemand ()} = (τ : ℝ)^12 := by
  have hI := integral_successIndicator (I := Unit) (J := Fin 12) p τ h qDemand ()
  have hfun : successIndicator qDemand () =
      Set.indicator {w : Unit → Fin 12 → Label | w () = qDemand ()} 1 := by
    funext w
    simp [successIndicator, Set.indicator_apply]
  rw [hfun, integral_indicator_one (by measurability)] at hI
  exact hI.trans (qDemand_probability p τ)

/-- A geometrically valid actual tetrahedron succeeds with probability
τ¹² in the full original sample and its single augmentation. -/
theorem validCandidate_probability (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (r : TetrahedronRoots G) (hr : admissibleRoots r) (t : TetrahedronParameters G)
    (ht : t ∈ validParameterSet r) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | t ∈ goodCandidates (ReservoirVertex ω true) r} = (τ : ℝ)^12 := by
  let hv : geometricallyValid r t := (Finset.mem_filter.mp ht).2
  let e := representativeOrbitEmbedding hodd r t hv
  let ev : Set (Unit → Fin 12 → Label) := {w | w () = qDemand ()}
  have hevent : {ω : FullSample G | t ∈ goodCandidates (ReservoirVertex ω true) r} =
      (fun ω => project e (fullLabels ω)) ⁻¹' ev := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [validParameter_mem_goodCandidates_iff hodd (ReservoirVertex ω true)
      (pairReservoir_of_reservoirVertex ω true) r hr t ht]
    constructor
    · intro hlabels
      funext i
      change fullLabels ω ((representativeOrbitPoint hodd r t hv i).1) = qDemand () i
      exact (representative_Q_iff_encoded hodd r t hv ω i).mp (hlabels i)
    · intro hlabels i
      apply (representative_Q_iff_encoded hodd r t hv ω i).mpr
      have hi := congrFun hlabels i
      change fullLabels ω ((representativeOrbitPoint hodd r t hv i).1) = qDemand () i at hi
      exact hi
  have hp := (project_measurePreserving (I := Unit) (J := Fin 12) p τ h e).comp
    (fullLabels_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ)
  rw [hevent]
  change (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
    ((project e ∘ fullLabels) ⁻¹' ev) = (τ : ℝ)^12
  rw [hp.measureReal_preimage (by measurability)]
  exact twelve_labels_probability p τ h

/-- Valid parameter triples which succeed on the given single augmentation. -/
def validSuccessfulCandidates (r : TetrahedronRoots G) (ω : FullSample G) :
    Finset (TetrahedronParameters G) :=
  (validParameterSet r).filter (fun t => t ∈ goodCandidates (ReservoirVertex ω true) r)

def candidateIndicator (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (ω : FullSample G) : ℝ := if t ∈ goodCandidates (ReservoirVertex ω true) r then 1 else 0

theorem validSuccessfulCandidates_card_sum (r : TetrahedronRoots G) (ω : FullSample G) :
    ((validSuccessfulCandidates r ω).card : ℝ) =
      ∑ t ∈ validParameterSet r, candidateIndicator r t ω := by
  exact (Finset.sum_boole (R := ℝ) (fun t => t ∈ goodCandidates (ReservoirVertex ω true) r)
    (validParameterSet r)).symm

/-- Exact expectation of the successful valid triples on the original
shared sample. Candidate successes may overlap arbitrarily. -/
theorem validSuccessfulCandidates_expectation (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (r : TetrahedronRoots G) (hr : admissibleRoots r) :
    (∫ ω : FullSample G, ((validSuccessfulCandidates r ω).card : ℝ)
      ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)) =
      ((validParameterSet r).card : ℝ) * (τ : ℝ)^12 := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  have hfun (t : TetrahedronParameters G) : candidateIndicator r t =
      Set.indicator {ω : FullSample G | t ∈ goodCandidates (ReservoirVertex ω true) r} 1 := by
    funext ω
    simp [candidateIndicator, Set.indicator_apply]
  have hint (t : TetrahedronParameters G) : Integrable (candidateIndicator r t) μ := by
    rw [hfun]
    exact (integrable_const 1).indicator (by measurability)
  calc
    _ = ∫ ω : FullSample G, ∑ t ∈ validParameterSet r, candidateIndicator r t ω ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ (validSuccessfulCandidates_card_sum r)
    _ = ∑ t ∈ validParameterSet r, ∫ ω, candidateIndicator r t ω ∂μ :=
      integral_finsetSum _ (fun t _ => hint t)
    _ = ∑ _t ∈ validParameterSet r, (τ : ℝ)^12 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hfun, integral_indicator_one (by measurability)]
      exact validCandidate_probability hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ r hr t ht
    _ = _ := by simp

/-- In the categorical sample, every successful candidate is strongly
valid, so the restricted count is exactly the total successful count. -/
theorem validSuccessfulCandidates_eq_goodCandidates (r : TetrahedronRoots G)
    (ω : FullSample G) :
    validSuccessfulCandidates r ω = goodCandidates (ReservoirVertex ω true) r := by
  ext t
  simp only [validSuccessfulCandidates, Finset.mem_filter]
  constructor
  · exact And.right
  · intro ht
    exact ⟨sampled_goodCandidates_subset_valid ω r ht,ht⟩

/-- Exact expectation of the full successful tetrahedron count on the
actual augmented sample. Different parameter triples may overlap. -/
theorem goodCandidates_expectation_eq (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (r : TetrahedronRoots G) (hr : admissibleRoots r) :
    (∫ ω : FullSample G, ((goodCandidates (ReservoirVertex ω true) r).card : ℝ)
      ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)) =
      ((validParameterSet r).card : ℝ) * (τ : ℝ)^12 := by
  simpa only [validSuccessfulCandidates_eq_goodCandidates] using
    validSuccessfulCandidates_expectation hodd q η a b hq0 hq1 hη0 hη1
      ha hb hab p τ h hP hQ r hr

/-- For n≥1152, the total successful-count mean is at least
(3/4) τ¹² n³, with no independence required between different triples. -/
theorem goodCandidates_expectation_lower (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (r : TetrahedronRoots G) (hr : admissibleRoots r) (hn : 1152 ≤ Fintype.card G) :
    (3 / 4 : ℝ) * (τ : ℝ)^12 * (Fintype.card G : ℝ)^3 ≤
      ∫ ω : FullSample G, ((goodCandidates (ReservoirVertex ω true) r).card : ℝ)
        ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) := by
  rw [goodCandidates_expectation_eq hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ r hr]
  have hthree : (3 : ℝ) * (Fintype.card G : ℝ)^3 ≤
      4 * ((validParameterSet r).card : ℝ) := by
    exact_mod_cast validParameterSet_three_quarters hodd r hr hn
  have hprod := mul_le_mul_of_nonneg_right hthree (show 0 ≤ (τ : ℝ)^12 by positivity)
  nlinarith

end
end EndpointMatching.Tetrahedron
