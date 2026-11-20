import CorralFormalization.EndpointProof.Probability.FiniteProductConcentration
import CorralFormalization.EndpointProof.Sampling.FullAvailability

/-!
The six P/Q inverse-pair counts for the universal core. All six are functions of the
same actual categorical label sample. Their common event uses a finite
union bound, not independence between the six counts.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal

namespace EndpointPairInventoryCounts
open EndpointFullProduct EndpointOriginalReservoir EndpointBlockAvailability
open EndpointSharedSample EndpointReservoirAvailability
open EndpointFiniteProductConcentration
noncomputable section

/-- Categorical label demanded by a fixed part and P/Q kind. -/
def pairLabel (part : Fin 3) (kind : Bool) : Label := encodeChild (some (part,kind))

def pairDensity (p τ : ℝ≥0) (kind : Bool) : ℝ≥0 := if kind then τ else p

theorem pairLabel_weight (p τ : ℝ≥0) (part : Fin 3) (kind : Bool) :
    labelWeights p τ (pairLabel part kind) = pairDensity p τ kind := by
  fin_cases part <;> cases kind <;> rfl

/-- The selected inverse orbits, one per physical pair. -/
def pairOrbitSet {O : Type*} [Fintype O] (w : O → Label) (part : Fin 3) (kind : Bool) :
    Finset O := Finset.univ.filter (fun o => w o = pairLabel part kind)

def categoricalPairCount {O : Type*} [Fintype O] (part : Fin 3) (kind : Bool)
    (w : O → Label) : ℝ := (pairOrbitSet w part kind).card

/-- Deterministic oscillation one for one demanded categorical pair label. -/
theorem categoricalPairCount_boundedDifferences {O : Type*} [Fintype O]
    (part : Fin 3) (kind : Bool) :
    CoordinateBoundedDifferences (categoricalPairCount (O := O) part kind) (fun _ => 1) := by
  classical
  intro o w w' hw
  have hsub (x y : O → Label) (hxy : ∀ j, j ≠ o → x j = y j) :
      pairOrbitSet x part kind ⊆ insert o (pairOrbitSet y part kind) := by
    intro j hj
    by_cases hjo : j = o
    · exact Finset.mem_insert.mpr (Or.inl hjo)
    · apply Finset.mem_insert.mpr
      right
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (hxy j hjo).symm.trans (Finset.mem_filter.mp hj).2⟩
  have hl := (Finset.card_le_card (hsub w w' hw)).trans (Finset.card_insert_le o _)
  have hr := (Finset.card_le_card (hsub w' w (fun j hj => (hw j hj).symm))).trans
    (Finset.card_insert_le o _)
  have hl' : ((pairOrbitSet w part kind).card : ℝ) ≤ (pairOrbitSet w' part kind).card + 1 := by
    exact_mod_cast hl
  have hr' : ((pairOrbitSet w' part kind).card : ℝ) ≤ (pairOrbitSet w part kind).card + 1 := by
    exact_mod_cast hr
  exact abs_le.mpr ⟨by dsimp [categoricalPairCount]; linarith,
    by dsimp [categoricalPairCount]; linarith⟩

theorem categoricalPairCount_sum {O : Type*} [Fintype O]
    (part : Fin 3) (kind : Bool) (w : O → Label) :
    categoricalPairCount part kind w = ∑ o, if w o = pairLabel part kind then (1 : ℝ) else 0 := by
  exact (Finset.sum_boole (R := ℝ) (fun o => w o = pairLabel part kind) Finset.univ).symm

/-- Exact categorical expectation, without requiring independence between
counts of different labels. -/
theorem categoricalPairCount_expectation {O : Type*} [Fintype O]
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (part : Fin 3) (kind : Bool) :
    (∫ w : O → Label, categoricalPairCount part kind w ∂orbitMeasure p τ h) =
      (Fintype.card O : ℝ) * pairDensity p τ kind := by
  let μ := orbitMeasure (O := O) p τ h
  have hone (o : O) : (∫ w : O → Label, if w o = pairLabel part kind then (1 : ℝ) else 0 ∂μ) =
      pairDensity p τ kind := by
    have hp := measurePreserving_eval (fun _ : O => labelMeasure p τ h) o
    have hprob : μ.real {w | w o = pairLabel part kind} = (pairDensity p τ kind : ℝ) := by
      have hevent : {w : O → Label | w o = pairLabel part kind} =
          (fun w : O → Label => w o) ⁻¹' {pairLabel part kind} := rfl
      rw [hevent]
      change (Measure.pi (fun _ : O => labelMeasure p τ h)).real
        (Function.eval o ⁻¹' {pairLabel part kind}) = _
      rw [hp.measureReal_preimage (s := {pairLabel part kind}) (measurableSet_singleton _)]
      simp [measureReal_def, labelMeasure_singleton, pairLabel_weight]
    have hfun : (fun w : O → Label => if w o = pairLabel part kind then (1 : ℝ) else 0) =
        Set.indicator {w | w o = pairLabel part kind} 1 := by
      funext w
      simp [Set.indicator_apply]
    rw [hfun, integral_indicator_one (by measurability)]
    exact hprob
  change (∫ w : O → Label, categoricalPairCount part kind w ∂μ) = _
  simp_rw [categoricalPairCount_sum]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [hone]
  simp

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Odd order gives exactly (n-1)/2 nonzero numerical inverse pairs. -/
theorem oddOrbit_card_identity (hodd : Odd (Fintype.card G)) :
    2 * Fintype.card (OddOrbit G) + 1 = Fintype.card G := by
  have h := Fintype.card_congr (fullPlaceEquiv (G := G) hodd)
  simpa only [Fintype.card_option, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using h

theorem oddOrbit_card_real (hodd : Odd (Fintype.card G)) :
    (Fintype.card (OddOrbit G) : ℝ) = ((Fintype.card G : ℝ)-1)/2 := by
  have h : 2 * (Fintype.card (OddOrbit G) : ℝ) + 1 = (Fintype.card G : ℝ) := by
    exact_mod_cast oddOrbit_card_identity (G := G) hodd
  linarith

/-- Actual P/Q pair count in a fixed tagged part of the one augmented
sample. This is an inverse-orbit count, not a vertex count. -/
def sampledPairCount (ω : FullSample G) (part : Fin 3) (kind : Bool) : ℕ :=
  (pairOrbitSet (fullLabels ω) part kind).card

/-- The exact pair-inventory center under the actual full sample law. -/
theorem sampledPairCount_expectation (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (part : Fin 3) (kind : Bool) :
    (∫ ω : FullSample G, (sampledPairCount ω part kind : ℝ)
      ∂fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) =
      (pairDensity p τ kind : ℝ) * ((Fintype.card G : ℝ)-1)/2 := by
  have hp := fullLabels_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ
  have hint : (∫ ω : FullSample G, categoricalPairCount part kind (fullLabels ω)
      ∂fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) =
      ∫ w : OddOrbit G → Label, categoricalPairCount part kind w ∂orbitMeasure p τ h := by
    rw [← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable
      (measurable_of_countable (categoricalPairCount part kind)).aestronglyMeasurable).symm
  change (∫ ω, categoricalPairCount part kind (fullLabels ω)
    ∂fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) = _
  rw [hint, categoricalPairCount_expectation, oddOrbit_card_real hodd]
  ring

/-- McDiarmid on the actual orbit labels, with variance proxy n/8. -/
theorem sampledPairCount_hasSubgaussianMGF (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (part : Fin 3) (kind : Bool) :
    HasSubgaussianMGF (fun ω : FullSample G =>
      (sampledPairCount ω part kind : ℝ) - (pairDensity p τ kind : ℝ) * ((Fintype.card G : ℝ)-1)/2)
      ((Fintype.card G : ℝ≥0)/8)
      (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) := by
  have hs := hasSubgaussianMGF_of_measurePreserving
    (fun _ : OddOrbit G => labelMeasure p τ h)
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)
    fullLabels (fullLabels_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ)
    (fun _ => 1) (categoricalPairCount part kind)
    (categoricalPairCount_boundedDifferences part kind)
  have hproxy : (∑ _o : OddOrbit G, ((1 : ℝ≥0)/2)^2) ≤ (Fintype.card G : ℝ≥0)/8 := by
    have hc : 2 * (Fintype.card (OddOrbit G) : ℝ) + 1 = (Fintype.card G : ℝ) := by
      exact_mod_cast oddOrbit_card_identity (G := G) hodd
    apply NNReal.coe_le_coe.mp
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast
    linarith
  have hw := proxy_mono hs hproxy
  change HasSubgaussianMGF (fun ω => (sampledPairCount ω part kind : ℝ) -
    ∫ ω : FullSample G, (sampledPairCount ω part kind : ℝ)
      ∂fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) _ _ at hw
  rw [sampledPairCount_expectation hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ] at hw
  exact hw

/-- The precise two-sided pair-inventory tail for one P/Q part, with the center
v(n-1)/2 and threshold vn/12. -/
theorem sampledPairCount_twoSided_tail (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (part : Fin 3) (kind : Bool) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | (pairDensity p τ kind : ℝ) * (Fintype.card G : ℝ)/12 <
        |(sampledPairCount ω part kind : ℝ) -
          (pairDensity p τ kind : ℝ)*((Fintype.card G : ℝ)-1)/2|} ≤
      2 * Real.exp (-(pairDensity p τ kind : ℝ)^2 * (Fintype.card G : ℝ)/36) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  let n : ℝ := Fintype.card G
  let v : ℝ := pairDensity p τ kind
  let X : FullSample G → ℝ := fun ω =>
    (sampledPairCount ω part kind : ℝ) - v*(n-1)/2
  let t : ℝ := v*n/12
  have ht : 0 ≤ t := by dsimp [t,v,n]; positivity
  have hs := sampledPairCount_hasSubgaussianMGF hodd q η a b hq0 hq1 hη0 hη1
    ha hb hab p τ h hP hQ part kind
  have hu : μ.real {ω | t ≤ X ω} ≤ Real.exp (-t^2/(2*(n/8))) := by
    simpa [μ,X,v,n] using hs.measure_ge_le ht
  have hl : μ.real {ω | t ≤ -X ω} ≤ Real.exp (-t^2/(2*(n/8))) := by
    simpa [μ,X,v,n] using hs.neg.measure_ge_le ht
  have hsub : {ω | t < |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    intro ω hω
    change t < |X ω| at hω
    change t ≤ X ω ∨ t ≤ -X ω
    rcases lt_abs.mp hω with hω | hω
    · exact Or.inl hω.le
    · exact Or.inr (by linarith)
  have hn0 : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  have hexp : -t^2/(2*(n/8)) = -v^2*n/36 := by
    dsimp [t]
    field_simp [hn0]
    ring
  calc
    μ.real {ω | t < |X ω|} ≤ μ.real ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) :=
      measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ -X ω} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-v^2*n/36) := by rw [hexp] at hu hl; linarith

/-- The common six-count event is fixed before every later numerical
forbidden set. No relation of independence between the counts is asserted. -/
def PairCountEvent (p τ : ℝ≥0) (ω : FullSample G) : Prop :=
  ∀ (part : Fin 3) (kind : Bool),
    |(sampledPairCount ω part kind : ℝ) -
      (pairDensity p τ kind : ℝ)*((Fintype.card G : ℝ)-1)/2| ≤
        (pairDensity p τ kind : ℝ) * (Fintype.card G : ℝ)/12

/-- Union of the six precise pair-inventory tails on the same full sample. -/
theorem pairCountEvent_failure_probability (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ PairCountEvent p τ ω} ≤
        6 * Real.exp (-(p : ℝ)^2 * (Fintype.card G : ℝ)/36) +
        6 * Real.exp (-(τ : ℝ)^2 * (Fintype.card G : ℝ)/36) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  let bad : (Fin 3 × Bool) → Set (FullSample G) := fun k =>
    {ω | ¬ |(sampledPairCount ω k.1 k.2 : ℝ) -
      (pairDensity p τ k.2 : ℝ)*((Fintype.card G : ℝ)-1)/2| ≤
        (pairDensity p τ k.2 : ℝ)*(Fintype.card G : ℝ)/12}
  have hevent : {ω : FullSample G | ¬ PairCountEvent p τ ω} = ⋃ k, bad k := by
    ext ω
    simp only [PairCountEvent, not_forall, Set.mem_iUnion, Set.mem_ofPred_eq, bad, Prod.exists]
  rw [hevent]
  calc
    μ.real (⋃ k, bad k) ≤ ∑ k, μ.real (bad k) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ k : Fin 3 × Bool,
        2 * Real.exp (-(pairDensity p τ k.2 : ℝ)^2 * (Fintype.card G : ℝ)/36) := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [bad, not_le] using sampledPairCount_twoSided_tail hodd q η a b hq0 hq1 hη0 hη1
        ha hb hab p τ h hP hQ k.1 k.2
    _ = _ := by simp [Fintype.sum_prod_type, pairDensity]; ring

/-- On the one count event, every part has the coarse linear inventory
bounds already at n≥6. The P assertion uses kind=false, the Q assertion
kind=true. This is before later numerical deletion. -/
theorem pairCountEvent_linear_bounds (p τ : ℝ≥0) (ω : FullSample G)
    (hevent : PairCountEvent p τ ω) (hn : 6 ≤ Fintype.card G)
    (part : Fin 3) (kind : Bool) :
    (pairDensity p τ kind : ℝ) * (Fintype.card G : ℝ)/3 ≤ (sampledPairCount ω part kind : ℝ) ∧
    (sampledPairCount ω part kind : ℝ) ≤ (pairDensity p τ kind : ℝ) * (Fintype.card G : ℝ) := by
  have hb := abs_le.mp (hevent part kind)
  have hv : 0 ≤ (pairDensity p τ kind : ℝ) := NNReal.coe_nonneg _
  have hn' : (6 : ℝ) ≤ (Fintype.card G : ℝ) := by exact_mod_cast hn
  have hslack := mul_nonneg hv (sub_nonneg.mpr hn')
  constructor <;> nlinarith

end
end EndpointPairInventoryCounts
