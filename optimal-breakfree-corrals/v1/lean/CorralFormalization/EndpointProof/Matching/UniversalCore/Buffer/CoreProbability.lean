import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.InventoryBudget
import CorralFormalization.EndpointProof.Matching.UniversalCore.PairCountInventory
import CorralFormalization.EndpointProof.Probability.SelectorSameSample
import CorralFormalization.EndpointProof.Probability.ExponentialMargin

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
open EndpointMatching.AbsorptionAssembly
open EndpointFullProduct EndpointOriginalReservoir
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Exact fixed-core conclusion on one augmented original sample. -/
def UniversalCoreEvent (τ : ℝ) (ω : FullSample G) : Prop :=
  ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
    ∃ A : Finset (Vertex G),
      (∀ v ∈ A, v.2 ≠ 0 ∧ signedMinus v.1 ω v.2) ∧
      Disjoint (support A) U ∧
      (A.card : ℝ) < 16200 * τ * (Fintype.card G : ℝ) ∧
      Balanced A ∧ (∑ v ∈ A, v.2 = 0) ∧
      AbsorbsUpTo A (quadraticCoreCapacity τ (Fintype.card G))

/-- Expand the integer capacity to the literal real-number hypotheses and
quantifier order used in the universal core result. -/
theorem universalCoreEvent_explicit_statement {τ : ℝ} {ω : FullSample G}
    (h : UniversalCoreEvent τ ω) :
    ∀ U : Finset G, (U.card : ℝ) ≤ (1 / 10^6 : ℝ) * τ^2 * Fintype.card G →
      ∃ A : Finset (Vertex G),
        (∀ v ∈ A, v.2 ≠ 0 ∧ signedMinus v.1 ω v.2) ∧
        Disjoint (support A) U ∧
        (A.card : ℝ) < 16200 * τ * (Fintype.card G : ℝ) ∧
        Balanced A ∧ (∑ v ∈ A, v.2 = 0) ∧
        ∀ S : Finset (Vertex G), (∀ v ∈ S, v.2 ≠ 0) → Balanced S →
          (∑ v ∈ S, v.2 = 0) → Disjoint A S →
          (S.card : ℝ) ≤ (1 / 10^6 : ℝ) * τ^2 * Fintype.card G →
          Nonempty (Matching (A ∪ S)) := by
  intro U hU
  have hU' : U.card ≤ quadraticCoreCapacity τ (Fintype.card G) := Nat.le_floor hU
  obtain ⟨A,hraw,havoid,hsize,hbalance,hsum,habs⟩ := h U hU'
  refine ⟨A,hraw,havoid,hsize,hbalance,hsum,?_⟩
  intro S hnonzero hbalanced hzero hdisjoint hS
  exact habs S hnonzero hbalanced hzero hdisjoint (Nat.le_floor hS)

/-- A good common-sample core event supplies the actual raw-minus receiver
directly. No new P, Q, graph, or buffer hypotheses are introduced. -/
theorem universalCoreEvent_rawCoreSupply {τ : ℝ} {ω : FullSample G}
    (h : UniversalCoreEvent τ ω) :
    RawCoreSupply (nonzeroRawMinus ω) (quadraticCoreCapacity τ (Fintype.card G))
      ⌊16200 * τ * (Fintype.card G : ℝ)⌋₊ := by
  intro U hU
  obtain ⟨A,hraw,havoid,hsize,_,_,habs⟩ := h U hU
  refine ⟨A,?_,?_,?_,habs⟩
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hraw v hv⟩
  · exact havoid.mono_left Finset.subset_union_left
  · exact Nat.le_floor (le_of_lt hsize)

def OriginalAdmitsUniversalCore (τ : ℝ) (s : OriginalSample G) : Prop :=
  ∃ ω : FullSample G, originalProcess ω = s ∧ UniversalCoreEvent τ ω

/-- The deterministic common-sample composition with explicit P-selector
and Q-inventory probability bounds. The tetrahedron and buffer tails are
proved, and no independence among these three events is used. -/
theorem universalCore_failure_probability_of_component_tails
    (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (hτ : 0 < (τ : ℝ)) (hτmax : (τ : ℝ) ≤ 1 / 3)
    (hτp : (τ : ℝ) ≤ (p : ℝ)^4 / 10^30)
    (hn : 1152 ≤ Fintype.card G)
    (hnlarge : (4000 : ℝ) ≤ (τ : ℝ)^2 * Fintype.card G)
    (eP eI : ℝ)
    (hPtail : (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ ColouredSelectors ω (selectorExternalBudget (p : ℝ) (Fintype.card G))} ≤ eP)
    (hItail : (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ InventoryBounds (τ : ℝ) ω} ≤ eI) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ UniversalCoreEvent (τ : ℝ) ω} ≤
      eP + eI +
      (Fintype.card G : ℝ)^6 * Real.exp (-(τ : ℝ)^24 * (Fintype.card G : ℝ) / 2304) +
        6 * (Fintype.card G : ℝ)^7 * Real.exp (-(τ : ℝ)^20 * (Fintype.card G : ℝ) / 100) +
      Real.exp (-(τ : ℝ)^6 * (Fintype.card G : ℝ) / 144) +
        3 * (Fintype.card G : ℝ) * Real.exp (-(τ : ℝ)^4 * (Fintype.card G : ℝ) / 4) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  let Pbad : Set (FullSample G) := {ω |
    ¬ ColouredSelectors ω (selectorExternalBudget (p : ℝ) (Fintype.card G))}
  let Ibad : Set (FullSample G) := {ω | ¬ InventoryBounds (τ : ℝ) ω}
  let Qbad : Set (FullSample G) := {ω | ¬ Buffer.CoreConstructionEvent (τ : ℝ) ω}
  have hsub : {ω | ¬ UniversalCoreEvent (τ : ℝ) ω} ⊆ Pbad ∪ Ibad ∪ Qbad := by
    intro ω hbad
    by_contra hnot
    have hp : ColouredSelectors ω (selectorExternalBudget (p : ℝ) (Fintype.card G)) := by
      by_contra hp
      exact hnot (Or.inl (Or.inl hp))
    have hi : InventoryBounds (τ : ℝ) ω := by
      by_contra hi
      exact hnot (Or.inl (Or.inr hi))
    have hq : Buffer.CoreConstructionEvent (τ : ℝ) ω := by
      by_contra hq
      exact hnot (Or.inr hq)
    exact hbad (explicit_universal_core_of_events ω (τ : ℝ) (p : ℝ) hτ hτmax hτp
      hodd hnlarge hq hp hi)
  have hQtail := Buffer.explicitQEvent_failure_probability hodd q η a b hq0 hq1 hη0 hη1
    ha hb hab p τ h hP hQ hτ hτmax hn hnlarge
  have hunion : μ.real (Pbad ∪ Ibad ∪ Qbad) ≤ μ.real Pbad + μ.real Ibad + μ.real Qbad := by
    have h1 := measureReal_union_le (μ := μ) (Pbad ∪ Ibad) Qbad
    have h2 := measureReal_union_le (μ := μ) Pbad Ibad
    linarith
  have hres := (measureReal_mono hsub (measure_ne_top μ _)).trans hunion
  linarith

/-- Projecting the same good augmentation gives the corresponding bound
for the original categorical sample; no new augmentation is chosen per U. -/
theorem originalCore_failure_probability_of_component_tails
    (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (hτ : 0 < (τ : ℝ)) (hτmax : (τ : ℝ) ≤ 1 / 3)
    (hτp : (τ : ℝ) ≤ (p : ℝ)^4 / 10^30)
    (hn : 1152 ≤ Fintype.card G)
    (hnlarge : (4000 : ℝ) ≤ (τ : ℝ)^2 * Fintype.card G)
    (eP eI : ℝ)
    (hPtail : (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ ColouredSelectors ω (selectorExternalBudget (p : ℝ) (Fintype.card G))} ≤ eP)
    (hItail : (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ InventoryBounds (τ : ℝ) ω} ≤ eI) :
    (originalMeasure (G := G) q hq0 hq1).real
      {s | ¬ OriginalAdmitsUniversalCore (τ : ℝ) s} ≤
      eP + eI +
      (Fintype.card G : ℝ)^6 * Real.exp (-(τ : ℝ)^24 * (Fintype.card G : ℝ) / 2304) +
        6 * (Fintype.card G : ℝ)^7 * Real.exp (-(τ : ℝ)^20 * (Fintype.card G : ℝ) / 100) +
      Real.exp (-(τ : ℝ)^6 * (Fintype.card G : ℝ) / 144) +
        3 * (Fintype.card G : ℝ) * Real.exp (-(τ : ℝ)^4 * (Fintype.card G : ℝ) / 4) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  have hp := originalProcess_measurePreserving (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  rw [← hp.measureReal_preimage (by measurability)]
  apply (measureReal_mono ?_ (measure_ne_top μ _)).trans
    (universalCore_failure_probability_of_component_tails hodd q η a b hq0 hq1 hη0 hη1
      ha hb hab p τ h hP hQ hτ hτmax hτp hn hnlarge eP eI hPtail hItail)
  intro ω hbad hgood
  exact hbad ⟨ω,rfl,hgood⟩

/-- The six proved P/Q pair-count tails remove the inventory-error
assumption. Only the same-sample P-selector tail remains to be supplied. -/
theorem originalCore_failure_probability_of_selector_tail
    (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (hτ : 0 < (τ : ℝ)) (hτmax : (τ : ℝ) ≤ 1 / 3)
    (hτp : (τ : ℝ) ≤ (p : ℝ)^4 / 10^30)
    (hn : 1152 ≤ Fintype.card G)
    (hnlarge : (4000 : ℝ) ≤ (τ : ℝ)^2 * Fintype.card G)
    (eP : ℝ)
    (hPtail : (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ ColouredSelectors ω (selectorExternalBudget (p : ℝ) (Fintype.card G))} ≤ eP) :
    (originalMeasure (G := G) q hq0 hq1).real
      {s | ¬ OriginalAdmitsUniversalCore (τ : ℝ) s} ≤
      eP + (6 * Real.exp (-(p : ℝ)^2 * (Fintype.card G : ℝ)/36) +
        6 * Real.exp (-(τ : ℝ)^2 * (Fintype.card G : ℝ)/36)) +
      (Fintype.card G : ℝ)^6 * Real.exp (-(τ : ℝ)^24 * (Fintype.card G : ℝ) / 2304) +
        6 * (Fintype.card G : ℝ)^7 * Real.exp (-(τ : ℝ)^20 * (Fintype.card G : ℝ) / 100) +
      Real.exp (-(τ : ℝ)^6 * (Fintype.card G : ℝ) / 144) +
        3 * (Fintype.card G : ℝ) * Real.exp (-(τ : ℝ)^4 * (Fintype.card G : ℝ) / 4) := by
  have hItail : (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ InventoryBounds (τ : ℝ) ω} ≤
      6 * Real.exp (-(p : ℝ)^2 * (Fintype.card G : ℝ)/36) +
        6 * Real.exp (-(τ : ℝ)^2 * (Fintype.card G : ℝ)/36) := by
    change (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ QPairInventoryEvent (τ : ℝ) ω} ≤ _
    exact qInventoryEvent_failure_probability hodd q η a b hq0 hq1 hη0 hη1 ha hb hab
      p τ h hP hQ (by omega)
  exact originalCore_failure_probability_of_component_tails hodd q η a b hq0 hq1 hη0 hη1
    ha hb hab p τ h hP hQ hτ hτmax hτp hn hnlarge eP _ hPtail hItail

/-- The complete explicit union bound at the literal sampling
parameters. No selector, inventory, graph, buffer, or concentration
existence assumption remains. -/
theorem originalCore_explicit_failure_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (hodd : Odd (Fintype.card G))
    (hn : 1152 ≤ Fintype.card G)
    (hnlarge : (4000 : ℝ) ≤ (tau q)^2 * Fintype.card G)
    (hsel : selectorSameSampleThreshold q ≤ Fintype.card G) :
    (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
      {s | ¬ OriginalAdmitsUniversalCore (tau q) s} ≤
      24 * (Fintype.card G : ℝ)^3 * Real.exp (-((p q)^8 / 32000) * (Fintype.card G : ℝ)) +
      (6 * Real.exp (-(p q)^2 * (Fintype.card G : ℝ)/36) +
        6 * Real.exp (-(tau q)^2 * (Fintype.card G : ℝ)/36)) +
      (Fintype.card G : ℝ)^6 * Real.exp (-(tau q)^24 * (Fintype.card G : ℝ) / 2304) +
        6 * (Fintype.card G : ℝ)^7 * Real.exp (-(tau q)^20 * (Fintype.card G : ℝ) / 100) +
      Real.exp (-(tau q)^6 * (Fintype.card G : ℝ) / 144) +
        3 * (Fintype.card G : ℝ) * Real.exp (-(tau q)^4 * (Fintype.card G : ℝ) / 4) := by
  obtain ⟨hη0,hη1,ha,hb,hab,hp,hcat,hP,hQ⟩ := samplingParameters_admissible q hq0 hq1
  have hτ : 0 < (tauNN q : ℝ) := by
    change 0 < tau q
    unfold tau p SamplingConstants.rho eta
    positivity
  have hcat' : 3 * (pNN q : ℝ) + 3 * (tauNN q : ℝ) ≤ 1 := by exact_mod_cast hcat
  have hτmax : (tauNN q : ℝ) ≤ 1 / 3 := by nlinarith [NNReal.coe_nonneg (pNN q)]
  have hτp : (tauNN q : ℝ) ≤ (pNN q : ℝ)^4 / 10^30 := by
    change tau q ≤ (p q)^4 / 10^30
    unfold tau
    ring_nf
    exact le_rfl
  have hPtail := selector_same_sample_external_error_of_threshold q hq0 hq1 hodd hsel
  have hPtail' : (fullMeasure (G := G) q eta (1/4) (tau q / SamplingConstants.rho q)
      (le_of_lt hq0) hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ ColouredSelectors ω (selectorExternalBudget (pNN q : ℝ) (Fintype.card G))} ≤
      24 * (Fintype.card G : ℝ)^3 * Real.exp (-((p q)^8 / 32000) * (Fintype.card G : ℝ)) := by
    have hpNN : (pNN q : ℝ) = p q := rfl
    rw [hpNN]
    simpa only [parameterizedFullMeasure] using hPtail
  have hresult := originalCore_failure_probability_of_selector_tail hodd q eta (1/4)
    (tau q / SamplingConstants.rho q)
    (le_of_lt hq0) hq1 hη0 hη1 ha hb hab (pNN q) (tauNN q) hcat hP hQ hτ hτmax hτp
    hn hnlarge _ hPtail'
  exact hresult

end
end EndpointMatching.UniversalCore
