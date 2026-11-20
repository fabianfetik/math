import CorralFormalization.EndpointProof.Flow.Tetrahedron.Concentration

/-!
The fixed-root and section tails with the constants, and their finite
union through the already proved deletion interface. No concentration
statement is postulated as an extra assumption.
-/

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

/-- PC4a for one admissible six-root query. The total is the actual
successful-candidate count, and n≥1152 is exactly the valid-count threshold. -/
theorem goodCandidates_lower_tail (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (r : TetrahedronRoots G) (hr : admissibleRoots r) (hn : 1152 ≤ Fintype.card G) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ((goodCandidates (ReservoirVertex ω true) r).card : ℝ) <
        (τ : ℝ)^12 * (Fintype.card G : ℝ)^3 / 2} ≤
      Real.exp (-(τ : ℝ)^24 * (Fintype.card G : ℝ) / 2304) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  let n : ℝ := Fintype.card G
  let f : FullSample G → ℝ := fun ω => (goodCandidates (ReservoirVertex ω true) r).card
  let m : ℝ := ∫ ω, f ω ∂μ
  let t : ℝ := (τ : ℝ)^12 * n^3 / 4
  have ht : 0 ≤ t := by dsimp [t,n]; positivity
  have hm : (3/4 : ℝ) * (τ : ℝ)^12 * n^3 ≤ m :=
    goodCandidates_expectation_lower hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ r hr hn
  have hsg := goodCandidates_hasSubgaussianMGF hodd q η a b hq0 hq1 hη0 hη1
    ha hb hab p τ h hP hQ r
  have htail : μ.real {ω | t ≤ m-f ω} ≤ Real.exp (-t^2 / (144*n^5)) := by
    have hs := hsg.neg.measure_ge_le ht
    norm_num [← mul_assoc] at hs
    simpa [μ, f, m, n] using hs
  have hsub : {ω | f ω < (τ : ℝ)^12 * n^3 / 2} ⊆ {ω | t ≤ m-f ω} := by
    intro ω hω
    change f ω < (τ : ℝ)^12 * n^3 / 2 at hω
    change t ≤ m-f ω
    dsimp only [t]
    nlinarith only [hm,hω]
  have hn0 : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  have hexp : -t^2 / (144*n^5) = -(τ : ℝ)^24 * n / 2304 := by
    dsimp [t]
    field_simp [hn0]
    ring
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans (hexp ▸ htail)

/-- Upper tail for the same ten-active-label majorant as the checked mean
and sensitivity estimates. The two constant tests have been omitted. -/
theorem validReducedSection_upper_tail (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | 2 * (τ : ℝ)^10 * (Fintype.card G : ℝ)^2 <
        ((validReducedSection (ReservoirVertex ω true) r i g).card : ℝ)} ≤
      Real.exp (-(τ : ℝ)^20 * (Fintype.card G : ℝ) / 100) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  let n : ℝ := Fintype.card G
  let f : FullSample G → ℝ := fun ω =>
    (validReducedSection (ReservoirVertex ω true) r i g).card
  let m : ℝ := ∫ ω, f ω ∂μ
  let t : ℝ := (τ : ℝ)^10 * n^2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hm : m ≤ (τ : ℝ)^10 * n^2 :=
    validReducedSection_expectation_le hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ r i g
  have hsg := validReducedSection_hasSubgaussianMGF hodd q η a b hq0 hq1 hη0 hη1
    ha hb hab p τ h hP hQ r i g
  have htail : μ.real {ω | t ≤ f ω-m} ≤ Real.exp (-t^2 / (100*n^3)) := by
    have hs := hsg.measure_ge_le ht
    norm_num [← mul_assoc] at hs
    simpa [μ, f, m, n] using hs
  have hsub : {ω | 2 * (τ : ℝ)^10 * n^2 < f ω} ⊆ {ω | t ≤ f ω-m} := by
    intro ω hω
    change 2 * (τ : ℝ)^10 * n^2 < f ω at hω
    change t ≤ f ω-m
    dsimp only [t]
    nlinarith only [hm,hω]
  have hn0 : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  have hexp : -t^2 / (100*n^3) = -(τ : ℝ)^20 * n / 100 := by
    dsimp [t]
    field_simp [hn0]
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans (hexp ▸ htail)

/-- The actual successful-section count is bounded by its ten-label
majorant, so it inherits the same section upper tail. -/
theorem goodCandidates_section_upper_tail (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | 2 * (τ : ℝ)^10 * (Fintype.card G : ℝ)^2 <
        (((goodCandidates (ReservoirVertex ω true) r).filter
          (fun t => tetrahedronDirection i t = g)).card : ℝ)} ≤
      Real.exp (-(τ : ℝ)^20 * (Fintype.card G : ℝ) / 100) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  have hsub : {ω : FullSample G | 2 * (τ : ℝ)^10 * (Fintype.card G : ℝ)^2 <
        (((goodCandidates (ReservoirVertex ω true) r).filter
          (fun t => tetrahedronDirection i t = g)).card : ℝ)} ⊆
      {ω | 2 * (τ : ℝ)^10 * (Fintype.card G : ℝ)^2 <
        ((validReducedSection (ReservoirVertex ω true) r i g).card : ℝ)} := by
    intro ω hω
    have hc : (((goodCandidates (ReservoirVertex ω true) r).filter
        (fun t => tetrahedronDirection i t = g)).card : ℝ) ≤
        ((validReducedSection (ReservoirVertex ω true) r i g).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (goodSection_subset_validReduced ω r i g)
    exact lt_of_lt_of_le hω hc
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    (validReducedSection_upper_tail hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ r i g)

/-- A single event supplies all later admissible six-root queries and all
forbidden sets within the paper's τ²n/192 numerical budget. The displayed
failure bound is the finite union of the now proved fixed-query tails. -/
theorem parameters_failure_probability (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (hτ : 0 < (τ : ℝ)) (hn : 1152 ≤ Fintype.card G)
    (budget : ℕ) (hbudget : (budget : ℝ) ≤ (τ : ℝ)^2 * (Fintype.card G : ℝ) / 192) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ TetrahedronParametersAvailable (ReservoirVertex ω true) budget} ≤
      (Fintype.card (AdmissibleRootQuery G) : ℝ) *
        Real.exp (-(τ : ℝ)^24 * (Fintype.card G : ℝ) / 2304) +
      (Fintype.card (AdmissibleRootQuery G) : ℝ) * 6 * (Fintype.card G : ℝ) *
        Real.exp (-(τ : ℝ)^20 * (Fintype.card G : ℝ) / 100) := by
  apply parameters_probability_of_count_tails
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)
    (fun ω => ReservoirVertex ω true) (τ : ℝ) (Fintype.card G : ℝ)
    (Real.exp (-(τ : ℝ)^24 * (Fintype.card G : ℝ) / 2304))
    (Real.exp (-(τ : ℝ)^20 * (Fintype.card G : ℝ) / 100))
    budget hτ (by positivity) hbudget
  · intro rq
    simpa only [not_le] using goodCandidates_lower_tail hodd q η a b hq0 hq1 hη0 hη1
      ha hb hab p τ h hP hQ (queryRoots rq) rq.2 hn
  · intro rq i g
    simpa only [not_le] using goodCandidates_section_upper_tail hodd q η a b hq0 hq1 hη0 hη1
      ha hb hab p τ h hP hQ (queryRoots rq) i g

/-- The same all-roots/all-forbidden-sets bound with the paper's coarse
query counts n⁶ and 6n⁷. No union over the later forbidden sets occurs. -/
theorem parameters_failure_probability_le (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (hτ : 0 < (τ : ℝ)) (hn : 1152 ≤ Fintype.card G)
    (budget : ℕ) (hbudget : (budget : ℝ) ≤ (τ : ℝ)^2 * (Fintype.card G : ℝ) / 192) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ TetrahedronParametersAvailable (ReservoirVertex ω true) budget} ≤
      (Fintype.card G : ℝ)^6 * Real.exp (-(τ : ℝ)^24 * (Fintype.card G : ℝ) / 2304) +
        6 * (Fintype.card G : ℝ)^7 * Real.exp (-(τ : ℝ)^20 * (Fintype.card G : ℝ) / 100) := by
  have hc : (Fintype.card (AdmissibleRootQuery G) : ℝ) ≤ (Fintype.card G : ℝ)^6 := by
    exact_mod_cast admissibleRootQuery_card_le (G := G)
  apply (parameters_failure_probability hodd q η a b hq0 hq1 hη0 hη1 ha hb hab
    p τ h hP hQ hτ hn budget hbudget).trans
  calc
    _ ≤ (Fintype.card G : ℝ)^6 * Real.exp (-(τ : ℝ)^24 * (Fintype.card G : ℝ) / 2304) +
        (Fintype.card G : ℝ)^6 * 6 * (Fintype.card G : ℝ) *
          Real.exp (-(τ : ℝ)^20 * (Fintype.card G : ℝ) / 100) := by gcongr
    _ = _ := by ring

end
end EndpointMatching.Tetrahedron
