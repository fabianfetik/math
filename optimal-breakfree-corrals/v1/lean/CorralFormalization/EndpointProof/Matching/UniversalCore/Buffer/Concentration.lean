import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.Sections
import CorralFormalization.EndpointProof.Flow.Tetrahedron.Concentration

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
namespace EndpointMatching.UniversalCore.Buffer
open EndpointFlow.AbelianTransport
open EndpointFullProduct EndpointOriginalReservoir EndpointBlockAvailability
open EndpointSharedSample EndpointReservoirAvailability EndpointFiniteProductConcentration
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

def categoricalTotalCount (w : OddOrbit G → Label) : ℝ :=
  (goodCandidates (EndpointMatching.Tetrahedron.categoricalQ w)).card

def categoricalSectionCount (i : Fin 3) (g : G) (w : OddOrbit G → Label) : ℝ :=
  (sectionMajorant (EndpointMatching.Tetrahedron.categoricalQ w) i g).card

theorem categoricalTotalCount_boundedDifferences :
    CoordinateBoundedDifferences (categoricalTotalCount (G := G))
      (fun _ => 6 * (Fintype.card G : ℝ≥0)) := by
  intro o w w' hw
  exact goodCandidates_count_change_le (EndpointMatching.Tetrahedron.categoricalQ w)
    (EndpointMatching.Tetrahedron.categoricalQ w') (orbitPlace (o,false))
    (EndpointMatching.Tetrahedron.categoricalQ_agrees_off_orbit w w' o hw)

theorem categoricalSectionCount_boundedDifferences (i : Fin 3) (g : G) :
    CoordinateBoundedDifferences (categoricalSectionCount i g) (fun _ => 4) := by
  intro o w w' hw
  exact sectionMajorant_count_change_le (EndpointMatching.Tetrahedron.categoricalQ w)
    (EndpointMatching.Tetrahedron.categoricalQ w') i g (orbitPlace (o,false))
    (EndpointMatching.Tetrahedron.categoricalQ_agrees_off_orbit w w' o hw)

theorem total_varianceProxy_le :
    (∑ _o : OddOrbit G, ((6 * (Fintype.card G : ℝ≥0)) / 2)^2) ≤
      (9 / 2 : ℝ≥0) * (Fintype.card G : ℝ≥0)^3 := by
  have hm : 2 * (Fintype.card (OddOrbit G) : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast EndpointMatching.Tetrahedron.oddOrbit_twice_card_le (G := G)
  apply NNReal.coe_le_coe.mp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  have hp := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ (9 / 2 : ℝ) * (Fintype.card G : ℝ)^2 by positivity)
  nlinarith only [hp]

theorem section_varianceProxy_le :
    (∑ _o : OddOrbit G, ((4 : ℝ≥0) / 2)^2) ≤ 2 * (Fintype.card G : ℝ≥0) := by
  have hm : 2 * (Fintype.card (OddOrbit G) : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast EndpointMatching.Tetrahedron.oddOrbit_twice_card_le (G := G)
  apply NNReal.coe_le_coe.mp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  nlinarith only [hm]

theorem goodCandidates_hasSubgaussianMGF (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b) :
    HasSubgaussianMGF (fun ω : FullSample G =>
      ((goodCandidates (ReservoirVertex ω true)).card : ℝ) -
        ∫ ω : FullSample G, ((goodCandidates (ReservoirVertex ω true)).card : ℝ)
          ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab))
      ((9 / 2 : ℝ≥0) * (Fintype.card G : ℝ≥0)^3)
      (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) := by
  have hs := hasSubgaussianMGF_of_measurePreserving
    (fun _ : OddOrbit G => labelMeasure p τ h)
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)
    fullLabels (fullLabels_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ)
    (fun _ => 6 * (Fintype.card G : ℝ≥0))
    categoricalTotalCount categoricalTotalCount_boundedDifferences
  have hw := proxy_mono hs (total_varianceProxy_le (G := G))
  simpa only [categoricalTotalCount, EndpointMatching.Tetrahedron.categoricalQ_fullLabels] using hw

theorem sectionMajorant_hasSubgaussianMGF (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (i : Fin 3) (g : G) :
    HasSubgaussianMGF (fun ω : FullSample G =>
      ((sectionMajorant (ReservoirVertex ω true) i g).card : ℝ) -
        ∫ ω : FullSample G, ((sectionMajorant (ReservoirVertex ω true) i g).card : ℝ)
          ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab))
      (2 * (Fintype.card G : ℝ≥0))
      (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) := by
  have hs := hasSubgaussianMGF_of_measurePreserving
    (fun _ : OddOrbit G => labelMeasure p τ h)
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)
    fullLabels (fullLabels_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ)
    (fun _ => 4) (categoricalSectionCount i g) (categoricalSectionCount_boundedDifferences i g)
  have hw := proxy_mono hs (section_varianceProxy_le (G := G))
  simpa only [categoricalSectionCount, EndpointMatching.Tetrahedron.categoricalQ_fullLabels] using hw

/-- The paper's total-buffer lower tail, on the original shared sample. -/
theorem goodCandidates_lower_tail (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (hn : 24 ≤ Fintype.card G) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ((goodCandidates (ReservoirVertex ω true)).card : ℝ) <
        (τ : ℝ)^3 * (Fintype.card G : ℝ)^2 / 2} ≤
      Real.exp (-(τ : ℝ)^6 * (Fintype.card G : ℝ) / 144) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  let n : ℝ := Fintype.card G
  let f : FullSample G → ℝ := fun ω => (goodCandidates (ReservoirVertex ω true)).card
  let m : ℝ := ∫ ω, f ω ∂μ
  let t : ℝ := (τ : ℝ)^3 * n^2 / 4
  have ht : 0 ≤ t := by dsimp [t,n]; positivity
  have hm : (3/4 : ℝ) * (τ : ℝ)^3 * n^2 ≤ m :=
    goodCandidates_expectation_three_quarters hodd q η a b hq0 hq1 hη0 hη1
      ha hb hab p τ h hP hQ hn
  have hsg := goodCandidates_hasSubgaussianMGF hodd q η a b hq0 hq1 hη0 hη1
    ha hb hab p τ h hP hQ
  have htail : μ.real {ω | t ≤ m-f ω} ≤ Real.exp (-t^2 / (9*n^3)) := by
    convert hsg.neg.measure_ge_le ht using 1 <;> norm_num [μ,f,m,n]
    all_goals ring
  have hsub : {ω | f ω < (τ : ℝ)^3 * n^2 / 2} ⊆ {ω | t ≤ m-f ω} := by
    intro ω hω
    change f ω < (τ : ℝ)^3 * n^2 / 2 at hω
    change t ≤ m-f ω
    dsimp only [t]
    nlinarith only [hm,hω]
  have hn0 : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  have hexp : -t^2 / (9*n^3) = -(τ : ℝ)^6 * n / 144 := by
    dsimp [t]
    field_simp [hn0]
    ring
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans (hexp ▸ htail)

/-- The two-active-label section majorant has the paper's upper tail. -/
theorem sectionMajorant_upper_tail (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (i : Fin 3) (g : G) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | 2 * (τ : ℝ)^2 * (Fintype.card G : ℝ) <
        ((sectionMajorant (ReservoirVertex ω true) i g).card : ℝ)} ≤
      Real.exp (-(τ : ℝ)^4 * (Fintype.card G : ℝ) / 4) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  let n : ℝ := Fintype.card G
  let f : FullSample G → ℝ := fun ω => (sectionMajorant (ReservoirVertex ω true) i g).card
  let m : ℝ := ∫ ω, f ω ∂μ
  let t : ℝ := (τ : ℝ)^2 * n
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hm : m ≤ (τ : ℝ)^2 * n :=
    sectionMajorant_expectation_le hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ i g
  have hsg := sectionMajorant_hasSubgaussianMGF hodd q η a b hq0 hq1 hη0 hη1
    ha hb hab p τ h hP hQ i g
  have htail : μ.real {ω | t ≤ f ω-m} ≤ Real.exp (-t^2 / (4*n)) := by
    convert hsg.measure_ge_le ht using 1
    all_goals norm_num [μ,f,m,n]
    all_goals ring
  have hsub : {ω | 2 * (τ : ℝ)^2 * n < f ω} ⊆ {ω | t ≤ f ω-m} := by
    intro ω hω
    change 2 * (τ : ℝ)^2 * n < f ω at hω
    change t ≤ f ω-m
    dsimp only [t]
    nlinarith only [hm,hω]
  have hn0 : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  have hexp : -t^2 / (4*n) = -(τ : ℝ)^4 * n / 4 := by
    dsimp [t]
    field_simp [hn0]
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans (hexp ▸ htail)

theorem goodSection_upper_tail (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (i : Fin 3) (g : G) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | 2 * (τ : ℝ)^2 * (Fintype.card G : ℝ) <
        (((goodCandidates (ReservoirVertex ω true)).filter (fun t => coordinate t i = g)).card : ℝ)} ≤
      Real.exp (-(τ : ℝ)^4 * (Fintype.card G : ℝ) / 4) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  have hsub : {ω : FullSample G | 2 * (τ : ℝ)^2 * (Fintype.card G : ℝ) <
        (((goodCandidates (ReservoirVertex ω true)).filter (fun t => coordinate t i = g)).card : ℝ)} ⊆
      {ω | 2 * (τ : ℝ)^2 * (Fintype.card G : ℝ) <
        ((sectionMajorant (ReservoirVertex ω true) i g).card : ℝ)} := by
    intro ω hω
    have hc : (((goodCandidates (ReservoirVertex ω true)).filter
        (fun t => coordinate t i = g)).card : ℝ) ≤
        ((sectionMajorant (ReservoirVertex ω true) i g).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (goodSection_subset_majorant (ReservoirVertex ω true) i g)
    exact lt_of_lt_of_le hω hc
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    (sectionMajorant_upper_tail hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ i g)

/-- One sample satisfies the total and all 3n section estimates. -/
def CountEvent (τ : ℝ) (ω : FullSample G) : Prop :=
  τ^3 * (Fintype.card G : ℝ)^2 / 2 ≤
      ((goodCandidates (ReservoirVertex ω true)).card : ℝ) ∧
  ∀ i : Fin 3, ∀ g : G,
    (((goodCandidates (ReservoirVertex ω true)).filter (fun t => coordinate t i = g)).card : ℝ) ≤
      2 * τ^2 * (Fintype.card G : ℝ)

/-- The total and all 3n buffer section tails hold on one sample; the
correlated bad events are combined only by a finite union bound. -/
theorem countEvent_failure_probability (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (hn : 24 ≤ Fintype.card G) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ CountEvent (τ : ℝ) ω} ≤
      Real.exp (-(τ : ℝ)^6 * (Fintype.card G : ℝ) / 144) +
        3 * (Fintype.card G : ℝ) * Real.exp (-(τ : ℝ)^4 * (Fintype.card G : ℝ) / 4) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  let n : ℝ := Fintype.card G
  let u : ℝ := Real.exp (-(τ : ℝ)^6 * n / 144)
  let v : ℝ := Real.exp (-(τ : ℝ)^4 * n / 4)
  let totalBad : Set (FullSample G) := {ω |
    ((goodCandidates (ReservoirVertex ω true)).card : ℝ) < (τ : ℝ)^3 * n^2 / 2}
  let sectionBad : Set (FullSample G) := ⋃ i : Fin 3, ⋃ g : G, {ω |
    2 * (τ : ℝ)^2 * n <
      (((goodCandidates (ReservoirVertex ω true)).filter (fun t => coordinate t i = g)).card : ℝ)}
  have hsub : {ω | ¬ CountEvent (τ : ℝ) ω} ⊆ totalBad ∪ sectionBad := by
    intro ω hbad
    by_contra hnot
    have ht : (τ : ℝ)^3 * n^2 / 2 ≤ ((goodCandidates (ReservoirVertex ω true)).card : ℝ) := by
      by_contra ht
      exact hnot (Or.inl (by simpa [totalBad] using (lt_of_not_ge ht)))
    have hs : ∀ i : Fin 3, ∀ g : G,
        (((goodCandidates (ReservoirVertex ω true)).filter (fun t => coordinate t i = g)).card : ℝ) ≤
          2 * (τ : ℝ)^2 * n := by
      intro i g
      by_contra hs
      apply hnot
      right
      exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨g,by simpa using (lt_of_not_ge hs)⟩⟩
    apply hbad
    exact ⟨ht,hs⟩
  have ht : μ.real totalBad ≤ u := by
    exact goodCandidates_lower_tail hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ hn
  have hs : μ.real sectionBad ≤ 3 * n * v := by
    calc
      μ.real sectionBad ≤ ∑ i : Fin 3, μ.real (⋃ g : G, {ω |
          2 * (τ : ℝ)^2 * n <
            (((goodCandidates (ReservoirVertex ω true)).filter
              (fun t => coordinate t i = g)).card : ℝ)}) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ i : Fin 3, ∑ g : G, μ.real {ω |
          2 * (τ : ℝ)^2 * n <
            (((goodCandidates (ReservoirVertex ω true)).filter
              (fun t => coordinate t i = g)).card : ℝ)} := by
        apply Finset.sum_le_sum
        intro i _
        exact measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin 3, ∑ _g : G, v := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro g _
        exact goodSection_upper_tail hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ i g
      _ = 3 * n * v := by simp [n]; ring
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add ht hs))

end
end EndpointMatching.UniversalCore.Buffer
