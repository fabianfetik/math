import CorralFormalization.EndpointProof.Probability.FiniteProductConcentration
import CorralFormalization.EndpointProof.Flow.Tetrahedron.SectionExpectation

/-!
Concentration of the actual tetrahedron counts. `categoricalQ` reads the
same seven-valued independent inverse-orbit labels as `fullLabels`; the
identity with `ReservoirVertex` is pointwise on every original augmented
sample. The only probabilistic premises are the explicit categorical laws.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal

namespace EndpointMatching.Tetrahedron
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointFullProduct EndpointOriginalReservoir EndpointBlockAvailability
open EndpointSharedSample EndpointReservoirAvailability
open EndpointFiniteProductConcentration
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Read Q membership from the actual seven-valued inverse-orbit labels. -/
def categoricalQ (w : OddOrbit G → Label) (v : Vertex G) : Prop :=
  ∃ (o : OddOrbit G) (side : Bool), orbitPlace (o,side) = v.2 ∧
    w o = encodeChild (some (v.1,true))

/-- This categorical function is exactly the Q reservoir of the single
actual augmented sample; no replacement sample is introduced. -/
theorem categoricalQ_fullLabels (ω : FullSample G) :
    categoricalQ (fullLabels ω) = ReservoirVertex ω true := by
  funext v
  apply propext
  simp only [categoricalQ, ReservoirVertex, fullLabels, sevenLabel,
    encodeChild_bijective.injective.eq_iff]

/-- Labels outside one orbit determine all tagged Q memberships outside
its two numerical signs. -/
theorem categoricalQ_agrees_off_orbit (w w' : OddOrbit G → Label) (o : OddOrbit G)
    (hw : ∀ j, j ≠ o → w j = w' j) :
    ∀ v : Vertex G, v.2 ≠ orbitPlace (o,false) →
      v.2 ≠ -orbitPlace (o,false) → (categoricalQ w v ↔ categoricalQ w' v) := by
  intro v hv hvneg
  have ho (j : OddOrbit G) (side : Bool) (hj : orbitPlace (j,side) = v.2) : j ≠ o := by
    intro he
    subst j
    cases side with
    | false => exact hv hj.symm
    | true => exact hvneg (hj.symm.trans (by simpa using orbitPlace_neg o false))
  constructor
  · rintro ⟨j,side,hj,hl⟩
    exact ⟨j,side,hj,(hw j (ho j side hj)).symm.trans hl⟩
  · rintro ⟨j,side,hj,hl⟩
    exact ⟨j,side,hj,(hw j (ho j side hj)).trans hl⟩

def categoricalTotalCount (r : TetrahedronRoots G) (w : OddOrbit G → Label) : ℝ :=
  (goodCandidates (categoricalQ w) r).card

def categoricalSectionCount (r : TetrahedronRoots G) (i : Fin 6) (g : G)
    (w : OddOrbit G → Label) : ℝ :=
  (validReducedSection (categoricalQ w) r i g).card

/-- The total count has the paper's 24 n² coordinate oscillation. -/
theorem categoricalTotalCount_boundedDifferences (r : TetrahedronRoots G) :
    CoordinateBoundedDifferences (categoricalTotalCount r)
      (fun _ => 24 * (Fintype.card G : ℝ≥0)^2) := by
  intro o w w' hw
  exact goodCandidate_count_change_le (categoricalQ w) (categoricalQ w')
    (orbitPlace (o,false)) r (categoricalQ_agrees_off_orbit w w' o hw)

/-- The ten-active-label section majorant has the paper's 20 n
coordinate oscillation. It is the same majorant as in SectionExpectation. -/
theorem categoricalSectionCount_boundedDifferences
    (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    CoordinateBoundedDifferences (categoricalSectionCount r i g)
      (fun _ => 20 * (Fintype.card G : ℝ≥0)) := by
  intro o w w' hw
  exact validReducedSection_count_change_le (categoricalQ w) (categoricalQ w')
    r i g (orbitPlace (o,false)) (categoricalQ_agrees_off_orbit w w' o hw)

/-- The chosen nonzero two-element inverse orbits number at most n/2.
This bound uses their injection into G and even holds without odd order. -/
theorem oddOrbit_twice_card_le : 2 * Fintype.card (OddOrbit G) ≤ Fintype.card G := by
  have h := Fintype.card_le_of_injective (orbitPlace (G := G)) orbitPlace.injective
  simpa only [Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using h

theorem total_varianceProxy_le :
    (∑ _o : OddOrbit G, ((24 * (Fintype.card G : ℝ≥0)^2) / 2)^2) ≤
      72 * (Fintype.card G : ℝ≥0)^5 := by
  have hm : 2 * (Fintype.card (OddOrbit G) : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast oddOrbit_twice_card_le (G := G)
  apply NNReal.coe_le_coe.mp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  have hp := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ 72 * (Fintype.card G : ℝ)^4 by positivity)
  nlinarith only [hp]

theorem section_varianceProxy_le :
    (∑ _o : OddOrbit G, ((20 * (Fintype.card G : ℝ≥0)) / 2)^2) ≤
      50 * (Fintype.card G : ℝ≥0)^3 := by
  have hm : 2 * (Fintype.card (OddOrbit G) : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast oddOrbit_twice_card_le (G := G)
  apply NNReal.coe_le_coe.mp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  have hp := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ 50 * (Fintype.card G : ℝ)^2 by positivity)
  nlinarith only [hp]

/-- Centered total-count MGF on the original augmented sample, with proxy
72 n⁵. This is McDiarmid using at most n/2 independent orbit labels. -/
theorem goodCandidates_hasSubgaussianMGF (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (r : TetrahedronRoots G) :
    HasSubgaussianMGF (fun ω : FullSample G =>
      ((goodCandidates (ReservoirVertex ω true) r).card : ℝ) -
        ∫ ω : FullSample G, ((goodCandidates (ReservoirVertex ω true) r).card : ℝ)
          ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab))
      (72 * (Fintype.card G : ℝ≥0)^5)
      (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) := by
  have hs := hasSubgaussianMGF_of_measurePreserving
    (fun _ : OddOrbit G => labelMeasure p τ h)
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)
    fullLabels (fullLabels_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ)
    (fun _ => 24 * (Fintype.card G : ℝ≥0)^2)
    (categoricalTotalCount r) (categoricalTotalCount_boundedDifferences r)
  have hw := proxy_mono hs (total_varianceProxy_le (G := G))
  simpa only [categoricalTotalCount, categoricalQ_fullLabels] using hw

/-- Centered ten-active-label section-count MGF on that same sample, with
proxy 50 n³. The two constant label tests remain omitted. -/
theorem validReducedSection_hasSubgaussianMGF (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    HasSubgaussianMGF (fun ω : FullSample G =>
      ((validReducedSection (ReservoirVertex ω true) r i g).card : ℝ) -
        ∫ ω : FullSample G, ((validReducedSection (ReservoirVertex ω true) r i g).card : ℝ)
          ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab))
      (50 * (Fintype.card G : ℝ≥0)^3)
      (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) := by
  have hs := hasSubgaussianMGF_of_measurePreserving
    (fun _ : OddOrbit G => labelMeasure p τ h)
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)
    fullLabels (fullLabels_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ)
    (fun _ => 20 * (Fintype.card G : ℝ≥0))
    (categoricalSectionCount r i g) (categoricalSectionCount_boundedDifferences r i g)
  have hw := proxy_mono hs (section_varianceProxy_le (G := G))
  simpa only [categoricalSectionCount, categoricalQ_fullLabels] using hw

end
end EndpointMatching.Tetrahedron
