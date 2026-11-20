import CorralFormalization.EndpointProof.AbsorberInputs.CategoricalQLaw

/-! Direct tetrahedron means and tails under the pure categorical orbit
law. In particular p=0 allows every Q density 0<tau<=1/3, independently
of an upstream raw-minus sample. -/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
namespace AbsorberInputs.CategoricalQ
open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open EndpointFullProduct EndpointReservoirAvailability EndpointFiniteProductConcentration
open EndpointFlow.AbelianTransport EndpointSelector.FixedCardinality
open EndpointMatching.Tetrahedron
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem validCandidate_probability (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (r : TetrahedronRoots G) (hr : admissibleRoots r) (t : TetrahedronParameters G)
    (ht : t ∈ validParameterSet r) :
    (orbitMeasure p τ h).real {w : OddOrbit G → Label |
      t ∈ goodCandidates (categoricalQ w) r} = (τ : ℝ)^12 := by
  let hv : geometricallyValid r t := (Finset.mem_filter.mp ht).2
  let e := representativeOrbitEmbedding hodd r t hv
  let ev : Set (Unit → Fin 12 → Label) := {w | w () = qDemand ()}
  have hevent : {w : OddOrbit G → Label | t ∈ goodCandidates (categoricalQ w) r} =
      project e ⁻¹' ev := by
    ext w
    simp only [Set.mem_ofPred_eq,Set.mem_preimage]
    rw [validParameter_mem_goodCandidates_iff hodd (categoricalQ w)
      (pairReservoir hodd w) r hr t ht]
    constructor
    · intro hlabels
      funext i
      exact (representative_iff_label hodd r t hv w i).mp (hlabels i)
    · intro hlabels i
      exact (representative_iff_label hodd r t hv w i).mpr (congrFun hlabels i)
  rw [hevent,(project_measurePreserving p τ h e).measureReal_preimage (by measurability)]
  exact twelve_labels_probability p τ h

def tetrahedronIndicator (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (w : OddOrbit G → Label) : ℝ := if t ∈ goodCandidates (categoricalQ w) r then 1 else 0

theorem tetrahedron_count_sum (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (w : OddOrbit G → Label) :
    categoricalTotalCount r w = ∑ t ∈ validParameterSet r, tetrahedronIndicator r t w := by
  have heq : (validParameterSet r).filter (fun t => t ∈ goodCandidates (categoricalQ w) r) =
      goodCandidates (categoricalQ w) r := by
    ext t
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun ht => ⟨goodCandidates_subset_valid hodd w r ht,ht⟩⟩
  dsimp [categoricalTotalCount,tetrahedronIndicator]
  calc
    ((goodCandidates (categoricalQ w) r).card : ℝ) =
        (((validParameterSet r).filter (fun t => t ∈ goodCandidates (categoricalQ w) r)).card : ℝ) := by
      rw [heq]
    _ = _ := (Finset.sum_boole (R := ℝ) (fun t => t ∈ goodCandidates (categoricalQ w) r)
      (validParameterSet r)).symm

theorem tetrahedron_expectation (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (r : TetrahedronRoots G) (hr : admissibleRoots r) :
    (∫ w : OddOrbit G → Label, categoricalTotalCount r w ∂orbitMeasure p τ h) =
      ((validParameterSet r).card : ℝ)*(τ : ℝ)^12 := by
  let μ := orbitMeasure (O := OddOrbit G) p τ h
  have hfun (t : TetrahedronParameters G) : tetrahedronIndicator r t =
      Set.indicator {w : OddOrbit G → Label | t ∈ goodCandidates (categoricalQ w) r} 1 := by
    funext w
    simp [tetrahedronIndicator,Set.indicator_apply]
  calc
    _ = ∫ w, ∑ t ∈ validParameterSet r, tetrahedronIndicator r t w ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ (tetrahedron_count_sum hodd r)
    _ = ∑ t ∈ validParameterSet r, ∫ w, tetrahedronIndicator r t w ∂μ :=
      integral_finsetSum _ (fun _ _ => Integrable.of_finite)
    _ = ∑ _t ∈ validParameterSet r, (τ : ℝ)^12 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hfun,integral_indicator_one (by measurability)]
      exact validCandidate_probability hodd p τ h r hr t ht
    _ = _ := by simp

theorem tetrahedron_expectation_lower (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (r : TetrahedronRoots G) (hr : admissibleRoots r)
    (hn : 1152 ≤ Fintype.card G) :
    (3/4 : ℝ)*(τ : ℝ)^12*(Fintype.card G : ℝ)^3 ≤
      ∫ w : OddOrbit G → Label, categoricalTotalCount r w ∂orbitMeasure p τ h := by
  rw [tetrahedron_expectation hodd p τ h r hr]
  have hc : (3:ℝ)*(Fintype.card G : ℝ)^3 ≤ 4*((validParameterSet r).card : ℝ) := by
    exact_mod_cast validParameterSet_three_quarters hodd r hr hn
  nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ (τ : ℝ)^12 by positivity)]

theorem activeLabels_probability (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (r : TetrahedronRoots G) (t : TetrahedronParameters G) (hv : geometricallyValid r t)
    (i : Fin 6) :
    (orbitMeasure p τ h).real {w : OddOrbit G → Label |
      activeLabels (categoricalQ w) r t i} = (τ : ℝ)^10 := by
  let e := activeOrbitEmbedding hodd r t hv i
  let ev : Set (Unit → ActiveIndex i → Label) := {w | w () = activeDemand i ()}
  have hevent : {w : OddOrbit G → Label | activeLabels (categoricalQ w) r t i} =
      project e ⁻¹' ev := by
    ext w
    simp only [Set.mem_ofPred_eq,Set.mem_preimage,activeLabels]
    constructor
    · intro hlabels
      funext j
      exact (representative_iff_label hodd r t hv w j.1).mp (hlabels j.1 j.2)
    · intro hlabels j hj
      exact (representative_iff_label hodd r t hv w j).mpr (congrFun hlabels ⟨j,hj⟩)
  rw [hevent,(project_measurePreserving p τ h e).measureReal_preimage (by measurability)]
  exact ten_labels_probability p τ h i

def sectionIndicator (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (i : Fin 6) (w : OddOrbit G → Label) : ℝ := if activeLabels (categoricalQ w) r t i then 1 else 0

theorem section_expectation (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    (∫ w : OddOrbit G → Label, categoricalSectionCount r i g w ∂orbitMeasure p τ h) =
      ((validSectionParameters r i g).card : ℝ)*(τ : ℝ)^10 := by
  let μ := orbitMeasure (O := OddOrbit G) p τ h
  have hfun (t : TetrahedronParameters G) : sectionIndicator r t i =
      Set.indicator {w : OddOrbit G → Label | activeLabels (categoricalQ w) r t i} 1 := by
    funext w
    simp [sectionIndicator,Set.indicator_apply]
  calc
    _ = ∫ w, ∑ t ∈ validSectionParameters r i g, sectionIndicator r t i w ∂μ := by
      apply integral_congr_ae
      apply ae_of_all μ
      intro w
      exact (Finset.sum_boole (R := ℝ) (fun t => activeLabels (categoricalQ w) r t i)
        (validSectionParameters r i g)).symm
    _ = ∑ t ∈ validSectionParameters r i g, ∫ w, sectionIndicator r t i w ∂μ :=
      integral_finsetSum _ (fun _ _ => Integrable.of_finite)
    _ = ∑ _t ∈ validSectionParameters r i g, (τ : ℝ)^10 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hfun,integral_indicator_one (by measurability)]
      exact activeLabels_probability hodd p τ h r t
        (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2 i
    _ = _ := by simp

theorem section_expectation_le (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    (∫ w : OddOrbit G → Label, categoricalSectionCount r i g w ∂orbitMeasure p τ h) ≤
      (τ : ℝ)^10*(Fintype.card G : ℝ)^2 := by
  rw [section_expectation hodd p τ h r i g]
  have hc : ((validSectionParameters r i g).card : ℝ) ≤ (Fintype.card G : ℝ)^2 := by
    exact_mod_cast validSectionParameters_card_le r i g
  nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ (τ : ℝ)^10 by positivity)]

theorem tetrahedron_lower_tail (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (r : TetrahedronRoots G) (hr : admissibleRoots r)
    (hn : 1152 ≤ Fintype.card G) :
    (orbitMeasure p τ h).real {w : OddOrbit G → Label |
      categoricalTotalCount r w < (τ : ℝ)^12*(Fintype.card G : ℝ)^3/2} ≤
      Real.exp (-(τ : ℝ)^24*(Fintype.card G : ℝ)/2304) := by
  let μ := orbitMeasure (O := OddOrbit G) p τ h
  let n : ℝ := Fintype.card G
  let m := ∫ w, categoricalTotalCount r w ∂μ
  let t : ℝ := (τ : ℝ)^12*n^3/4
  have hm : (3/4 : ℝ)*(τ : ℝ)^12*n^3 ≤ m := tetrahedron_expectation_lower hodd p τ h r hr hn
  have hs := EndpointFiniteProductConcentration.hasSubgaussianMGF
    (fun _ : OddOrbit G => labelMeasure p τ h)
    (fun _ => 24*(Fintype.card G : ℝ≥0)^2)
    (categoricalTotalCount r) (categoricalTotalCount_boundedDifferences r)
  have hsg := proxy_mono hs (EndpointMatching.Tetrahedron.total_varianceProxy_le (G := G))
  have htail : μ.real {w | t ≤ m-categoricalTotalCount r w} ≤ Real.exp (-t^2/(144*n^5)) := by
    have ht := hsg.neg.measure_ge_le (show 0 ≤ t by dsimp [t,n]; positivity)
    norm_num [← mul_assoc] at ht
    simpa [μ,m,n,orbitMeasure] using ht
  have hsub : {w : OddOrbit G → Label | categoricalTotalCount r w < (τ : ℝ)^12*n^3/2} ⊆
      {w | t ≤ m-categoricalTotalCount r w} := by
    intro w hw
    change categoricalTotalCount r w < (τ : ℝ)^12*n^3/2 at hw
    change t ≤ m-categoricalTotalCount r w
    dsimp [t]
    nlinarith only [hm,hw]
  have hn0 : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  have he : -t^2/(144*n^5) = -(τ : ℝ)^24*n/2304 := by
    dsimp [t]
    field_simp [hn0] <;> ring
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans (he ▸ htail)

theorem section_upper_tail (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    (orbitMeasure p τ h).real {w : OddOrbit G → Label |
      2*(τ : ℝ)^10*(Fintype.card G : ℝ)^2 < categoricalSectionCount r i g w} ≤
      Real.exp (-(τ : ℝ)^20*(Fintype.card G : ℝ)/100) := by
  let μ := orbitMeasure (O := OddOrbit G) p τ h
  let n : ℝ := Fintype.card G
  let m := ∫ w, categoricalSectionCount r i g w ∂μ
  let t : ℝ := (τ : ℝ)^10*n^2
  have hm : m ≤ (τ : ℝ)^10*n^2 := section_expectation_le hodd p τ h r i g
  have hs := EndpointFiniteProductConcentration.hasSubgaussianMGF
    (fun _ : OddOrbit G => labelMeasure p τ h) (fun _ => 20*(Fintype.card G : ℝ≥0))
    (categoricalSectionCount r i g) (categoricalSectionCount_boundedDifferences r i g)
  have hsg := proxy_mono hs (EndpointMatching.Tetrahedron.section_varianceProxy_le (G := G))
  have htail : μ.real {w | t ≤ categoricalSectionCount r i g w-m} ≤ Real.exp (-t^2/(100*n^3)) := by
    have ht := hsg.measure_ge_le (show 0 ≤ t by dsimp [t,n]; positivity)
    norm_num [← mul_assoc] at ht
    simpa [μ,m,n,orbitMeasure] using ht
  have hsub : {w : OddOrbit G → Label | 2*(τ : ℝ)^10*n^2 < categoricalSectionCount r i g w} ⊆
      {w | t ≤ categoricalSectionCount r i g w-m} := by
    intro w hw
    change 2*(τ : ℝ)^10*n^2 < categoricalSectionCount r i g w at hw
    change t ≤ categoricalSectionCount r i g w-m
    dsimp [t]
    nlinarith only [hm,hw]
  have hn0 : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  have he : -t^2/(100*n^3) = -(τ : ℝ)^20*n/100 := by
    dsimp [t]
    field_simp [hn0] <;> ring
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans (he ▸ htail)

end
end AbsorberInputs.CategoricalQ
