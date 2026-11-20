import CorralFormalization.EndpointProof.AbsorberInputs.FreeDensityPairedCover

/-! Direct buffer expectations and tails on the same free-density
categorical Q sample used for the tetrahedron. -/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
namespace AbsorberInputs.CategoricalQ.BufferCounts
open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open EndpointFiniteProductConcentration EndpointFlow.AbelianTransport
open EndpointMatching.UniversalCore EndpointMatching.UniversalCore.Buffer
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]
local notation "catQ" => EndpointMatching.Tetrahedron.categoricalQ

theorem valid_buffer_probability (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (t : Parameters G) (hv : GeometricallyValid t) :
    (orbitMeasure p τ h).real {w : OddOrbit G → Label |
      ∀ i : Fin 3, catQ w (i,coordinate t i)} = (τ : ℝ)^3 := by
  let e := orbitEmbedding hodd t hv
  let ev : Set (Unit → Fin 3 → Label) := {w | w () = demand ()}
  have hevent : {w : OddOrbit G → Label | ∀ i : Fin 3, catQ w (i,coordinate t i)} =
      project e ⁻¹' ev := by
    ext w
    simp only [Set.mem_ofPred_eq,Set.mem_preimage]
    constructor
    · intro hlabels
      funext i
      exact (buffer_coordinate_iff_label hodd t hv w i).mp (hlabels i)
    · intro hlabels i
      exact (buffer_coordinate_iff_label hodd t hv w i).mpr (congrFun hlabels i)
  rw [hevent,(project_measurePreserving p τ h e).measureReal_preimage (by measurability)]
  exact three_labels_probability p τ h

def bufferIndicator (t : Parameters G) (w : OddOrbit G → Label) : ℝ :=
  if ∀ i : Fin 3, catQ w (i,coordinate t i) then 1 else 0

theorem buffer_expectation (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) :
    (∫ w : OddOrbit G → Label, categoricalTotalCount w ∂orbitMeasure p τ h) =
      ((validParameters (G := G)).card : ℝ)*(τ : ℝ)^3 := by
  let μ := orbitMeasure (O := OddOrbit G) p τ h
  have hfun (t : Parameters G) : bufferIndicator t =
      Set.indicator {w : OddOrbit G → Label | ∀ i : Fin 3, catQ w (i,coordinate t i)} 1 := by
    funext w
    simp [bufferIndicator,Set.indicator_apply]
  calc
    _ = ∫ w, ∑ t ∈ (validParameters : Finset (Parameters G)), bufferIndicator t w ∂μ := by
      apply integral_congr_ae
      apply ae_of_all μ
      intro w
      exact (Finset.sum_boole (R := ℝ) (fun t => ∀ i : Fin 3, catQ w (i,coordinate t i))
        validParameters).symm
    _ = ∑ t ∈ (validParameters : Finset (Parameters G)), ∫ w, bufferIndicator t w ∂μ :=
      integral_finsetSum _ (fun _ _ => Integrable.of_finite)
    _ = ∑ _t ∈ (validParameters : Finset (Parameters G)), (τ : ℝ)^3 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hfun,integral_indicator_one (by measurability)]
      exact valid_buffer_probability hodd p τ h t (Finset.mem_filter.mp ht).2
    _ = _ := by simp

theorem buffer_expectation_lower (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (hn : 24 ≤ Fintype.card G) :
    (3/4 : ℝ)*(τ : ℝ)^3*(Fintype.card G : ℝ)^2 ≤
      ∫ w : OddOrbit G → Label, categoricalTotalCount w ∂orbitMeasure p τ h := by
  rw [buffer_expectation hodd p τ h]
  have hc : (3:ℝ)*(Fintype.card G : ℝ)^2 ≤ 4*((validParameters (G := G)).card : ℝ) := by
    exact_mod_cast validParameters_three_quarters (G := G) hn
  nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ (τ : ℝ)^3 by positivity)]

theorem activeLabels_probability (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (t : Parameters G) (hv : GeometricallyValid t) (i : Fin 3) :
    (orbitMeasure p τ h).real {w : OddOrbit G → Label | activeLabels (catQ w) t i} =
      (τ : ℝ)^2 := by
  let e := activeOrbitEmbedding hodd t hv i
  let ev : Set (Unit → ActivePart i → Label) := {w | w () = activeDemand i ()}
  have hevent : {w : OddOrbit G → Label | activeLabels (catQ w) t i} = project e ⁻¹' ev := by
    ext w
    simp only [Set.mem_ofPred_eq,Set.mem_preimage,activeLabels]
    constructor
    · intro hlabels
      funext j
      exact (buffer_coordinate_iff_label hodd t hv w j.1).mp (hlabels j.1 j.2)
    · intro hlabels j hj
      exact (buffer_coordinate_iff_label hodd t hv w j).mpr (congrFun hlabels ⟨j,hj⟩)
  rw [hevent,(project_measurePreserving p τ h e).measureReal_preimage (by measurability)]
  exact two_labels_probability p τ h i

def sectionIndicator (t : Parameters G) (i : Fin 3) (w : OddOrbit G → Label) : ℝ :=
  if activeLabels (catQ w) t i then 1 else 0

theorem section_expectation (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (i : Fin 3) (g : G) :
    (∫ w : OddOrbit G → Label, categoricalSectionCount i g w ∂orbitMeasure p τ h) =
      ((sectionParameters i g : Finset (Parameters G)).card : ℝ)*(τ : ℝ)^2 := by
  let μ := orbitMeasure (O := OddOrbit G) p τ h
  have hfun (t : Parameters G) : sectionIndicator t i =
      Set.indicator {w : OddOrbit G → Label | activeLabels (catQ w) t i} 1 := by
    funext w
    simp [sectionIndicator,Set.indicator_apply]
  calc
    _ = ∫ w, ∑ t ∈ (sectionParameters i g : Finset (Parameters G)), sectionIndicator t i w ∂μ := by
      apply integral_congr_ae
      apply ae_of_all μ
      intro w
      exact (Finset.sum_boole (R := ℝ) (fun t => activeLabels (catQ w) t i)
        (sectionParameters i g)).symm
    _ = ∑ t ∈ (sectionParameters i g : Finset (Parameters G)), ∫ w, sectionIndicator t i w ∂μ :=
      integral_finsetSum _ (fun _ _ => Integrable.of_finite)
    _ = ∑ _t ∈ (sectionParameters i g : Finset (Parameters G)), (τ : ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hfun,integral_indicator_one (by measurability)]
      exact activeLabels_probability hodd p τ h t
        (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2 i
    _ = _ := by simp

theorem section_expectation_le (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (i : Fin 3) (g : G) :
    (∫ w : OddOrbit G → Label, categoricalSectionCount i g w ∂orbitMeasure p τ h) ≤
      (τ : ℝ)^2*(Fintype.card G : ℝ) := by
  rw [section_expectation hodd p τ h i g]
  have hc : ((sectionParameters i g : Finset (Parameters G)).card : ℝ) ≤ Fintype.card G := by
    exact_mod_cast sectionParameters_card_le (G := G) i g
  nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (τ : ℝ))]

theorem buffer_lower_tail (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (hn : 24 ≤ Fintype.card G) :
    (orbitMeasure p τ h).real {w : OddOrbit G → Label |
      categoricalTotalCount w < (τ : ℝ)^3*(Fintype.card G : ℝ)^2/2} ≤
      Real.exp (-(τ : ℝ)^6*(Fintype.card G : ℝ)/144) := by
  let μ := orbitMeasure (O := OddOrbit G) p τ h
  let n : ℝ := Fintype.card G
  let m := ∫ w, categoricalTotalCount w ∂μ
  let t : ℝ := (τ : ℝ)^3*n^2/4
  have hm : (3/4 : ℝ)*(τ : ℝ)^3*n^2 ≤ m := buffer_expectation_lower hodd p τ h hn
  have hs := EndpointFiniteProductConcentration.hasSubgaussianMGF
    (fun _ : OddOrbit G => labelMeasure p τ h) (fun _ => 6*(Fintype.card G : ℝ≥0))
    categoricalTotalCount categoricalTotalCount_boundedDifferences
  have hsg := proxy_mono hs (EndpointMatching.UniversalCore.Buffer.total_varianceProxy_le (G := G))
  have htail : μ.real {w | t ≤ m-categoricalTotalCount w} ≤ Real.exp (-t^2/(9*n^3)) := by
    convert hsg.neg.measure_ge_le (show 0 ≤ t by dsimp [t,n]; positivity) using 1 <;>
      norm_num [μ,m,n,orbitMeasure]
    all_goals ring
  have hsub : {w : OddOrbit G → Label | categoricalTotalCount w < (τ : ℝ)^3*n^2/2} ⊆
      {w | t ≤ m-categoricalTotalCount w} := by
    intro w hw
    change categoricalTotalCount w < (τ : ℝ)^3*n^2/2 at hw
    change t ≤ m-categoricalTotalCount w
    dsimp [t]
    nlinarith only [hm,hw]
  have hn0 : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  have he : -t^2/(9*n^3) = -(τ : ℝ)^6*n/144 := by
    dsimp [t]
    field_simp [hn0] <;> ring
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans (he ▸ htail)

theorem section_upper_tail (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (i : Fin 3) (g : G) :
    (orbitMeasure p τ h).real {w : OddOrbit G → Label |
      2*(τ : ℝ)^2*(Fintype.card G : ℝ) < categoricalSectionCount i g w} ≤
      Real.exp (-(τ : ℝ)^4*(Fintype.card G : ℝ)/4) := by
  let μ := orbitMeasure (O := OddOrbit G) p τ h
  let n : ℝ := Fintype.card G
  let m := ∫ w, categoricalSectionCount i g w ∂μ
  let t : ℝ := (τ : ℝ)^2*n
  have hm : m ≤ (τ : ℝ)^2*n := section_expectation_le hodd p τ h i g
  have hs := EndpointFiniteProductConcentration.hasSubgaussianMGF
    (fun _ : OddOrbit G => labelMeasure p τ h) (fun _ => 4)
    (categoricalSectionCount i g) (categoricalSectionCount_boundedDifferences i g)
  have hsg := proxy_mono hs (EndpointMatching.UniversalCore.Buffer.section_varianceProxy_le (G := G))
  have htail : μ.real {w | t ≤ categoricalSectionCount i g w-m} ≤ Real.exp (-t^2/(4*n)) := by
    convert hsg.measure_ge_le (show 0 ≤ t by dsimp [t,n]; positivity) using 1 <;>
      norm_num [μ,m,n,orbitMeasure]
    all_goals ring
  have hsub : {w : OddOrbit G → Label | 2*(τ : ℝ)^2*n < categoricalSectionCount i g w} ⊆
      {w | t ≤ categoricalSectionCount i g w-m} := by
    intro w hw
    change 2*(τ : ℝ)^2*n < categoricalSectionCount i g w at hw
    change t ≤ categoricalSectionCount i g w-m
    dsimp [t]
    nlinarith only [hm,hw]
  have hn0 : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  have he : -t^2/(4*n) = -(τ : ℝ)^4*n/4 := by
    dsimp [t]
    field_simp [hn0] <;> ring
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans (he ▸ htail)

def BufferCountEvent (τ : ℝ) (w : OddOrbit G → Label) : Prop :=
  τ^3*(Fintype.card G : ℝ)^2/2 ≤ categoricalTotalCount w ∧
    ∀ i : Fin 3, ∀ g : G,
      (((goodCandidates (catQ w)).filter (fun t => coordinate t i = g)).card : ℝ) ≤
        2*τ^2*(Fintype.card G : ℝ)

theorem bufferCountEvent_failure_probability (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (hn : 24 ≤ Fintype.card G) :
    (orbitMeasure p τ h).real {w : OddOrbit G → Label | ¬ BufferCountEvent (τ : ℝ) w} ≤
      Real.exp (-(τ : ℝ)^6*(Fintype.card G : ℝ)/144) +
      3*(Fintype.card G : ℝ)*Real.exp (-(τ : ℝ)^4*(Fintype.card G : ℝ)/4) := by
  let μ := orbitMeasure (O := OddOrbit G) p τ h
  let badTotal : Set (OddOrbit G → Label) :=
    {w | categoricalTotalCount w < (τ : ℝ)^3*(Fintype.card G : ℝ)^2/2}
  let badSection : Fin 3 → G → Set (OddOrbit G → Label) := fun i g =>
    {w | 2*(τ : ℝ)^2*(Fintype.card G : ℝ) <
      (((goodCandidates (catQ w)).filter (fun t => coordinate t i = g)).card : ℝ)}
  have hs (i : Fin 3) (g : G) : μ.real (badSection i g) ≤
      Real.exp (-(τ : ℝ)^4*(Fintype.card G : ℝ)/4) := by
    apply (measureReal_mono ?_ (measure_ne_top μ _)).trans
      (section_upper_tail hodd p τ h i g)
    intro w hw
    have hc : (((goodCandidates (catQ w)).filter (fun t => coordinate t i = g)).card : ℝ) ≤
        categoricalSectionCount i g w := by
      dsimp only [categoricalSectionCount]
      exact_mod_cast Finset.card_le_card (goodSection_subset_majorant (catQ w) i g)
    exact lt_of_lt_of_le hw hc
  have hsub : {w : OddOrbit G → Label | ¬ BufferCountEvent (τ : ℝ) w} ⊆
      badTotal ∪ ⋃ i : Fin 3, ⋃ g : G, badSection i g := by
    intro w hw
    simp only [BufferCountEvent,not_and_or,not_forall,not_le] at hw
    rcases hw with ht | ⟨i,g,hg⟩
    · exact Or.inl ht
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨g,hg⟩⟩)
  have hsections : μ.real (⋃ i : Fin 3, ⋃ g : G, badSection i g) ≤
      3*(Fintype.card G : ℝ)*Real.exp (-(τ : ℝ)^4*(Fintype.card G : ℝ)/4) := by
    calc
      _ ≤ ∑ i : Fin 3, μ.real (⋃ g : G, badSection i g) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ i : Fin 3, ∑ g : G, μ.real (badSection i g) :=
        Finset.sum_le_sum (fun _ _ => measureReal_iUnion_fintype_le _)
      _ ≤ ∑ _i : Fin 3, ∑ _g : G, Real.exp (-(τ : ℝ)^4*(Fintype.card G : ℝ)/4) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun g _ => hs i g))
      _ = _ := by simp; ring
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (buffer_lower_tail hodd p τ h hn) hsections))

end
end AbsorberInputs.CategoricalQ.BufferCounts
