import CorralFormalization.EndpointProof.Probability.LayeredSample.Model
import CorralFormalization.EndpointProof.Probability.FiniteProductConcentration

/-! Finite categorical counts and simultaneous raw layer-size concentration. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointOriginalReservoir EndpointFullProduct EndpointFiniteProductConcentration

noncomputable section

/-- A count on a fixed set of independent categorical coordinates. -/
def eventCount {ι A : Type*} (S : Finset ι) (P : A → Prop) (w : ι → A) : ℝ :=
  ∑ i ∈ S, if P (w i) then 1 else 0

theorem eventCount_eq_card {ι A : Type*} (S : Finset ι) (P : A → Prop) (w : ι → A) :
    eventCount S P w = ((S.filter (fun i => P (w i))).card : ℝ) := by
  exact Finset.sum_boole (R := ℝ) (fun i => P (w i)) S

theorem eventCount_boundedDifferences {ι A : Type*} [Fintype ι]
    (S : Finset ι) (P : A → Prop) :
    CoordinateBoundedDifferences (eventCount S P) (fun _ : ι => 1) := by
  intro i x y hxy
  unfold eventCount
  rw [← Finset.sum_sub_distrib]
  have hrest (j : ι) (_ : j ∈ S) (hji : j ≠ i) :
      (if P (x j) then (1 : ℝ) else 0) - (if P (y j) then 1 else 0) = 0 := by
    rw [hxy j hji, sub_self]
  by_cases hi : i ∈ S
  · rw [Finset.sum_eq_single i hrest (by simp [hi])]
    split_ifs <;> norm_num
  · rw [Finset.sum_eq_zero (fun j hj => hrest j hj (by intro h; subst j; exact hi hj))]
    norm_num

theorem eventCount_expectation {ι A : Type*} [Fintype ι] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (L : FiniteLaw A) (S : Finset ι) (P : A → Prop) :
    (∫ w : ι → A, eventCount S P w ∂Measure.pi (fun _ : ι => L.measure)) =
      S.card * eventMass L.weight P := by
  have hone (i : ι) :
      (∫ w : ι → A, if P (w i) then (1 : ℝ) else 0
        ∂Measure.pi (fun _ : ι => L.measure)) = eventMass L.weight P := by
    have hp := measurePreserving_eval (fun _ : ι => L.measure) i
    have hfun : (fun w : ι → A => if P (w i) then (1 : ℝ) else 0) =
        Set.indicator ((Function.eval i) ⁻¹' {a | P a}) 1 := by
      funext w; simp [Set.indicator_apply]
    rw [hfun, integral_indicator_one (by measurability), hp.measureReal_preimage
      (by measurability), FiniteLaw.real_event]
  unfold eventCount
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [hone]
  simp

theorem eventCount_hasSubgaussianMGF {ι A : Type*} [Fintype ι] [Fintype A]
    [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (L : FiniteLaw A) (S : Finset ι) (P : A → Prop) :
    HasSubgaussianMGF
      (fun w : ι → A => eventCount S P w - S.card * eventMass L.weight P)
      ((Fintype.card ι : ℝ≥0) / 4) (Measure.pi (fun _ : ι => L.measure)) := by
  have h := EndpointFiniteProductConcentration.hasSubgaussianMGF
    (fun _ : ι => L.measure) (fun _ : ι => 1) (eventCount S P)
      (eventCount_boundedDifferences S P)
  rw [eventCount_expectation] at h
  convert h using 1 <;> simp <;> ring

theorem eventCount_lower_tail {ι A : Type*} [Fintype ι] [Fintype A]
    [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (L : FiniteLaw A) (S : Finset ι) (P : A → Prop) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι => L.measure)).real
      {w | t ≤ S.card * eventMass L.weight P - eventCount S P w} ≤
        Real.exp (-t^2 / (2 * ((Fintype.card ι : ℝ) / 4))) := by
  simpa only [Pi.neg_apply, neg_sub, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_ofNat] using (eventCount_hasSubgaussianMGF L S P).neg.measure_ge_le ht

theorem eventCount_twoSided_tail {ι A : Type*} [Fintype ι] [Fintype A]
    [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (L : FiniteLaw A) (S : Finset ι) (P : A → Prop) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι => L.measure)).real
      {w | t < |eventCount S P w - S.card * eventMass L.weight P|} ≤
        2 * Real.exp (-t^2 / (2 * ((Fintype.card ι : ℝ) / 4))) := by
  let μ := Measure.pi (fun _ : ι => L.measure)
  let X : (ι → A) → ℝ := fun w => eventCount S P w - S.card * eventMass L.weight P
  have hs := eventCount_hasSubgaussianMGF L S P
  have hu : μ.real {w | t ≤ X w} ≤
      Real.exp (-t^2 / (2 * ((Fintype.card ι : ℝ) / 4))) := by
    simpa [μ, X] using hs.measure_ge_le ht
  have hl : μ.real {w | t ≤ -X w} ≤
      Real.exp (-t^2 / (2 * ((Fintype.card ι : ℝ) / 4))) := by
    simpa [μ, X] using hs.neg.measure_ge_le ht
  have hsub : {w | t < |X w|} ⊆ {w | t ≤ X w} ∪ {w | t ≤ -X w} := by
    intro w hw
    change t < |X w| at hw
    change t ≤ X w ∨ t ≤ -X w
    rcases lt_abs.mp hw with h | h
    · exact Or.inl h.le
    · exact Or.inr (by linarith)
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    ((measureReal_union_le _ _).trans (by linarith))

/-- Every raw role size, including both reserves, is close to its actual
categorical mean on the same sample. -/
def SizeEvent {G : Type*} [Fintype G] {m : ℕ}
    (d : Densities m) (t : ℝ) (s : Sample G m) : Prop :=
  (∀ v : VertexRole m,
    |((vertexSet s v).card : ℝ) - (Fintype.card G : ℝ) * vertexWeight d v| ≤ t) ∧
  (∀ c : ColourRole m,
    |((colourSet s c).card : ℝ) - (Fintype.card G : ℝ) * colourWeight d c| ≤ t)

/-- A union bound over the fixed role labels, with no independence between
different role sizes.  There are `(m+4) + (m+3) = 2m+7` such labels. -/
theorem sizeEvent_failure_probability {G : Type*} [Fintype G] {m : ℕ}
    (d : Densities m) (t : ℝ) (ht : 0 ≤ t) :
    (sampleMeasure (G := G) d).real {s | ¬ SizeEvent d t s} ≤
      (2 * (2 * m + 7 : ℕ) : ℝ) *
        Real.exp (-t^2 / (2 * ((Fintype.card G : ℝ) / 4))) := by
  let μ := sampleMeasure (G := G) d
  let badV : VertexRole m → Set (Sample G m) := fun v =>
    {s | t < |((vertexSet s v).card : ℝ) - (Fintype.card G : ℝ) * vertexWeight d v|}
  let badC : ColourRole m → Set (Sample G m) := fun c =>
    {s | t < |((colourSet s c).card : ℝ) - (Fintype.card G : ℝ) * colourWeight d c|}
  have hV (v : VertexRole m) : μ.real (badV v) ≤
      2 * Real.exp (-t^2 / (2 * ((Fintype.card G : ℝ) / 4))) := by
    have hp : MeasurePreserving (Prod.fst : Sample G m → G → VertexRole m) μ
        (Measure.pi (fun _ : G => (vertexLaw d).measure)) := measurePreserving_fst
    have hc := eventCount_twoSided_tail (vertexLaw d) (Finset.univ : Finset G)
      (fun x => x = v) t ht
    rw [← hp.measureReal_preimage (by measurability)] at hc
    convert hc using 1
    congr 1
    ext s
    simp only [badV, Set.mem_ofPred_eq, Set.mem_preimage, eventCount_eq_card,
      Finset.card_univ, eventMass_eq, vertexLaw, vertexSet]
    apply Iff.of_eq
    congr 5
    ext g
    simp
  have hC (c : ColourRole m) : μ.real (badC c) ≤
      2 * Real.exp (-t^2 / (2 * ((Fintype.card G : ℝ) / 4))) := by
    have hp : MeasurePreserving (Prod.snd : Sample G m → G → ColourRole m) μ
        (Measure.pi (fun _ : G => (colourLaw d).measure)) := measurePreserving_snd
    have hc := eventCount_twoSided_tail (colourLaw d) (Finset.univ : Finset G)
      (fun x => x = c) t ht
    rw [← hp.measureReal_preimage (by measurability)] at hc
    convert hc using 1
    congr 1
    ext s
    simp only [badC, Set.mem_ofPred_eq, Set.mem_preimage, eventCount_eq_card,
      Finset.card_univ, eventMass_eq, colourLaw, colourSet]
    apply Iff.of_eq
    congr 5
    ext g
    simp
  have hevent : {s : Sample G m | ¬ SizeEvent d t s} =
      (⋃ v, badV v) ∪ (⋃ c, badC c) := by
    ext s
    simp only [SizeEvent, badV, badC, not_and_or, not_forall, not_le,
      Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq]
  rw [hevent]
  calc
    μ.real ((⋃ v, badV v) ∪ (⋃ c, badC c)) ≤
        μ.real (⋃ v, badV v) + μ.real (⋃ c, badC c) := measureReal_union_le _ _
    _ ≤ (∑ v, μ.real (badV v)) + ∑ c, μ.real (badC c) :=
      add_le_add (measureReal_iUnion_fintype_le _) (measureReal_iUnion_fintype_le _)
    _ ≤ (∑ _v : VertexRole m,
        2 * Real.exp (-t^2 / (2 * ((Fintype.card G : ℝ) / 4)))) +
        (∑ _c : ColourRole m,
          2 * Real.exp (-t^2 / (2 * ((Fintype.card G : ℝ) / 4)))) :=
      add_le_add (Finset.sum_le_sum fun v _ => hV v) (Finset.sum_le_sum fun c _ => hC c)
    _ = _ := by simp [VertexRole, ColourRole]; push_cast; ring

end
end EndpointLayeredSample
