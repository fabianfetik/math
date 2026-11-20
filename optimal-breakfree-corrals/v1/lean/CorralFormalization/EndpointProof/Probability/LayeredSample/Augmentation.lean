import CorralFormalization.EndpointProof.Probability.LayeredSample.PairBits
import CorralFormalization.EndpointProof.Probability.LayeredSample.Joint

/-!
Independent reserve thinning on the actual categorical layer sample.
This file supplies the sampling/law interface, not the router theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointOriginalReservoir EndpointFullProduct

noncomputable section

theorem Densities.r_le_one {m : ℕ} (d : Densities m) : d.r ≤ 1 := by
  have hma := mul_nonneg (Nat.cast_nonneg m) d.a_nonneg
  linarith [d.vertex_total, d.q_nonneg]

def thinningAt {A : Type*} (role : A) (z : A × Bool) : Bool :=
  decide (z.1 = role ∧ z.2 = true)

/-- A selected categorical role thinned by an independent Bernoulli coin
has the exact product density. -/
theorem thinningAt_measurePreserving {A : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (L : FiniteLaw A) (role : A) (t u : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hmass : L.weight role * t = u) :
    MeasurePreserving (thinningAt role) (L.prod (coinLaw t ht0 ht1)).measure
      (coinLaw u hu0 hu1).measure := by
  have htrue : eventMass (L.prod (coinLaw t ht0 ht1)).weight
      (fun z => z.1 = role ∧ z.2 = true) = u := by
    change eventMass (productWeight L.weight (coinWeight t))
      (fun z => z.1 = role ∧ z.2 = true) = u
    rw [eventMass_product L.weight (coinWeight t) (fun a => a = role)
      (fun b => b = true), eventMass_eq, eventMass_eq]
    simpa [coinWeight] using hmass
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_measureReal_singleton
  intro b
  rw [map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton _)]
  change (L.prod (coinLaw t ht0 ht1)).measure.real {z | thinningAt role z = b} =
    (coinLaw u hu0 hu1).measure.real {b' | b' = b}
  rw [FiniteLaw.real_event, FiniteLaw.real_event, eventMass_eq]
  cases b
  · have heq : eventMass (L.prod (coinLaw t ht0 ht1)).weight
        (fun z => thinningAt role z = false) =
        eventMass (L.prod (coinLaw t ht0 ht1)).weight
          (fun z => ¬ (z.1 = role ∧ z.2 = true)) := by
      exact eventMass_congr _ (fun z => by simp [thinningAt])
    rw [heq, eventMass_compl, htrue]
    rfl
  · have heq : eventMass (L.prod (coinLaw t ht0 ht1)).weight
        (fun z => thinningAt role z = true) =
        eventMass (L.prod (coinLaw t ht0 ht1)).weight
          (fun z => z.1 = role ∧ z.2 = true) := by
      exact eventMass_congr _ (fun z => by simp [thinningAt])
    rw [heq, htrue]
    rfl

/-- The original labels and one fresh thinning coin in each channel at
each group element.  Coin and label are independent at every coordinate. -/
abbrev AugmentedSample (G : Type*) (m : ℕ) :=
  (G → VertexRole m × Bool) × (G → ColourRole m × Bool)

def augmentedMeasure {G : Type*} [Fintype G] {m : ℕ} (d : Densities m)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Measure (AugmentedSample G m) :=
  (Measure.pi fun _ : G => ((vertexLaw d).prod (coinLaw t ht0 ht1)).measure).prod
    (Measure.pi fun _ : G => ((colourLaw d).prod (coinLaw t ht0 ht1)).measure)

instance {G : Type*} [Fintype G] {m : ℕ} (d : Densities m)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (augmentedMeasure (G := G) d t ht0 ht1) := by
  unfold augmentedMeasure; infer_instance

def forgetAugmented {G : Type*} {m : ℕ} (s : AugmentedSample G m) : Sample G m :=
  (fun g => (s.1 g).1, fun g => (s.2 g).1)

theorem forgetAugmented_measurePreserving {G : Type*} [Fintype G] {m : ℕ}
    (d : Densities m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MeasurePreserving forgetAugmented (augmentedMeasure (G := G) d t ht0 ht1)
      (sampleMeasure d) := by
  have hv : MeasurePreserving Prod.fst ((vertexLaw d).prod (coinLaw t ht0 ht1)).measure
      (vertexLaw d).measure := by
    rw [finiteLaw_measure_prod]
    exact measurePreserving_fst
  have hc : MeasurePreserving Prod.fst ((colourLaw d).prod (coinLaw t ht0 ht1)).measure
      (colourLaw d).measure := by
    rw [finiteLaw_measure_prod]
    exact measurePreserving_fst
  exact (measurePreserving_pi _ _ (fun _ : G => hv)).prod
    (measurePreserving_pi _ _ (fun _ : G => hc))

def thinnedReserves {G : Type*} {m : ℕ} (s : AugmentedSample G m) :
    (G → Bool) × (G → Bool) :=
  (fun g => thinningAt (reserveVertex m) (s.1 g),
   fun g => thinningAt (reserveColour m) (s.2 g))

theorem thinnedVertex_mem_reserve {G : Type*} {m : ℕ} (s : AugmentedSample G m) (g : G)
    (h : (thinnedReserves s).1 g = true) :
    (forgetAugmented s).1 g = reserveVertex m := by
  have h' : (s.1 g).1 = reserveVertex m ∧ (s.1 g).2 = true := by
    simpa [thinnedReserves, thinningAt] using h
  exact h'.1

theorem thinnedColour_mem_reserve {G : Type*} {m : ℕ} (s : AugmentedSample G m) (g : G)
    (h : (thinnedReserves s).2 g = true) :
    (forgetAugmented s).2 g = reserveColour m := by
  have h' : (s.2 g).1 = reserveColour m ∧ (s.2 g).2 = true := by
    simpa [thinnedReserves, thinningAt] using h
  exact h'.1

/-- Independent Bernoulli-`u` vertex and colour reserves from independent
thinning at rate `u/r`.  The original categorical law is preserved by the
other projection of this same augmentation. -/
theorem thinnedReserves_measurePreserving {G : Type*} [Fintype G] {m : ℕ}
    (d : Densities m) (hr : 0 < d.r) (u : ℝ) (hu0 : 0 ≤ u) (hur : u ≤ d.r) :
    MeasurePreserving thinnedReserves
      (augmentedMeasure (G := G) d (u / d.r) (div_nonneg hu0 hr.le)
        ((div_le_one hr).mpr hur))
      ((Measure.pi fun _ : G => (coinLaw u hu0 (hur.trans d.r_le_one)).measure).prod
        (Measure.pi fun _ : G => (coinLaw u hu0 (hur.trans d.r_le_one)).measure)) := by
  have hm : d.r * (u / d.r) = u := by field_simp
  have hv := thinningAt_measurePreserving (vertexLaw d) (reserveVertex m)
    (u / d.r) u (div_nonneg hu0 hr.le) ((div_le_one hr).mpr hur)
    hu0 (hur.trans d.r_le_one) (by simpa [vertexLaw, vertexWeight] using hm)
  have hc := thinningAt_measurePreserving (colourLaw d) (reserveColour m)
    (u / d.r) u (div_nonneg hu0 hr.le) ((div_le_one hr).mpr hur)
    hu0 (hur.trans d.r_le_one) (by simpa [colourLaw, colourWeight] using hm)
  exact (measurePreserving_pi _ _ (fun _ : G => hv)).prod
    (measurePreserving_pi _ _ (fun _ : G => hc))

/-- Exact transfer of any fixed reserve-bank event, including a supplied
router event, from its independent Bernoulli law to this augmentation. -/
theorem thinnedReserves_event_probability {G : Type*} [Fintype G] {m : ℕ}
    (d : Densities m) (hr : 0 < d.r) (u : ℝ) (hu0 : 0 ≤ u) (hur : u ≤ d.r)
    (event : ((G → Bool) × (G → Bool)) → Prop) :
    (augmentedMeasure (G := G) d (u / d.r) (div_nonneg hu0 hr.le)
        ((div_le_one hr).mpr hur)).real {s | ¬ event (thinnedReserves s)} =
      ((Measure.pi fun _ : G => (coinLaw u hu0 (hur.trans d.r_le_one)).measure).prod
        (Measure.pi fun _ : G => (coinLaw u hu0 (hur.trans d.r_le_one)).measure)).real
          {z | ¬ event z} := by
  exact (thinnedReserves_measurePreserving d hr u hu0 hur).measureReal_preimage
    (s := {z | ¬ event z}) (by measurability)

/-- A further event such as a proved router event can be joined to the
already proved layer event on the same augmented sample. -/
theorem augmented_good_and_event_failure_probability
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (tol B e : ℝ)
    (hgood : (sampleMeasure (G := G) d).real {s | ¬ GoodSample d tol s} ≤ B)
    (event : AugmentedSample G m → Prop)
    (hevent : (augmentedMeasure d t ht0 ht1).real {s | ¬ event s} ≤ e) :
    (augmentedMeasure d t ht0 ht1).real
      {s | ¬ (GoodSample d tol (forgetAugmented s) ∧ event s)} ≤ B + e := by
  have hp := forgetAugmented_measurePreserving (G := G) d t ht0 ht1
  rw [← hp.measureReal_preimage (by measurability)] at hgood
  have heq : {s : AugmentedSample G m |
      ¬ (GoodSample d tol (forgetAugmented s) ∧ event s)} =
      (forgetAugmented ⁻¹' {s | ¬ GoodSample d tol s}) ∪ {s | ¬ event s} := by
    ext s; simp only [not_and_or, Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [heq]
  exact (measureReal_union_le _ _).trans (add_le_add hgood hevent)

/-- Positive-probability common augmentation.  It is one witness for the
whole already-universal layer event and the additional supplied event. -/
theorem exists_goodAugmented_and_event_of_error_lt_one
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (tol B e : ℝ)
    (hgood : (sampleMeasure (G := G) d).real {s | ¬ GoodSample d tol s} ≤ B)
    (event : AugmentedSample G m → Prop)
    (hevent : (augmentedMeasure d t ht0 ht1).real {s | ¬ event s} ≤ e)
    (hsmall : B + e < 1) :
    ∃ s : AugmentedSample G m, GoodSample d tol (forgetAugmented s) ∧ event s := by
  have hp := augmented_good_and_event_failure_probability d t ht0 ht1 tol B e
    hgood event hevent
  by_contra hnone
  have heq : {s : AugmentedSample G m |
      ¬ (GoodSample d tol (forgetAugmented s) ∧ event s)} = Set.univ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact fun hs => hnone ⟨s, hs⟩
  rw [heq, probReal_univ] at hp
  linarith

end
end EndpointLayeredSample
