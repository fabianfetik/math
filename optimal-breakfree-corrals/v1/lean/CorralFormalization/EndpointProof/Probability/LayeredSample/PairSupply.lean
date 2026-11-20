import CorralFormalization.EndpointProof.Probability.LayeredSample.Concentration

/-!
The actual pair bank in the path-factor construction.  The argument reindexes only
the independent colour channel, so distinct pairs use disjoint coordinates
in both channels.  Colour zero is omitted by erasing exactly `a = g`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointOriginalReservoir EndpointFullProduct

noncomputable section

def pairLaw {m : ℕ} (d : Densities m) : FiniteLaw (VertexRole m × ColourRole m) :=
  (vertexLaw d).prod (colourLaw d)

def pairSelected {m : ℕ} (z : VertexRole m × ColourRole m) : Prop :=
  z.1 = lastVertex m ∧ z.2 = specialColour m

theorem pairSelected_mass {m : ℕ} (d : Densities m) :
    eventMass (pairLaw d).weight pairSelected = d.q^2 := by
  change eventMass (productWeight (vertexWeight d) (colourWeight d))
    (fun z => z.1 = lastVertex m ∧ z.2 = specialColour m) = _
  rw [eventMass_product (vertexWeight d) (colourWeight d)
    (fun v => v = lastVertex m) (fun c => c = specialColour m), eventMass_eq, eventMass_eq]
  simp [vertexWeight, colourWeight, lastVertex, specialColour, pow_two]

def subtractionEquiv {G : Type*} [AddCommGroup G] (g : G) : G ≃ G where
  toFun := fun a => g - a
  invFun := fun a => g - a
  left_inv := by intro a; simp
  right_inv := by intro a; simp

def pairSites {G : Type*} [AddCommGroup G] {m : ℕ}
    (g : G) (s : Sample G m) : G → VertexRole m × ColourRole m :=
  fun a => (s.1 a, s.2 (g - a))

/-- Every fixed numerical root gives an actual independent product of
paired coordinates.  This is derived from the original two-channel law. -/
theorem pairSites_measurePreserving {G : Type*} [Fintype G] [AddCommGroup G]
    {m : ℕ} (d : Densities m) (g : G) :
    MeasurePreserving (pairSites g) (sampleMeasure (G := G) d)
      (Measure.pi fun _ : G => (pairLaw d).measure) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : G => ColourRole m) (subtractionEquiv g)
  have hp : MeasurePreserving (fun w : G → ColourRole m => fun a => w (g - a))
      (Measure.pi fun _ : G => (colourLaw d).measure)
      (Measure.pi fun _ : G => (colourLaw d).measure) := by
    convert measurePreserving_piCongrLeft (fun _ : G => (colourLaw d).measure)
      (subtractionEquiv g) using 1
    funext w a
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply, subtractionEquiv]
  let E := MeasurableEquiv.arrowProdEquivProdArrow (VertexRole m) (ColourRole m) G
  have hsplit := (measurePreserving_arrowProdEquivProdArrow
    (VertexRole m) (ColourRole m) G
    (fun _ : G => (vertexLaw d).measure) (fun _ : G => (colourLaw d).measure)).symm E
  have h := hsplit.comp ((MeasurePreserving.id
    (Measure.pi fun _ : G => (vertexLaw d).measure)).prod hp)
  unfold pairLaw
  simp_rw [finiteLaw_measure_prod]
  exact h

/-- Literal usable pairs `(a, g-a)` with `a ∈ V_J` and nonzero colour in
`C_*`.  The vertex `a = 0` is allowed. -/
def pairSupplySet {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (s : Sample G m) (g : G) : Finset G :=
  Finset.univ.filter (fun a => s.1 a = lastVertex m ∧
    s.2 (g - a) = specialColour m ∧ g - a ≠ 0)

theorem pairSupplySet_eq {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (s : Sample G m) (g : G) :
    pairSupplySet s g = (Finset.univ.erase g).filter
      (fun a => pairSelected (pairSites g s a)) := by
  ext a
  constructor
  · intro ha
    obtain ⟨_, hv, hc, hz⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, hv, hc⟩
    intro hag
    subst a
    exact hz (sub_self g)
  · intro ha
    obtain ⟨hmem, hv, hc⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hv, hc, ?_⟩
    exact sub_ne_zero.mpr (Finset.mem_erase.mp hmem).1.symm

theorem pairSupplyCount_eq_eventCount {G : Type*} [Fintype G] [AddCommGroup G]
    {m : ℕ} (s : Sample G m) (g : G) :
    ((pairSupplySet s g).card : ℝ) =
      eventCount (Finset.univ.erase g) pairSelected (pairSites g s) := by
  rw [eventCount_eq_card, pairSupplySet_eq]

/-- Exact `(n-1)q²` mean, including the omission of precisely the zero
colour coordinate.  No endpoint coordinate is deleted. -/
theorem pairSupplyCount_expectation {G : Type*} [Fintype G] [AddCommGroup G]
    {m : ℕ} (d : Densities m) (g : G) :
    (∫ s : Sample G m, ((pairSupplySet s g).card : ℝ) ∂sampleMeasure d) =
      ((Fintype.card G : ℝ) - 1) * d.q^2 := by
  have hp := pairSites_measurePreserving d g
  simp_rw [pairSupplyCount_eq_eventCount]
  have hi := integral_map (μ := sampleMeasure d) hp.measurable.aemeasurable
    (measurable_of_countable (eventCount (Finset.univ.erase g) pairSelected)).aestronglyMeasurable
  rw [hp.map_eq] at hi
  rw [← hi, eventCount_expectation, pairSelected_mass,
    Finset.card_erase_of_mem (Finset.mem_univ g), Finset.card_univ]
  have hn : 1 ≤ Fintype.card G := Fintype.card_pos_iff.mpr inferInstance
  rw [Nat.cast_sub hn]
  simp

/-- The paper's advertised elementary bound for one fixed root, valid
already for `n ≥ 4`.  Different roots need not have independent banks. -/
theorem pairSupply_failure_probability {G : Type*} [Fintype G] [AddCommGroup G]
    {m : ℕ} (d : Densities m) (g : G) (hn : 4 ≤ Fintype.card G) :
    (sampleMeasure (G := G) d).real
      {s | ((pairSupplySet s g).card : ℝ) < d.q^2 * (Fintype.card G : ℝ) / 2} ≤
        Real.exp (-d.q^4 * (Fintype.card G : ℝ) / 8) := by
  let n : ℝ := Fintype.card G
  let t : ℝ := d.q^2 * n / 4
  have ht : 0 ≤ t := by dsimp [t, n]; positivity
  have hp := pairSites_measurePreserving d g
  have htail := eventCount_lower_tail (pairLaw d) (Finset.univ.erase g)
    pairSelected t ht
  rw [← hp.measureReal_preimage (by measurability), pairSelected_mass] at htail
  have hnreal : (4 : ℝ) ≤ n := by dsimp [n]; exact_mod_cast hn
  have hcard : ((Finset.univ.erase g).card : ℝ) = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ g), Finset.card_univ,
      Nat.cast_sub (show 1 ≤ Fintype.card G by omega)]
    simp [n]
  have hsub : {s : Sample G m |
      ((pairSupplySet s g).card : ℝ) < d.q^2 * n / 2} ⊆
      pairSites g ⁻¹' {w | t ≤ (Finset.univ.erase g).card * d.q^2 -
        eventCount (Finset.univ.erase g) pairSelected w} := by
    intro s hs
    change t ≤ (Finset.univ.erase g).card * d.q^2 -
      eventCount (Finset.univ.erase g) pairSelected (pairSites g s)
    rw [← pairSupplyCount_eq_eventCount, hcard]
    dsimp [t]
    have hslack := mul_nonneg (sq_nonneg d.q) (sub_nonneg.mpr hnreal)
    dsimp only [Set.mem_ofPred_eq] at hs
    nlinarith
  have hn0 : n ≠ 0 := by linarith
  have hexp : -t^2 / (2 * (n / 4)) = -d.q^4 * n / 8 := by
    dsimp [t]
    field_simp [hn0]
    <;> ring
  apply (measureReal_mono hsub (measure_ne_top (sampleMeasure d) _)).trans
  change _ ≤ Real.exp (-t^2 / (2 * (n / 4))) at htail
  rw [hexp] at htail
  exact htail

/-- Item 4 of §5, fixed before every later query. -/
def PairSupplyEvent {G : Type*} [Fintype G] [AddCommGroup G]
    {m : ℕ} (d : Densities m) (s : Sample G m) : Prop :=
  ∀ g : G, d.q^2 * (Fintype.card G : ℝ) / 2 ≤ (pairSupplySet s g).card

theorem pairSupplyEvent_failure_probability {G : Type*} [Fintype G] [AddCommGroup G]
    {m : ℕ} (d : Densities m) (hn : 4 ≤ Fintype.card G) :
    (sampleMeasure (G := G) d).real {s | ¬ PairSupplyEvent d s} ≤
      (Fintype.card G : ℝ) * Real.exp (-d.q^4 * (Fintype.card G : ℝ) / 8) := by
  let bad : G → Set (Sample G m) := fun g =>
    {s | ((pairSupplySet s g).card : ℝ) < d.q^2 * (Fintype.card G : ℝ) / 2}
  have heq : {s : Sample G m | ¬ PairSupplyEvent d s} = ⋃ g, bad g := by
    ext s; simp only [PairSupplyEvent, not_forall, not_le, bad,
      Set.mem_iUnion, Set.mem_ofPred_eq]
  rw [heq]
  apply (measureReal_iUnion_fintype_le bad).trans
  calc
    (∑ g, (sampleMeasure d).real (bad g)) ≤
      ∑ _g : G, Real.exp (-d.q^4 * (Fintype.card G : ℝ) / 8) := by
        exact Finset.sum_le_sum (fun g _ => pairSupply_failure_probability d g hn)
    _ = _ := by simp

end
end EndpointLayeredSample
