import CorralFormalization.EndpointProof.Sampling.OriginalLaw

/-!
Query-dependent common availability on the actual group-indexed source law.
The deterministic orbit packings, demands, and mean/budget separation remain
explicit inputs. This does not assert the missing matching or factor supplier.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

namespace EndpointFullProduct

open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open EndpointReservoirAvailability

noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G]

def fullLabels (ω : FullSample G) : OddOrbit G → Label :=
  fun o ↦ sevenLabel ((regroup ω).1 o)

theorem fullLabels_measurePreserving (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1)
    (hP : (p : ℝ) = rho q η * a) (hQ : (τ : ℝ) = rho q η * b) :
    MeasurePreserving (fullLabels (G := G))
      (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab)
      (orbitMeasure p τ h) :=
  (original_product_to_orbitMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ).comp
    (blocks_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab)

/-- The support is a finite subset of the actual group G containing both signs.
Different queries may use overlapping packings. -/
def FullAvailable {Q I J : Type*} [Fintype J]
    (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label)
    (budget : ℕ) (ω : FullSample G) : Prop :=
  UniversallyAvailable (fun u ↦ support (e u) orbitPlace)
    (fun u ω i ↦ project (e u) (fullLabels ω) i = demand u i) budget ω

/-- The common availability event under the actual G-indexed law including zero.
No independence between queries or between a later forbidden set and the sample
is assumed. The exponent is the proved additive Hoeffding exponent. -/
theorem full_sample_universal_availability {Q I J : Type*}
    [Fintype Q] [Fintype I] [Fintype J] [DecidableEq I]
    (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1)
    (hP : (p : ℝ) = rho q η * a) (hQ : (τ : ℝ) = rho q η * b)
    (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label)
    (budget : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hmean : ∀ u, (budget : ℝ) ≤ (∑ i, successProbability p τ (demand u i)) - t) :
    (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω : FullSample G | ¬ FullAvailable e demand budget ω} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) := by
  have hp := fullLabels_measurePreserving hodd
    q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ
  have heq := hp.measureReal_preimage
    (s := {ω : OddOrbit G → Label |
      ¬ UniversallyAvailable (fun u ↦ support (e u) orbitPlace)
        (fun u ω i ↦ project (e u) ω i = demand u i) budget ω}) (by measurability)
  have hh := shared_universal_availability p τ h e orbitPlace demand budget t ht hmean
  rw [← heq] at hh
  exact hh

/-- Project away all auxiliary randomness by an existential augmentation.
This statement still asks only for packed availability, not exact matching. -/
def OriginalAdmitsAvailable {Q I J : Type*} [Fintype J]
    (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label)
    (budget : ℕ) (s : OriginalSample G) : Prop :=
  ∃ ω : FullSample G, originalProcess ω = s ∧ FullAvailable e demand budget ω

theorem original_sample_admits_availability {Q I J : Type*}
    [Fintype Q] [Fintype I] [Fintype J] [DecidableEq I]
    (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1)
    (hP : (p : ℝ) = rho q η * a) (hQ : (τ : ℝ) = rho q η * b)
    (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label)
    (budget : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hmean : ∀ u, (budget : ℝ) ≤ (∑ i, successProbability p τ (demand u i)) - t) :
    (originalMeasure q hq0 hq1).real
      {s : OriginalSample G | ¬ OriginalAdmitsAvailable e demand budget s} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) := by
  have hp := originalProcess_measurePreserving (G := G)
    q η a b hq0 hq1 hη0 hη1 ha hb hab
  rw [← hp.measureReal_preimage (by measurability)]
  apply le_trans (measureReal_mono ?_)
    (full_sample_universal_availability hodd q η a b hq0 hq1 hη0 hη1 ha hb hab
      p τ h hP hQ e demand budget t ht hmean)
  intro ω hbad hgood
  exact hbad ⟨ω, rfl, hgood⟩

/-- A nonvacuous concrete original-coordinate-and-coin realization, with the
entire common-event quantifier, once the explicit finite error is below one. -/
theorem exists_full_available {Q I J : Type*}
    [Fintype Q] [Fintype I] [Fintype J] [DecidableEq I]
    (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1)
    (hP : (p : ℝ) = rho q η * a) (hQ : (τ : ℝ) = rho q η * b)
    (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label)
    (budget : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hmean : ∀ u, (budget : ℝ) ≤ (∑ i, successProbability p τ (demand u i)) - t)
    (hsmall : (Fintype.card Q : ℝ) *
      Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) < 1) :
    ∃ ω : FullSample G, FullAvailable e demand budget ω := by
  by_contra hn
  have hbad : {ω : FullSample G | ¬ FullAvailable e demand budget ω} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro hgood
    exact hn ⟨ω, hgood⟩
  have hh := full_sample_universal_availability hodd q η a b hq0 hq1 hη0 hη1 ha hb hab
    p τ h hP hQ e demand budget t ht hmean
  rw [hbad] at hh
  have hh' : (1 : ℝ) ≤ (Fintype.card Q : ℝ) *
      Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) := by simpa using hh
  linarith

end
end EndpointFullProduct
