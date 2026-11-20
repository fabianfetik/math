import CorralFormalization.EndpointProof.Sampling.OriginalReservoir
import CorralFormalization.EndpointProof.Sampling.SharedSample

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

namespace EndpointReservoirAvailability

open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample

noncomputable section

/-- The child-label order is P_A,P_B,P_C,Q_A,Q_B,Q_C,neither. -/
def encodeChild : Option (Part × Bool) → Label
  | none => 6
  | some (p,false) => ⟨p.val, by omega⟩
  | some (p,true) => ⟨p.val+3, by omega⟩

theorem encodeChild_bijective : Function.Bijective encodeChild := by decide

def sevenLabel (s : OrbitInput) : Label := encodeChild (childLabel s)

theorem encoded_fiber_mass (q η a b : ℝ) (l : Option (Part × Bool)) :
    eventMass (orbitInputWeight q η a b) (fun s ↦ sevenLabel s = encodeChild l) =
      eventMass (orbitInputWeight q η a b) (fun s ↦ childLabel s = l) := by
  apply eventMass_congr
  intro s
  exact encodeChild_bijective.injective.eq_iff

theorem sevenLabel_mass (q η a b : ℝ) (p τ : ℝ≥0)
    (h : 3*p+3*τ ≤ 1) (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (l : Label) :
    eventMass (orbitInputWeight q η a b) (fun s ↦ sevenLabel s = l) =
      (labelWeights p τ l : ℝ) := by
  fin_cases l
  · change eventMass _ (fun s ↦ sevenLabel s = encodeChild (some (0,false))) = _
    rw [encoded_fiber_mass, childLabel_P_mass]
    simpa [labelWeights] using hP.symm
  · change eventMass _ (fun s ↦ sevenLabel s = encodeChild (some (1,false))) = _
    rw [encoded_fiber_mass, childLabel_P_mass]
    simpa [labelWeights] using hP.symm
  · change eventMass _ (fun s ↦ sevenLabel s = encodeChild (some (2,false))) = _
    rw [encoded_fiber_mass, childLabel_P_mass]
    simpa [labelWeights] using hP.symm
  · change eventMass _ (fun s ↦ sevenLabel s = encodeChild (some (0,true))) = _
    rw [encoded_fiber_mass, childLabel_Q_mass]
    simpa [labelWeights] using hQ.symm
  · change eventMass _ (fun s ↦ sevenLabel s = encodeChild (some (1,true))) = _
    rw [encoded_fiber_mass, childLabel_Q_mass]
    simpa [labelWeights] using hQ.symm
  · change eventMass _ (fun s ↦ sevenLabel s = encodeChild (some (2,true))) = _
    rw [encoded_fiber_mass, childLabel_Q_mass]
    simpa [labelWeights] using hQ.symm
  · change eventMass _ (fun s ↦ sevenLabel s = encodeChild none) = _
    rw [encoded_fiber_mass, childLabel_none_mass]
    change 1 - 3*rho q η*(a+b) = ((1 - (3*p+3*τ) : ℝ≥0) : ℝ)
    rw [NNReal.coe_sub h]
    simp only [NNReal.coe_one, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, hP, hQ]
    ring

/-- The exact measure law for block availability is derived
from original coordinate variables and coins, not supplied as a premise. -/
theorem original_to_sevenLabel_measurePreserving
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b) :
    MeasurePreserving sevenLabel
      (orbitInputLaw q η a b hq0 hq1 hη0 hη1 ha hb hab).measure
      (labelMeasure p τ h) := by
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_measureReal_singleton
  intro l
  rw [map_measureReal_apply (by fun_prop) (measurableSet_singleton l)]
  change (orbitInputLaw q η a b hq0 hq1 hη0 hη1 ha hb hab).measure.real
      {s | sevenLabel s = l} = _
  rw [FiniteLaw.real_event, orbitInputLaw_weight, sevenLabel_mass q η a b p τ h hP hQ]
  rw [measureReal_def, labelMeasure_singleton]
  simp

/-- Full original product sample to a single categorical orbit sample. -/
theorem original_product_to_orbitMeasure {O : Type*} [Fintype O]
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b) :
    MeasurePreserving (fun ω (o : O) ↦ sevenLabel (ω o))
      (originalProductMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab)
      (orbitMeasure p τ h) := by
  exact measurePreserving_pi _ _ (fun _ ↦
    original_to_sevenLabel_measurePreserving q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ)

/-- Combined reservoir and availability event: the common event lives on the original
coordinate-and-coin sample. Queries and forbidden supports may then be
chosen after seeing that sample. -/
theorem original_sample_universal_availability {Q O I J K : Type*}
    [Fintype Q] [Fintype O] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq K]
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (e : Q → I × J ↪ O) (place : O × Bool ↪ K)
    (demand : Q → I → J → Label) (budget : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hmean : ∀ u, (budget : ℝ) ≤ (∑ i, successProbability p τ (demand u i)) - t) :
    (originalProductMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω : O → OrbitInput |
        ¬ UniversallyAvailable (fun u ↦ support (e u) place)
          (fun u ω i ↦ project (e u) (fun o ↦ sevenLabel (ω o)) i = demand u i) budget ω} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-t^2 / (2 * (Fintype.card I : ℝ) * (1/4))) := by
  have hp := original_product_to_orbitMeasure (O := O)
    q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ
  have heq := hp.measureReal_preimage
    (s := {ω : O → Label |
      ¬ UniversallyAvailable (fun u ↦ support (e u) place)
        (fun u ω i ↦ project (e u) ω i = demand u i) budget ω}) (by measurability)
  have hh := shared_universal_availability p τ h e place demand budget t ht hmean
  rw [← heq] at hh
  exact hh

end
end EndpointReservoirAvailability
