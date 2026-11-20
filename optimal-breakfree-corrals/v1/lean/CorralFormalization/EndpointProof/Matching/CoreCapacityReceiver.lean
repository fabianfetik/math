import CorralFormalization.EndpointProof.Matching.AbsorptionAssembly.PhysicalReceiver
import CorralFormalization.EndpointProof.Probability.PairedCoverAtCoreCapacity

/-!
Deterministic receiver at the smaller core capacity. The two suppliers
remain explicit assumptions: this module does not prove their existence or
the probability of a common event.
-/

open scoped Classical BigOperators

namespace EndpointMatching.AbsorptionAssembly

open EndpointFlow.AbelianTransport
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- Total symmetric-difference distance between the three original sample
parts and their physical targets. -/
def physicalEditDistance (RX RY RC X Y C : Finset G) : ℕ :=
  (RX \ X).card + (X \ RX).card +
  (RY \ Y).card + (Y \ RY).card +
  (RC \ C).card + (C \ RC).card

omit [AddCommGroup G] in
/-- The sample elements missing from the actual target are no more numerous
than all symmetric-difference edits. -/
theorem missing_sample_edits_le_distance (RX RY RC X Y C : Finset G) :
    (RX \ X).card + (RY \ Y).card + (RC \ C).card ≤
      physicalEditDistance RX RY RC X Y C := by
  unfold physicalEditDistance
  omega

/-- The physical exact-matching conclusion follows from the small-capacity
core and later near-matching suppliers at the original exact-matching edit radius. The
capacity is the integer floor of `kappa q * n`. -/
theorem physical_exact_of_core_capacity_suppliers
    {RX RY RC X Y C : Finset G} {rawMinus : Finset (Vertex G)}
    (q : ℝ) (n coreBound : ℕ)
    (hminus : rawMinus ⊆ signedTarget RX RY RC)
    (hcore : RawCoreSupply rawMinus ⌊kappa q * (n : ℝ)⌋₊ coreBound)
    (hdistance : (physicalEditDistance RX RY RC X Y C : ℝ) ≤
      (1 / 10^6 : ℝ) * kappa q * (n : ℝ))
    (hlarge : (2 : ℝ) ≤ kappa q * (n : ℝ))
    (hXY : X.card = Y.card) (hXC : X.card = C.card)
    (hchecksum : (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x)
    (hnear : ∀ A : Finset (Vertex G), A ⊆ signedTarget X Y C →
      (∀ v ∈ A, v.2 ≠ 0) → Balanced A → (∑ v ∈ A, v.2 = 0) →
      A.card ≤ coreBound →
      Nonempty (CompatibleNearMatching (signedTarget X Y C) A
        ⌊kappa q * (n : ℝ)⌋₊)) :
    Nonempty (PhysicalDifferenceMatching X Y C) := by
  have hedits : (((RX \ X).card + (RY \ Y).card + (RC \ C).card : ℕ) : ℝ) ≤
      (1 / 10^6 : ℝ) * kappa q * (n : ℝ) := by
    apply le_trans _ hdistance
    exact_mod_cast missing_sample_edits_le_distance RX RY RC X Y C
  have hexclusion := edit_count_add_zero_le_core_capacity q n
    ((RX \ X).card + (RY \ Y).card + (RC \ C).card) hedits hlarge
  exact physical_exact_of_suppliers hminus hcore hexclusion hXY hXC hchecksum hnear

end
end EndpointMatching.AbsorptionAssembly
