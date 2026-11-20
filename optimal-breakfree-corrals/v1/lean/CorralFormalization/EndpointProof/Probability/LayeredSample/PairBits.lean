import CorralFormalization.EndpointProof.Probability.LayeredSample.PairSupply

/-! The exact independent Bernoulli-`q²` process behind the pair supply. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointOriginalReservoir EndpointFullProduct

noncomputable section

theorem eventMass_compl {A : Type*} [Fintype A] (L : FiniteLaw A) (P : A → Prop) :
    eventMass L.weight (fun a => ¬ P a) = 1 - eventMass L.weight P := by
  have h : eventMass L.weight (fun a => ¬ P a) + eventMass L.weight P = 1 := by
    unfold eventMass
    rw [← Finset.sum_add_distrib, ← L.total]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : P a <;> simp [h]
  linarith

theorem Densities.q_sq_le_one {m : ℕ} (d : Densities m) : d.q^2 ≤ 1 := by
  have hq1 : d.q ≤ 1 := d.q_le_half.trans (by norm_num)
  have h := mul_nonneg d.q_nonneg (sub_nonneg.mpr hq1)
  nlinarith

def pairBit {m : ℕ} (z : VertexRole m × ColourRole m) : Bool := decide (pairSelected z)

theorem pairBit_measurePreserving {m : ℕ} (d : Densities m) :
    MeasurePreserving pairBit (pairLaw d).measure
      (coinLaw (d.q^2) (sq_nonneg _) d.q_sq_le_one).measure := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_measureReal_singleton
  intro b
  rw [map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton _)]
  change (pairLaw d).measure.real {z | pairBit z = b} =
    (coinLaw (d.q^2) (sq_nonneg _) d.q_sq_le_one).measure.real {b' | b' = b}
  rw [FiniteLaw.real_event, FiniteLaw.real_event, eventMass_eq]
  cases b
  · have heq : eventMass (pairLaw d).weight (fun z => pairBit z = false) =
        eventMass (pairLaw d).weight (fun z => ¬ pairSelected z) := by
      exact eventMass_congr _ (fun z => by simp [pairBit])
    rw [heq, eventMass_compl, pairSelected_mass]
    rfl
  · have heq : eventMass (pairLaw d).weight (fun z => pairBit z = true) =
        eventMass (pairLaw d).weight pairSelected := by
      exact eventMass_congr _ (fun z => by simp [pairBit])
    rw [heq, pairSelected_mass]
    rfl

def pairBits {G : Type*} [AddCommGroup G] {m : ℕ}
    (g : G) (s : Sample G m) : G → Bool := fun a => pairBit (pairSites g s a)

/-- Literal independent Bernoulli-`q²` bits over all `a ∈ G` for any
fixed root `g`.  Deleting only the bit at `a=g` gives exactly the usual
`n-1`-trial binomial sampling scheme for `pairSupplySet s g`. -/
theorem pairBits_measurePreserving {G : Type*} [Fintype G] [AddCommGroup G]
    {m : ℕ} (d : Densities m) (g : G) :
    MeasurePreserving (pairBits g) (sampleMeasure (G := G) d)
      (Measure.pi fun _ : G =>
        (coinLaw (d.q^2) (sq_nonneg _) d.q_sq_le_one).measure) := by
  exact (measurePreserving_pi _ _ (fun _ : G => pairBit_measurePreserving d)).comp
    (pairSites_measurePreserving d g)

theorem pairSupplySet_eq_pairBits {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (s : Sample G m) (g : G) :
    pairSupplySet s g = (Finset.univ.erase g).filter (fun a => pairBits g s a = true) := by
  rw [pairSupplySet_eq]
  apply Finset.filter_congr
  intro a _
  simp [pairBits, pairBit]

end
end EndpointLayeredSample
