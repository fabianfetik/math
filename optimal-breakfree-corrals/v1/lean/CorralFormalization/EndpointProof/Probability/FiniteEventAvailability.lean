import CorralFormalization.EndpointProof.Probability.JointAvailability
import CorralFormalization.EndpointProof.Probability.FlowAvailability

/-!
A finite family of differently shaped P/Q primitive events on a single
actual paper-parameter sample. No primitive event or packing is constructed
here; the per-event probability bounds are explicit inputs.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

namespace EndpointFullProduct

open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

/-- uniform exact-matching theorem's actual augmented sample law, with the parameter admissibility
proofs supplied by the existing paper-constants theorem. -/
def parameterizedFullMeasure (G : Type*) [Fintype G] [AddCommGroup G]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) : Measure (FullSample G) :=
  fullMeasure q eta (1/4) (tau q / SamplingConstants.rho q) (le_of_lt hq0) hq1
    (samplingParameters_admissible q hq0 hq1).1
    (samplingParameters_admissible q hq0 hq1).2.1
    (samplingParameters_admissible q hq0 hq1).2.2.1
    (samplingParameters_admissible q hq0 hq1).2.2.2.1
    (samplingParameters_admissible q hq0 hq1).2.2.2.2.1

/-- If every member of a fixed finite family has its own verified P- or
Q-type polynomial tail, one original sample has one augmentation satisfying
every member, except with at most the paper's final exponential error.
The event contracts may have different query types, support sizes and
reservoir demand lengths; no independence between events is assumed. -/
theorem original_finite_events_probability {T : Type*} [Fintype T]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (C : T → ℝ) (k : T → ℕ) (isP : T → Bool) :
    ∃ N : ℕ, ∀ (G : Type*) [Fintype G] [AddCommGroup G]
      (hn : N ≤ Fintype.card G) (events : T → FullSample G → Prop),
      (∀ i, (parameterizedFullMeasure G q hq0 hq1).real {ω | ¬ events i ω} ≤
        C i * (Fintype.card G : ℝ)^(k i) *
          Real.exp (-(pqTailRate q (isP i)) * (Fintype.card G : ℝ))) →
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ OriginalAdmitsEvents events s} ≤
      Real.exp (-((xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := finite_sampling_tails_pay_one_event q hq0 hq1 C k isP
  refine ⟨N, ?_⟩
  intro G _ _ hn events herror
  obtain ⟨hη0,hη1,ha,hb,hab,_,_,_,_⟩ := samplingParameters_admissible q hq0 hq1
  have herror' : ∀ i,
      (fullMeasure q eta (1/4) (tau q / SamplingConstants.rho q)
        (le_of_lt hq0) hq1 hη0 hη1 ha hb hab).real {ω | ¬ events i ω} ≤
        C i * (Fintype.card G : ℝ)^(k i) *
          Real.exp (-(pqTailRate q (isP i)) * (Fintype.card G : ℝ)) := by
    intro i
    simpa only [parameterizedFullMeasure] using herror i
  have hjoint := original_sample_admits_finite_events q eta (1/4)
    (tau q / SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
    events (fun i ↦ C i * (Fintype.card G : ℝ)^(k i) *
      Real.exp (-(pqTailRate q (isP i)) * (Fintype.card G : ℝ))) herror'
  exact hjoint.trans (hN (Fintype.card G) hn)

end
end EndpointFullProduct
