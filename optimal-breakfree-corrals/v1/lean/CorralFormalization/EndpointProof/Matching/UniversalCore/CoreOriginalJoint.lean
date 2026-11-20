import CorralFormalization.EndpointProof.Matching.UniversalCore.CorePhysicalReceiver

open MeasureTheory
open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFullProduct
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- On a good original sample there is one augmentation whose universal
core is good and the same original sample has property E. -/
def OriginalCoreAndEvent (q : ℝ) (E : OriginalSample G → Prop)
    (s : OriginalSample G) : Prop :=
  ∃ ω : FullSample G, originalProcess ω = s ∧
    UniversalCoreEvent (tau q) ω ∧ E s

/-- No independence is used to combine the proved core event with any
separately established event of the very same original sample. This is a
conditional probability composition, not a proof of E. -/
theorem originalCore_and_event_failure_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hodd : Odd (Fintype.card G))
    (hn : 1152 ≤ Fintype.card G)
    (hnlarge : (4000 : ℝ) ≤ (tau q)^2 * Fintype.card G)
    (hsel : selectorSameSampleThreshold q ≤ Fintype.card G)
    (E : OriginalSample G → Prop) (e : ℝ)
    (hE : (originalMeasure (G := G) q (le_of_lt hq0) hq1).real {s | ¬ E s} ≤ e) :
    (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
      {s | ¬ OriginalCoreAndEvent q E s} ≤ coreFailureBound q (Fintype.card G) + e := by
  obtain ⟨hη0,hη1,ha,hb,hab,_,_,_,_⟩ := samplingParameters_admissible q hq0 hq1
  let μ := fullMeasure (G := G) q eta (1/4) (tau q / SamplingConstants.rho q)
    (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
  have hp := originalProcess_measurePreserving (G := G) q eta (1/4)
    (tau q / SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
  have hEfull : μ.real {ω | ¬ E (originalProcess ω)} ≤ e := by
    have heq := hp.measureReal_preimage (s := {s | ¬ E s}) (by measurability)
    exact le_of_eq_of_le heq hE
  have hC := fullCore_explicit_failure_probability q hq0 hq1 hodd hn hnlarge hsel
  have hCfull : μ.real {ω | ¬ UniversalCoreEvent (tau q) ω} ≤
      coreFailureBound q (Fintype.card G) := by
    simpa only [μ, parameterizedFullMeasure] using hC
  have hjoint := original_sample_admits_two_events q eta (1/4)
    (tau q / SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
    (fun ω : FullSample G => UniversalCoreEvent (tau q) ω)
    (fun ω => E (originalProcess ω)) (coreFailureBound q (Fintype.card G)) e hCfull hEfull
  have hequiv : {s : OriginalSample G | ¬ OriginalCoreAndEvent q E s} =
      {s : OriginalSample G | ¬ OriginalAdmitsBoth
        (fun ω => UniversalCoreEvent (tau q) ω) (fun ω => E (originalProcess ω)) s} := by
    ext s
    simp only [Set.mem_ofPred_eq, OriginalCoreAndEvent, OriginalAdmitsBoth]
    constructor
    · intro hn ⟨ω,heq,hc,hEω⟩
      exact hn ⟨ω,heq,hc,heq ▸ hEω⟩
    · intro hn ⟨ω,heq,hc,hEs⟩
      exact hn ⟨ω,heq,hc,heq.symm ▸ hEs⟩
  rw [hequiv]
  exact hjoint

end
end EndpointMatching.UniversalCore
