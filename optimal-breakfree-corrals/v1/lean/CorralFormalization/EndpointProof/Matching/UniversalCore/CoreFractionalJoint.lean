import CorralFormalization.EndpointProof.Matching.UniversalCore.CoreFractionalRate
import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Joint

open MeasureTheory
open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFullProduct
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
noncomputable section

/-- The proved universal core and the proved fractional raw Fourier/degree
event hold together on one actual original sample and one augmentation,
with the ξ-based exponential failure rate. Neither event is an assumption. -/
theorem originalCore_and_fractionalRawEvent_final_rate
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [AddCommGroup G] [Fintype G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
        {s | ¬ OriginalCoreAndEvent q (EndpointFractionalRawEvent.fractionalRawEvent q) s} ≤
        Real.exp (-((xi q)^4/10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := originalCore_and_fractional_event_final_rate q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  apply hN G hodd hn (EndpointFractionalRawEvent.fractionalRawEvent q)
  have h := EndpointFractionalRawEvent.fractionalRawEvent_failure_probability
    (G := G) q hq0 hq1
  convert h using 1
  all_goals
    congr 2
    ring

/-- In particular the conjunction pays every paper-style coefficient
`λ⁴/10⁶` with `0 ≤ λ ≤ ξ(q)`. The choice of λ remains explicit; no
Pippenger parameter is constructed or assumed here. -/
theorem originalCore_and_fractionalRawEvent_at_smaller_rate
    (q lam : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hLam0 : 0 ≤ lam) (hLam : lam ≤ xi q) :
    ∃ N : ℕ, ∀ (G : Type*) [AddCommGroup G] [Fintype G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
        {s | ¬ OriginalCoreAndEvent q (EndpointFractionalRawEvent.fractionalRawEvent q) s} ≤
        Real.exp (-(lam^4/10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := originalCore_and_fractionalRawEvent_final_rate q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  apply (hN G hodd hn).trans
  apply Real.exp_le_exp.mpr
  have hpow : lam^4 ≤ (xi q)^4 := pow_le_pow_left₀ hLam0 hLam 4
  have hn0 : 0 ≤ (Fintype.card G : ℝ) := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hn0]

end
end EndpointMatching.UniversalCore
