import CorralFormalization.EndpointProof.Matching.UniversalCore.ExactFromRawL2
import CorralFormalization.EndpointProof.Matching.Fractional.PhysicalFractionalSupplier
import CorralFormalization.EndpointProof.Matching.Fractional.Fourier.ActualRawSpectral

open MeasureTheory
open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.ActualRemainder EndpointMatching.Fractional.Rounding
open EndpointMatching.Fractional.Fourier
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
noncomputable section
universe u

/-- The actual original Fourier/degree event proves the full robust
fractional supplier for every later target and every admissible later edge
ban. No independence between roles, target Fourier assumption, or external
matching theorem is needed. -/
theorem physicalRobustFractionalEvent_of_raw
    {G : Type u} [Fintype G] [AddCommGroup G]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) (s : OriginalSample G)
    (hraw : fractionalRawEvent q s) : PhysicalRobustFractionalEvent q s :=
  physicalRobustFractionalEvent_of_raw_and_L2 q hq0 hq1 s hraw
    (fractionalRawEvent_actualRawMatrix_L2_le hraw)

/-- The full paper fractional supplier, including any later admissible edge
ban, holds with its stated failure bound for every finite abelian group.
Zero may occur in either endpoint role. -/
theorem physicalRobustFractionalEvent_failure_probability
    {G : Type u} [Fintype G] [AddCommGroup G]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
      {s | ¬ PhysicalRobustFractionalEvent q s} ≤
      18 * (Fintype.card G : ℝ) *
        Real.exp (-q^8 * (Fintype.card G : ℝ) / (4*10^10)) := by
  have hsub : {s : OriginalSample G | ¬ PhysicalRobustFractionalEvent q s} ⊆
      {s | ¬ fractionalRawEvent q s} := by
    intro s hbad hraw
    exact hbad (physicalRobustFractionalEvent_of_raw q hq0 hq1 s hraw)
  exact (measureReal_mono hsub
    (measure_ne_top (originalMeasure (G := G) q (le_of_lt hq0) hq1) _)).trans
    (fractionalRawEvent_failure_probability q hq0 hq1)

/-- uniform exact-matching theorem's original-law physical statement for all sufficiently large odd
abelian groups, with the named ξ-based failure rate. The only remaining
nonstandard theorem input is the explicitly stated published AKS
near-regular hypergraph matching result. -/
theorem original_exact_matching_probability
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
        {s | ¬ PhysicalExactEvent q s} ≤
        Real.exp (-((xi q)^4/10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := original_exact_probability_of_raw_L2 hAKS q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  apply hN G hodd hn
  intro s hraw
  exact fractionalRawEvent_actualRawMatrix_L2_le hraw

/-- exact-matching also holds at any explicitly chosen nonnegative paper rate
`λ⁴/10⁶` with `λ ≤ ξ(q)`; no Pippenger parameter is fabricated. -/
theorem original_exact_matching_probability_at_smaller_rate
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (q lam : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hLam0 : 0 ≤ lam) (hLam : lam ≤ xi q) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
        {s | ¬ PhysicalExactEvent q s} ≤
        Real.exp (-(lam^4/10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := original_exact_matching_probability hAKS q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  apply (hN G hodd hn).trans
  apply Real.exp_le_exp.mpr
  have hpow : lam^4 ≤ (xi q)^4 := pow_le_pow_left₀ hLam0 hLam 4
  have hn0 : 0 ≤ (Fintype.card G : ℝ) := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hn0]

end
end EndpointMatching.UniversalCore
