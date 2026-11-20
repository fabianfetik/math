import CorralFormalization.EndpointProof.Matching.UniversalCore.ExactFromFractionalWeights
import CorralFormalization.EndpointProof.Matching.UniversalCore.CoreFractionalJoint

open MeasureTheory
open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.ActualRemainder EndpointMatching.Fractional.Rounding
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
noncomputable section
universe u

/-- uniform exact-matching theorem's physical exact-matching conclusion, uniformly over all targets
chosen after exposure of the original sample. -/
def PhysicalExactEvent {G : Type u} [Fintype G] [AddCommGroup G]
    (q : ℝ) (s : OriginalSample G) : Prop :=
  ∀ X Y C : Finset G,
    Disjoint X Y → (0 : G) ∉ C → X.card = Y.card → X.card = C.card →
    (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x →
    (physicalEditDistance (originalTailSet s) (originalHeadSet s) (originalColourSet s) X Y C : ℝ) ≤
      (1 / 10^6 : ℝ) * kappa q * (Fintype.card G : ℝ) →
    Nonempty (PhysicalDifferenceMatching X Y C)

/-- The paper's whole exact-matching probability and quantifier contract,
with exactly two visible remaining inputs: the external near-regular AKS
result and an actual fractional-perfect-weight theorem on good original
samples. The latter must hold for every later nearby target; it is not an
assumption of any integral matching or of the uniform exact-matching theorem itself. -/
theorem original_exact_probability_of_fractional_weights
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (∀ s : OriginalSample G, fractionalRawEvent q s →
        ActualFractionalWeights (signedRawTarget s) ∅ q
          (EndpointFractionalRawEvent.rho q * (Fintype.card G : ℝ))) →
      (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
        {s | ¬ PhysicalExactEvent q s} ≤
        Real.exp (-((xi q)^4/10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨Nexact,hNexact⟩ := physical_exact_on_shared_core_and_fractionalWeights hAKS q hq0 hq1
  obtain ⟨Nj,hNj⟩ := originalCore_and_fractionalRawEvent_final_rate q hq0 hq1
  refine ⟨max Nexact Nj, ?_⟩
  intro G _ _ hodd hn hweights
  have hnexact : Nexact ≤ Fintype.card G := by omega
  have hnj : Nj ≤ Fintype.card G := by omega
  have hsub : {s : OriginalSample G | ¬ PhysicalExactEvent q s} ⊆
      {s | ¬ OriginalCoreAndEvent q (fractionalRawEvent q) s} := by
    intro s hbad hgood
    obtain ⟨ω,hω,hcore,hraw⟩ := hgood
    have hraw' : fractionalRawEvent q (originalProcess ω) := by simpa [hω] using hraw
    have hw := hweights s hraw
    have hw' : ActualFractionalWeights (signedRawTarget (originalProcess ω)) ∅ q
        (EndpointFractionalRawEvent.rho q * (Fintype.card G : ℝ)) := by
      simpa only [hω] using hw
    apply hbad
    intro X Y C hdisjoint hzero hXY hXC hsum hd
    have hd' : (physicalEditDistance (originalTailSet (originalProcess ω))
        (originalHeadSet (originalProcess ω)) (originalColourSet (originalProcess ω)) X Y C : ℝ) ≤
        (1 / 10^6 : ℝ) * kappa q * (Fintype.card G : ℝ) := by simpa only [hω] using hd
    exact hNexact G hnexact ω hcore hraw' hw' X Y C hdisjoint hzero hXY hXC hsum hd'
  have hprob := measureReal_mono hsub (measure_ne_top (originalMeasure (G := G) q (le_of_lt hq0) hq1) _)
  exact hprob.trans (hNj G hodd hnj)

/-- The ξ-bound is at least as strong as the paper's `λ⁴/10⁶` bound for
every nonnegative `λ ≤ ξ`. No choice of Pippenger's parameter is fabricated. -/
theorem original_exact_probability_of_fractional_weights_at_smaller_rate
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (q lam : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hLam0 : 0 ≤ lam) (hLam : lam ≤ xi q) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (∀ s : OriginalSample G, fractionalRawEvent q s →
        ActualFractionalWeights (signedRawTarget s) ∅ q
          (EndpointFractionalRawEvent.rho q * (Fintype.card G : ℝ))) →
      (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
        {s | ¬ PhysicalExactEvent q s} ≤
        Real.exp (-(lam^4/10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := original_exact_probability_of_fractional_weights hAKS q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn hweights
  apply (hN G hodd hn hweights).trans
  apply Real.exp_le_exp.mpr
  have hpow : lam^4 ≤ (xi q)^4 := pow_le_pow_left₀ hLam0 hLam 4
  have hn0 : 0 ≤ (Fintype.card G : ℝ) := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hn0]

end
end EndpointMatching.UniversalCore
