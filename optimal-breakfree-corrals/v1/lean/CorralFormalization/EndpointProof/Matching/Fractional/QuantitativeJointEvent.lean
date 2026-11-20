import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.NativeSource
import CorralFormalization.EndpointProof.Matching.UniformExactMatching

/-! Assemble the original-sample probability, robust fractional supplier,
and quantitative actual remainder on one common event. The external
source-shaped AKS one-bite theorem remains an explicit argument. -/

open MeasureTheory
open scoped Classical BigOperators
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.UniversalCore EndpointMatching.Fractional.Rounding
open EndpointMatching.Fractional.ActualRemainder AKSSubsetTransport

namespace EndpointMatching.Fractional.JointRawEvent
noncomputable section
universe u

def QuantitativeActualRemainderEvent
    {G : Type u} [Fintype G] [AddCommGroup G]
    (q : ℝ) (Cstar : ℝ) (s : OriginalSample G) : Prop :=
  ∀ (X Y C : Finset G) (A P : Finset (Vertex G)) (M₀ : Matching P)
    (F : Finset (Finset (Vertex G))),
    Disjoint X Y → (0 : G) ∉ C → X.card = Y.card → X.card = C.card →
    (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x →
    Balanced A → (∑ v ∈ A, v.2 = 0) → A ⊆ signedTarget X Y C →
    P ⊆ signedTarget X Y C \ A → (∀ E ∈ M₀.edges, E ∉ F) →
    (∀ z, ((banAt F z).card : ℝ) ≤ beta q * (Fintype.card G : ℝ)) →
    (taggedDistance (signedRawTarget s) (signedTarget X Y C) : ℝ) + (A.card : ℝ) +
      3 * (M₀.edges.card : ℝ) + (zeroCharge (residual (signedTarget X Y C) A P) : ℝ)
        ≤ rho q * (Fintype.card G : ℝ) →
    ∃ M : ActualRemainderMatching (signedTarget X Y C) A P M₀ F,
      (∀ p : Fin 3, ((slice (residual (signedTarget X Y C) A M.covered) p).card : ℝ)
        ≤ Real.sqrt 6 * Cstar * remainderProfile (Fintype.card G)) ∧
      ((residual (signedTarget X Y C) A M.covered).card : ℝ) ≤
        3 * (Real.sqrt 6 * Cstar) * remainderProfile (Fintype.card G)

/-- The paper's `+3` allowance pays for the exact zero-or-three charge. -/
theorem three_budget_controls_zeroCharge
    {G : Type u} [AddCommGroup G] (W : Finset (Vertex G))
    {d a p bound : ℝ} (h : d + a + 3*p + 3 ≤ bound) :
    d + a + 3*p + (zeroCharge W : ℝ) ≤ bound := by
  have hz : (zeroCharge W : ℝ) ≤ 3 := by
    exact_mod_cast zeroCharge_le_three W
  linarith

/-- If the remaining inventory is zero-free, no charge is needed. -/
theorem zero_free_budget_controls_zeroCharge
    {G : Type u} [AddCommGroup G] (W : Finset (Vertex G))
    {d a p bound : ℝ} (hzero : ∀ v ∈ W, v.2 ≠ 0)
    (h : d + a + 3*p ≤ bound) :
    d + a + 3*p + (zeroCharge W : ℝ) ≤ bound := by
  have hz : zeroCharge W = 0 := by
    unfold zeroCharge
    exact if_pos hzero
  simpa only [hz, Nat.cast_zero, add_zero] using h

theorem common_fractional_and_quantitative_failure_probability
    (hsource : ∃ K Dmin C Cw : ℝ, 0 < K ∧ 0 ≤ C ∧ 0 ≤ Cw ∧
      NativeBiteTheorem.{u} K Dmin C Cw) :
    ∃ (Dstar : ℕ) (Cstar : ℝ), 3 ≤ Dstar ∧ 0 < Cstar ∧
      ∀ (G : Type u) [Fintype G] [AddCommGroup G]
        (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2),
        6 * (Dstar : ℝ) ≤ q^2 * (Fintype.card G : ℝ) →
        (originalMeasure (G := G) q hq0.le hq1).real
          {s | ¬ (PhysicalRobustFractionalEvent q s ∧
            QuantitativeActualRemainderEvent q Cstar s)} ≤
          18 * (Fintype.card G : ℝ) *
            Real.exp (-q^8 * (Fintype.card G : ℝ) / (4*10^10)) := by
  obtain ⟨Dstar, Cstar, hDstar, hCstar, happly⟩ :=
    AKSSourceIteration.physical_actual_remainder_from_native_bite hsource
  refine ⟨Dstar, Cstar, hDstar, hCstar, ?_⟩
  intro G _ _ q hq0 hq1 hsize
  let μ := originalMeasure (G := G) q hq0.le hq1
  have hsub : {s : OriginalSample G | ¬ (PhysicalRobustFractionalEvent q s ∧
      QuantitativeActualRemainderEvent q Cstar s)} ⊆
      {s | ¬ fractionalRawEvent q s} := by
    intro s hbad hraw
    apply hbad
    refine ⟨physicalRobustFractionalEvent_of_raw q hq0 hq1 s hraw, ?_⟩
    intro X Y C A P M₀ F hdis hzero hXY hXC hsum hA hAsum hAT hP hM hF hbudget
    exact happly G q s X Y C A P M₀ F hq0 hq1 hraw hdis hzero hXY hXC hsum
      hA hAsum hAT hP hM hF hbudget hsize
  have hprob := measureReal_mono hsub (measure_ne_top μ _)
  exact hprob.trans (fractionalRawEvent_failure_probability q hq0 hq1)

end
end EndpointMatching.Fractional.JointRawEvent
