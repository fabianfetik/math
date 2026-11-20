import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.RawAdapter
import CorralFormalization.EndpointProof.Matching.UniformExactMatching

/-! Connect the proved raw-event fractional supplier to the quantitative
actual-remainder receiver. The near-regular AKS theorem remains an explicit
external argument. Target, reserve, frozen edges and bounded-root bans are
all chosen after the same original raw event. -/

open scoped Classical BigOperators
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.UniversalCore EndpointMatching.Fractional.RobustWeights
open EndpointMatching.Fractional.Fourier EndpointMatching.Fractional.Rounding

namespace EndpointMatching.Fractional.ActualRemainder
noncomputable section
universe u

theorem physical_actual_remainder_from_raw_event
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C) :
    ∃ (Dstar : ℕ) (Cstar : ℝ), 3 ≤ Dstar ∧ 0 < Cstar ∧
      ∀ (H : Type u) [Fintype H] [AddCommGroup H]
        (q : ℝ) (s : OriginalSample H) (X Y C : Finset H)
        (A P : Finset (Vertex H)) (M₀ : Matching P) (F : Finset (Finset (Vertex H))),
        0 < q → q ≤ 1 / 2 → fractionalRawEvent q s →
        Disjoint X Y → (0 : H) ∉ C → X.card = Y.card → X.card = C.card →
        (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x →
        Balanced A → (∑ v ∈ A, v.2 = 0) → A ⊆ signedTarget X Y C →
        P ⊆ signedTarget X Y C \ A → (∀ E ∈ M₀.edges, E ∉ F) →
        (∀ z, ((banAt F z).card : ℝ) ≤ beta q * (Fintype.card H : ℝ)) →
        (taggedDistance (signedRawTarget s) (signedTarget X Y C) : ℝ) + (A.card : ℝ) +
          3 * (M₀.edges.card : ℝ) + (zeroCharge (residual (signedTarget X Y C) A P) : ℝ)
            ≤ rho q * (Fintype.card H : ℝ) →
        6 * (Dstar : ℝ) ≤ q ^ 2 * (Fintype.card H : ℝ) →
        ∃ M : ActualRemainderMatching (signedTarget X Y C) A P M₀ F,
          (∀ p : Fin 3, ((slice (residual (signedTarget X Y C) A M.covered) p).card : ℝ)
            ≤ Real.sqrt 6 * Cstar * remainderProfile (Fintype.card H)) ∧
          ((residual (signedTarget X Y C) A M.covered).card : ℝ) ≤
            3 * (Real.sqrt 6 * Cstar) * remainderProfile (Fintype.card H) := by
  classical
  obtain ⟨Dstar, Cstar, hstar, hCstar, hrem⟩ :=
    physical_actual_remainder_on_raw_event hAKS
  refine ⟨Dstar, Cstar, hstar, hCstar, ?_⟩
  intro H _ _ q s X Y C A P M₀ F hq hqhalf hraw hXY hC hsizeXY hsizeXC hsum
    hA hAsum hAT hP hallowed hban hbudget hlarge
  have hsmall := actualRawSmallSquare_of_l2 hq hqhalf hraw
    (fractionalRawEvent_actualRawMatrix_L2_le hraw)
  have hweights := actualFractionalWeights_of_raw_and_smallSquare
    q hq hqhalf s hraw hsmall F hban
  exact hrem H q s X Y C A P M₀ F hq hqhalf hraw hXY hC hsizeXY hsizeXC hsum
    hA hAsum hAT hP hallowed hban hbudget hlarge hweights

end
end EndpointMatching.Fractional.ActualRemainder
