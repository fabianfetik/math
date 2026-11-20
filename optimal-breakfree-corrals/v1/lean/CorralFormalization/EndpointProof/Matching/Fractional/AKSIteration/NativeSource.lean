import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.VertexSubtype
import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.ActualRemainderFromBite

/-! A finite-vertex formulation of the explicit external one-bite theorem
suffices. All subtype translations and the deterministic iteration are
proved here; the source one-bite theorem itself remains an assumption. -/

open scoped Classical BigOperators
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.UniversalCore EndpointMatching.Fractional.RobustWeights
open EndpointMatching.Fractional.Fourier EndpointMatching.Fractional.Rounding
open EndpointMatching.Fractional.ActualRemainder AKSSourceBite AKSSubsetTransport

namespace AKSSourceIteration
noncomputable section
universe u

/-- Transport the constants and one-bite source theorem, without changing
its degree, waste, or error hypotheses. -/
theorem absolute_source_bite_from_native
    (hsource : ∃ K Dmin C Cw : ℝ, 0 < K ∧ 0 ≤ C ∧ 0 ≤ Cw ∧
      NativeBiteTheorem.{u} K Dmin C Cw) :
    ∃ K Dmin C Cw : ℝ, 0 < K ∧ 0 ≤ C ∧ 0 ≤ Cw ∧
      SourceBiteTheorem.{u} K Dmin C Cw := by
  obtain ⟨K,Dmin,C,Cw,hK,hC,hCw,hbite⟩ := hsource
  exact ⟨K,Dmin,C,Cw,hK,hC,hCw,source_bite_from_native K Dmin C Cw hbite⟩

/-- The external native one-bite formulation supplies the original
near-regular finite-set matching input. -/
theorem absolute_AKS_input_from_native_bite
    (hsource : ∃ K Dmin C Cw : ℝ, 0 < K ∧ 0 ≤ C ∧ 0 ≤ Cw ∧
      NativeBiteTheorem.{u} K Dmin C Cw) :
    ∃ K D0 Cstar : ℝ, 0 < K ∧ 0 < Cstar ∧ AKSSetFamilyTheorem.{u} K D0 Cstar := by
  exact absolute_AKS_input_from_source_bite (absolute_source_bite_from_native hsource)

/-- The complete adaptive quantitative remainder follows from the common
raw event and the source-shaped one-bite theorem on native vertex types. -/
theorem physical_actual_remainder_from_native_bite
    (hsource : ∃ K Dmin C Cw : ℝ, 0 < K ∧ 0 ≤ C ∧ 0 ≤ Cw ∧
      NativeBiteTheorem.{u} K Dmin C Cw) :
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
  exact physical_actual_remainder_from_source_bite (absolute_source_bite_from_native hsource)


end
end AKSSourceIteration
