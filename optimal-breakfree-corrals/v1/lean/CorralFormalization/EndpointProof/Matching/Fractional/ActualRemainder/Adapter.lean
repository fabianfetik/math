import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Canonical
import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Budget
import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.RootedCounting

/-!
# A conditional deterministic actual-remainder theorem

The matching is constructed from a fractional-perfect certificate through
the proved rounding/AKS bridge.  The reserved inventory and frozen matching
are fixed first; the zero step and the fractional certificate concern their
actual complement.  Every output condition concerns the actual set
`T \ (A ∪ covered)`.  No finished near matching is a supplier premise.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.ActualRemainder

open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.Rounding

noncomputable section

universe u

variable {G : Type u} [AddCommGroup G]

/-- Actual near-matching output, including the frozen edge family and the
later ban.  All remainder invariants are conclusions. -/
structure ActualRemainderMatching (T A P : Finset (Vertex G)) (M₀ : Matching P)
    (F : Finset (Finset (Vertex G))) where
  covered : Finset (Vertex G)
  matching : Matching covered
  inside : covered ⊆ T \ A
  contains : M₀.edges ⊆ matching.edges
  allowed : ∀ E ∈ matching.edges, E ∉ F
  nonzero : ∀ v ∈ residual T A covered, v.2 ≠ 0
  balanced : Balanced (residual T A covered)
  checksum : ∑ v ∈ residual T A covered, v.2 = 0
  disjoint : Disjoint A (residual T A covered)

/-- Convert only after the actual proved remainder bound fits the selected
integer core capacity. -/
def ActualRemainderMatching.toCompatibleNearMatching
    {T A P : Finset (Vertex G)} {M₀ : Matching P}
    {F : Finset (Finset (Vertex G))} (M : ActualRemainderMatching T A P M₀ F)
    (capacity : ℕ) (hcapacity : (residual T A M.covered).card ≤ capacity) :
    CompatibleNearMatching T A capacity :=
  ⟨M.covered, M.matching, M.inside, M.nonzero, hcapacity⟩

/-- Deterministic assembly after one explicit zero step.  The same absolute
AKS constants and threshold serve every later target, core, frozen matching,
zero step, ban and fractional-perfect certificate. -/
theorem actual_remainder_after_zero_step_uniform
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C) :
    ∃ (Dstar : ℕ) (Cstar : ℝ), 3 ≤ Dstar ∧ 0 < Cstar ∧
      ∀ (H : Type u) [AddCommGroup H]
        (T A P : Finset (Vertex H)) (M₀ : Matching P)
        (F : Finset (Finset (Vertex H))),
        Balanced T → (∑ v ∈ T, v.2 = 0) → Balanced A →
        (∑ v ∈ A, v.2 = 0) → A ⊆ T → P ⊆ T \ A →
        (∀ E ∈ M₀.edges, E ∉ F) →
        ∀ (Z : ZeroStep (residual T A P) F) (D : ℕ), Dstar ≤ D →
          FractionalPerfect ((residual T A P) \ Z.covered) F D →
          ∃ M : ActualRemainderMatching T A P M₀ F,
            ((residual T A M.covered).card : ℝ) ≤
              Cstar * (((residual T A P) \ Z.covered).card : ℝ) * diffuseRate D ∧
            ∀ p : Fin 3, ((slice (residual T A M.covered) p).card : ℝ) ≤
              Cstar * ((slice ((residual T A P) \ Z.covered) 0).card : ℝ) * diffuseRate D := by
  obtain ⟨Dstar, Cstar, hstar, hCstar, hmatching⟩ := actual_matching_from_fractional_uniform hAKS
  refine ⟨Dstar, Cstar, hstar, hCstar, ?_⟩
  intro H _ T A P M₀ F hT hsum hA hAsum hAT hP hallowed Z D hD hfrac
  have hPT : P ⊆ T := fun _ hv => (Finset.mem_sdiff.mp (hP hv)).1
  have hAP : Disjoint A P := Finset.disjoint_left.mpr (by
    intro v hvA hvP
    exact (Finset.mem_sdiff.mp (hP hvP)).2 hvA)
  have hPZ : Disjoint P Z.covered := Finset.disjoint_left.mpr (by
    intro v hvP hvZ
    exact (Finset.mem_sdiff.mp (Z.inside hvZ)).2 (Finset.mem_union_right _ hvP))
  let MPZ := unionMatching M₀ Z.matching hPZ
  have hPZT : P ∪ Z.covered ⊆ T := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hPT hv
    · exact (Finset.mem_sdiff.mp (Z.inside hv)).1
  have hAPZ : Disjoint A (P ∪ Z.covered) := Finset.disjoint_left.mpr (by
    intro v hvA hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.disjoint_left.mp hAP hvA hv
    · exact (Finset.mem_sdiff.mp (Z.inside hv)).2 (Finset.mem_union_left _ hvA))
  have hW : residual T A (P ∪ Z.covered) = (residual T A P) \ Z.covered := by
    ext v
    simp only [AbsorptionAssembly.residual, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hWb : Balanced ((residual T A P) \ Z.covered) := by
    rw [← hW]
    exact residual_balanced hT hA MPZ hAT hPZT hAPZ
  obtain ⟨Q, MQ, hQ, hQallowed, hrest⟩ := hmatching H _ F D hD hfrac
  have hQW : Q ⊆ residual T A (P ∪ Z.covered) := by simpa only [hW] using hQ
  have hPQ : Disjoint (P ∪ Z.covered) Q := Finset.disjoint_left.mpr (by
    intro v hvP hvQ
    exact (Finset.mem_sdiff.mp (hQW hvQ)).2 (Finset.mem_union_right _ hvP))
  let MM := unionMatching MPZ MQ hPQ
  have hfinal : (P ∪ Z.covered) ∪ Q ⊆ T \ A := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · refine Finset.mem_sdiff.mpr ⟨hPZT hv, ?_⟩
      intro hvA
      exact Finset.disjoint_left.mp hAPZ hvA hv
    · refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (hQW hv)).1, ?_⟩
      intro hvA
      exact (Finset.mem_sdiff.mp (hQW hv)).2 (Finset.mem_union_left _ hvA)
  have hfinalT : (P ∪ Z.covered) ∪ Q ⊆ T := fun _ hv => (Finset.mem_sdiff.mp (hfinal hv)).1
  have hAfinal : Disjoint A ((P ∪ Z.covered) ∪ Q) := Finset.disjoint_left.mpr (by
    intro v hvA hv
    exact (Finset.mem_sdiff.mp (hfinal hv)).2 hvA)
  have hS : residual T A ((P ∪ Z.covered) ∪ Q) =
      ((residual T A P) \ Z.covered) \ Q := by
    ext v
    simp only [AbsorptionAssembly.residual, Finset.mem_sdiff, Finset.mem_union]
    tauto
  let result : ActualRemainderMatching T A P M₀ F := {
    covered := (P ∪ Z.covered) ∪ Q
    matching := MM
    inside := hfinal
    contains := by
      intro E hE
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hE)
    allowed := by
      intro E hE
      rcases Finset.mem_union.mp hE with hE | hE
      · rcases Finset.mem_union.mp hE with hE | hE
        · exact hallowed E hE
        · exact Z.allowed E hE
      · exact hQallowed E hE
    nonzero := by
      intro v hv
      rw [hS] at hv
      exact Z.nonzero v (Finset.mem_sdiff.mp hv).1
    balanced := residual_balanced hT hA MM hAT hfinalT hAfinal
    checksum := residual_sum_eq_zero hsum hAsum MM hAT hfinalT hAfinal
    disjoint := (residual_disjoint_reserved T A _).symm.mono
      Finset.subset_union_left (Finset.Subset.refl _) }
  have hsize : ((residual T A result.covered).card : ℝ) ≤
      Cstar * (((residual T A P) \ Z.covered).card : ℝ) * diffuseRate D := by
    simpa only [result, hS] using hrest
  refine ⟨result, hsize, ?_⟩
  intro p
  have hS3 := balanced_card result.balanced
  have hW3 := balanced_card hWb
  have hp := result.balanced p
  rw [hS3, hW3] at hsize
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hsize
  rw [hp]
  nlinarith

/-- Fixed-group specialization, retaining the existing local interface. -/
theorem actual_remainder_after_zero_step
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C) :
    ∃ (Dstar : ℕ) (Cstar : ℝ), 3 ≤ Dstar ∧ 0 < Cstar ∧
      ∀ (T A P : Finset (Vertex G)) (M₀ : Matching P)
        (F : Finset (Finset (Vertex G))),
        Balanced T → (∑ v ∈ T, v.2 = 0) → Balanced A →
        (∑ v ∈ A, v.2 = 0) → A ⊆ T → P ⊆ T \ A →
        (∀ E ∈ M₀.edges, E ∉ F) →
        ∀ (Z : ZeroStep (residual T A P) F) (D : ℕ), Dstar ≤ D →
          FractionalPerfect ((residual T A P) \ Z.covered) F D →
          ∃ M : ActualRemainderMatching T A P M₀ F,
            ((residual T A M.covered).card : ℝ) ≤
              Cstar * (((residual T A P) \ Z.covered).card : ℝ) * diffuseRate D ∧
            ∀ p : Fin 3, ((slice (residual T A M.covered) p).card : ℝ) ≤
              Cstar * ((slice ((residual T A P) \ Z.covered) 0).card : ℝ) * diffuseRate D := by
  obtain ⟨Dstar, Cstar, hstar, hCstar, hadapter⟩ := actual_remainder_after_zero_step_uniform hAKS
  exact ⟨Dstar, Cstar, hstar, hCstar, hadapter G⟩

end
end EndpointMatching.Fractional.ActualRemainder
