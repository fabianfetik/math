import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Adapter
import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Size

/-!
# The actual physical remainder, conditional on a fractional supplier

This theorem quantifies over every later physical target, reserved balanced
zero-sum inventory, frozen matching and later ban.  The source premise is a
fractional-perfect certificate on every paid actual nonzero complement,
with the explicit degree/size inequalities needed for the paper's rate.
The raw-event-to-certificate theorem is not asserted in this file.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.ActualRemainder

open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.Rounding

noncomputable section

universe u

variable {G : Type u} [AddCommGroup G]

/-- A visible fractional-only supplier.  It requires exact unit load on
every vertex of the actual complement.  Its last three inequalities are
the finite quantitative inputs to `diffuse_role_bound_le_profile`.

No checksum or endpoint disjointness is needed by the supplier; those
conditions belong to the target and deterministic remainder assembly. -/
def QuantitativeFractionalSupply (R : Finset (Vertex G))
    (F : Finset (Finset (Vertex G))) (q : ℝ) (n : ℕ) (radius : ℝ) (Dstar : ℕ) : Prop :=
  ∀ W : Finset (Vertex G), Balanced W → (∀ v ∈ W, v.2 ≠ 0) →
    (taggedDistance R W : ℝ) ≤ radius →
    ∃ D : ℕ, Dstar ≤ D ∧ FractionalPerfect W F D ∧
      ((slice W 0).card : ℝ) ≤ 2 * q * (n : ℝ) ∧
      q * ((slice W 0).card : ℝ) ≤ 3 * (D : ℝ) ∧ D ≤ n

/-- The literal fractional-perfect interval and actual-size collar from the
manuscript's fractional supplier.  This is an explicit source proposition,
not an asserted theorem about the sampled reservoir. -/
def IntervalFractionalSupply (R : Finset (Vertex G))
    (F : Finset (Finset (Vertex G))) (q : ℝ) (n : ℕ) (radius : ℝ) : Prop :=
  ∀ W : Finset (Vertex G), Balanced W → (∀ v ∈ W, v.2 ≠ 0) →
    (taggedDistance R W : ℝ) ≤ radius →
    q * (n : ℝ) / 2 ≤ ((slice W 0).card : ℝ) ∧
      ((slice W 0).card : ℝ) ≤ 2 * q * (n : ℝ) ∧
      ∃ w : AllowedEdge W F → ℝ,
        (∀ e, 1 / (2 * (q * ((slice W 0).card : ℝ))) ≤ w e ∧
          w e ≤ 3 / (2 * (q * ((slice W 0).card : ℝ)))) ∧
        ∀ v : W, (∑ e, if v ∈ localEdge e then w e else 0) = 1

/-- All integer scale, cap and AKS-threshold conditions are proved from
the literal interval supplier and one explicit `q`-only order threshold. -/
theorem quantitativeFractionalSupply_of_interval
    {R : Finset (Vertex G)} {F : Finset (Finset (Vertex G))}
    (q : ℝ) (n : ℕ) (radius : ℝ) (Dstar : ℕ)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hstar : 3 ≤ Dstar)
    (hlarge : 6 * (Dstar : ℝ) ≤ q ^ 2 * (n : ℝ))
    (hsupply : IntervalFractionalSupply R F q n radius) :
    QuantitativeFractionalSupply R F q n radius Dstar := by
  intro W hW hnz hdist
  obtain ⟨hlower, hupper, w, hw, hperfect⟩ := hsupply W hW hnz hdist
  let m := (slice W 0).card
  obtain ⟨hD, hdegree, hDn⟩ := explicitDegree_conditions q n m Dstar hq hqhalf hstar hlower hupper hlarge
  have hd : 3 ≤ q * (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlower hq.le
    have hstar' : (3 : ℝ) ≤ Dstar := by exact_mod_cast hstar
    nlinarith
  refine ⟨explicitDegree q m, hD, ?_, hupper, hdegree, hDn⟩
  apply fractionalPerfect_of_interval (q * (m : ℝ)) (explicitDegree q m)
    (by linarith) (by omega) (by simpa only [mul_assoc] using (explicitDegree_scale q m hd).2)
      w hw hperfect

/-- The complete deterministic actual-remainder adapter.  The optional
endpoint-zero edge is chosen after `A`, `M₀` and `F`.  The final residual is
the actual complement in `signedTarget X Y C`, is disjoint from `A`, and
satisfies both the per-role and total bounds with `C₀ = sqrt 6 * Cstar`.

`hzero` is a local raw-degree request, separately discharged by
`zero_edge_from_raw_candidates` when its paid candidate margin is available.
The last `+3` is absent exactly when the actual preprocessed inventory has
no zero, through `zeroCharge`. -/
theorem physical_actual_remainder_of_fractional_uniform
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C) :
    ∃ (Dstar : ℕ) (Cstar : ℝ), 3 ≤ Dstar ∧ 0 < Cstar ∧
      ∀ (H : Type u) [AddCommGroup H] (q : ℝ) (n : ℕ) (radius : ℝ) (R : Finset (Vertex H))
        (X Y C : Finset H) (A P : Finset (Vertex H)) (M₀ : Matching P)
        (F : Finset (Finset (Vertex H))),
        0 < q → Disjoint X Y → (0 : H) ∉ C →
        X.card = Y.card → X.card = C.card →
        (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x →
        Balanced A → (∑ v ∈ A, v.2 = 0) → A ⊆ signedTarget X Y C →
        P ⊆ signedTarget X Y C \ A → (∀ E ∈ M₀.edges, E ∉ F) →
        (∀ z ∈ residual (signedTarget X Y C) A P, z.2 = 0 →
          ∃ E : Finset (Vertex H), Hyperedge E ∧
            E ⊆ residual (signedTarget X Y C) A P ∧ z ∈ E ∧ E ∉ F) →
        (taggedDistance R (signedTarget X Y C) : ℝ) + (A.card : ℝ) +
          3 * (M₀.edges.card : ℝ) + (zeroCharge (residual (signedTarget X Y C) A P) : ℝ)
            ≤ radius →
        QuantitativeFractionalSupply R F q n radius Dstar →
        ∃ M : ActualRemainderMatching (signedTarget X Y C) A P M₀ F,
          (∀ p : Fin 3, ((slice (residual (signedTarget X Y C) A M.covered) p).card : ℝ)
            ≤ Real.sqrt 6 * Cstar * remainderProfile n) ∧
          ((residual (signedTarget X Y C) A M.covered).card : ℝ) ≤
            3 * (Real.sqrt 6 * Cstar) * remainderProfile n := by
  obtain ⟨Dstar, Cstar, hstar, hCstar, hadapter⟩ :=
    actual_remainder_after_zero_step_uniform hAKS
  refine ⟨Dstar, Cstar, hstar, hCstar, ?_⟩
  intro H _ q n radius R X Y C A P M₀ F hq hXY hC hsizeXY hsizeXC hsum
    hA hAsum hAT hP hallowed hzero hbudget hfrac
  let T := signedTarget X Y C
  have hT : Balanced T := signedTarget_balanced hsizeXY hsizeXC
  have hTsum : ∑ v ∈ T, v.2 = 0 := signedTarget_zeroSum hsum
  have hPT : P ⊆ T := fun _ hv => (Finset.mem_sdiff.mp (hP hv)).1
  have hAP : Disjoint A P := Finset.disjoint_left.mpr (by
    intro v hvA hvP
    exact (Finset.mem_sdiff.mp (hP hvP)).2 hvA)
  obtain ⟨Z⟩ := zeroStep_exists hXY hC (show residual T A P ⊆ signedTarget X Y C from
    fun _ hv => (Finset.mem_sdiff.mp hv).1) hzero
  have hWb : Balanced ((residual T A P) \ Z.covered) :=
    balanced_sdiff_matching (residual_balanced hT hA M₀ hAT hPT hAP) Z.matching Z.inside
  have hpaid : (taggedDistance R ((residual T A P) \ Z.covered) : ℝ) ≤ radius := by
    calc
      _ ≤ (taggedDistance R T : ℝ) + (A.card : ℝ) + 3 * (M₀.edges.card : ℝ) +
          (zeroCharge (residual T A P) : ℝ) := by
        exact_mod_cast preprocessed_distance_le (R := R) M₀ Z
      _ ≤ radius := hbudget
  obtain ⟨D, hD, hperfect, hm, hdegree, hDn⟩ :=
    hfrac _ hWb Z.nonzero hpaid
  obtain ⟨M, htotal, hrole⟩ := hadapter H T A P M₀ F hT hTsum hA hAsum hAT hP
    hallowed Z D hD hperfect
  have hbound := diffuse_role_bound_le_profile Cstar q n
    (slice ((residual T A P) \ Z.covered) 0).card D hCstar.le hq
      (show 1 ≤ D by omega) hm hdegree hDn
  have hrole' : ∀ p : Fin 3, ((slice (residual T A M.covered) p).card : ℝ) ≤
      Real.sqrt 6 * Cstar * remainderProfile n := fun p => (hrole p).trans hbound
  refine ⟨M, hrole', ?_⟩
  have hcard := balanced_card M.balanced
  have hzero := hrole' 0
  rw [hcard]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

/-- Fixed-group specialization of the group-uniform physical adapter. -/
theorem physical_actual_remainder_of_fractional
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C) :
    ∃ (Dstar : ℕ) (Cstar : ℝ), 3 ≤ Dstar ∧ 0 < Cstar ∧
      ∀ (q : ℝ) (n : ℕ) (radius : ℝ) (R : Finset (Vertex G))
        (X Y C : Finset G) (A P : Finset (Vertex G)) (M₀ : Matching P)
        (F : Finset (Finset (Vertex G))),
        0 < q → Disjoint X Y → (0 : G) ∉ C →
        X.card = Y.card → X.card = C.card →
        (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x →
        Balanced A → (∑ v ∈ A, v.2 = 0) → A ⊆ signedTarget X Y C →
        P ⊆ signedTarget X Y C \ A → (∀ E ∈ M₀.edges, E ∉ F) →
        (∀ z ∈ residual (signedTarget X Y C) A P, z.2 = 0 →
          ∃ E : Finset (Vertex G), Hyperedge E ∧
            E ⊆ residual (signedTarget X Y C) A P ∧ z ∈ E ∧ E ∉ F) →
        (taggedDistance R (signedTarget X Y C) : ℝ) + (A.card : ℝ) +
          3 * (M₀.edges.card : ℝ) + (zeroCharge (residual (signedTarget X Y C) A P) : ℝ)
            ≤ radius →
        QuantitativeFractionalSupply R F q n radius Dstar →
        ∃ M : ActualRemainderMatching (signedTarget X Y C) A P M₀ F,
          (∀ p : Fin 3, ((slice (residual (signedTarget X Y C) A M.covered) p).card : ℝ)
            ≤ Real.sqrt 6 * Cstar * remainderProfile n) ∧
          ((residual (signedTarget X Y C) A M.covered).card : ℝ) ≤
            3 * (Real.sqrt 6 * Cstar) * remainderProfile n := by
  obtain ⟨Dstar, Cstar, hstar, hCstar, hadapter⟩ :=
    physical_actual_remainder_of_fractional_uniform hAKS
  exact ⟨Dstar, Cstar, hstar, hCstar, hadapter G⟩

end
end EndpointMatching.Fractional.ActualRemainder
