import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Incidence

/-!
# Exact positive fractional weights from a regularized inverse

The input is an explicitly bounded inverse of `B Bᵀ + d K`, together with
an approximate load vector.  The output contains actual weights and all
vertex equations.  The inverse is an analytic obligation; no fractional
perfect certificate is assumed.
-/

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace EndpointMatching.Fractional.RobustWeights

noncomputable section

variable {I E : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype E]

omit [Nonempty I] in
/-- Each incidence column has precisely three entries, so a vertex correction
changes each edge weight by at most three times its sup norm. -/
theorem transpose_incidence_norm_le (edge : E → Fin 3 → I)
    (z : (Fin 3 × I) → ℝ) :
    ‖(incidence edge)ᵀ *ᵥ z‖ ≤ 3 * ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro e
  rw [transpose_incidence_mulVec]
  calc
    ‖∑ r : Fin 3, z (r, edge e r)‖ ≤ ∑ r : Fin 3, ‖z (r, edge e r)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, ‖z‖ := Finset.sum_le_sum (fun r _ => norm_le_pi_norm _ _)
    _ = 3 * ‖z‖ := by simp

/-- Solve the true Gram equation on the balanced-mass subspace.  Adding `d K`
is solely a regularization; its contribution vanishes in the solved vector. -/
theorem gram_solve_of_regularized_inverse (edge : E → Fin 3 → I)
    (d : ℝ) (hd : d ≠ 0) (A : Matrix (Fin 3 × I) (Fin 3 × I) ℝ)
    (hA : (gram edge + d • roleKernelProjection) * A = 1)
    (r : (Fin 3 × I) → ℝ) (hr : roleKernelProjection *ᵥ r = 0) :
    gram edge *ᵥ (A *ᵥ r) = r := by
  have hHz : (gram edge + d • roleKernelProjection) *ᵥ (A *ᵥ r) = r := by
    rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  have hKH : roleKernelProjection * (gram edge + d • roleKernelProjection) =
      d • roleKernelProjection := by
    rw [mul_add, roleKernelProjection_mul_gram, Matrix.mul_smul,
      roleKernelProjection_idempotent, zero_add]
  have hK := congrArg (fun z => roleKernelProjection *ᵥ z) hHz
  rw [Matrix.mulVec_mulVec, hKH, Matrix.smul_mulVec, hr] at hK
  have hKz : roleKernelProjection *ᵥ (A *ᵥ r) = 0 :=
    (smul_eq_zero.mp hK).resolve_left hd
  simpa only [Matrix.add_mulVec, Matrix.smul_mulVec, hKz, smul_zero, add_zero] using hHz

/-- Construct exact weights from arbitrary approximate weights and control
the entire correction in sup norm. -/
theorem exists_exact_weights_of_inverse (edge : E → Fin 3 → I)
    (d : ℝ) (hd : d ≠ 0) (A : Matrix (Fin 3 × I) (Fin 3 × I) ℝ)
    (hA : (gram edge + d • roleKernelProjection) * A = 1) (w : E → ℝ) :
    ∃ w' : E → ℝ, (∀ v, (incidence edge *ᵥ w') v = 1) ∧
      ‖w' - w‖ ≤ 3 * ‖A‖ * ‖(fun _ => 1) - incidence edge *ᵥ w‖ := by
  let r : (Fin 3 × I) → ℝ := (fun _ => 1) - incidence edge *ᵥ w
  let z := A *ᵥ r
  let w' := w + (incidence edge)ᵀ *ᵥ z
  have hsolve : gram edge *ᵥ z = r :=
    gram_solve_of_regularized_inverse edge d hd A hA r
      (roleKernelProjection_load_deficit edge w)
  refine ⟨w', ?_, ?_⟩
  · have hload : incidence edge *ᵥ w' = (fun _ => 1) := by
      dsimp only [w']
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
      change incidence edge *ᵥ w + gram edge *ᵥ z = _
      rw [hsolve]
      exact add_sub_cancel _ _
    intro v
    exact congrFun hload v
  · have hdiff : w' - w = (incidence edge)ᵀ *ᵥ z := by
      dsimp only [w']
      abel
    rw [hdiff]
    calc
      ‖(incidence edge)ᵀ *ᵥ z‖ ≤ 3 * ‖z‖ := transpose_incidence_norm_le edge z
      _ ≤ 3 * (‖A‖ * ‖r‖) :=
        mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec A r) (by norm_num)
      _ = 3 * ‖A‖ * ‖(fun _ => 1) - incidence edge *ᵥ w‖ := by dsimp [r]; ring

/-- Pointwise bounds follow from the actual norm-controlled construction. -/
theorem exists_exact_weights_interval (edge : E → Fin 3 → I)
    (d : ℝ) (hd : d ≠ 0) (A : Matrix (Fin 3 × I) (Fin 3 × I) ℝ)
    (hA : (gram edge + d • roleKernelProjection) * A = 1)
    (w : E → ℝ) (a b δ : ℝ) (hw : ∀ e, a ≤ w e ∧ w e ≤ b)
    (herror : 3 * ‖A‖ * ‖(fun _ => 1) - incidence edge *ᵥ w‖ ≤ δ) :
    ∃ w' : E → ℝ, (∀ e, a - δ ≤ w' e ∧ w' e ≤ b + δ) ∧
      ∀ v, (∑ e, if v ∈ edgeSet edge e then w' e else 0) = 1 := by
  obtain ⟨w', hload, hnorm⟩ := exists_exact_weights_of_inverse edge d hd A hA w
  refine ⟨w', ?_, ?_⟩
  · intro e
    have he : |w' e - w e| ≤ δ := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        (norm_le_pi_norm (w' - w) e).trans (hnorm.trans herror)
    have habs := abs_le.mp he
    constructor <;> linarith [(hw e).1, (hw e).2]
  · intro v
    simpa only [incidence_load] using hload v

/-- A complete quantitative deterministic supplier from inverse and degree
estimates.  The hypotheses are strictly analytic/combinatorial data, not
weights.  Its output is in the exact convention consumed by rounding. -/
theorem exists_positive_perfect_weights (edge : E → Fin 3 → I)
    (d : ℝ) (hd : 0 < d) (A : Matrix (Fin 3 × I) (Fin 3 × I) ℝ)
    (hA : (gram edge + d • roleKernelProjection) * A = 1)
    (hnA : ‖A‖ ≤ 36 / d)
    (hdegree : ‖(fun _ => 1) - incidence edge *ᵥ (fun _ => 1 / d)‖ ≤ 1 / 216) :
    ∃ w : E → ℝ, (∀ e, 1 / (2 * d) ≤ w e ∧ w e ≤ 3 / (2 * d)) ∧
      ∀ v, (∑ e, if v ∈ edgeSet edge e then w e else 0) = 1 := by
  have herror : 3 * ‖A‖ *
      ‖(fun _ => 1) - incidence edge *ᵥ (fun _ => 1 / d)‖ ≤ 1 / (2 * d) := by
    calc
      _ ≤ 3 * (36 / d) * (1 / 216) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hnA (by norm_num)) hdegree
          (norm_nonneg _) (by positivity)
      _ = 1 / (2 * d) := by ring
  obtain ⟨w, hw, hload⟩ := exists_exact_weights_interval edge d hd.ne' A hA
    (fun _ => 1 / d) (1 / d) (1 / d) (1 / (2 * d)) (fun _ => ⟨le_rfl, le_rfl⟩) herror
  refine ⟨w, ?_, hload⟩
  intro e
  convert hw e using 2 <;> ring

end
end EndpointMatching.Fractional.RobustWeights
