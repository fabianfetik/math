import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Correction

/-!
# Row-sum estimates and arbitrary later edge bans

All norms on matrices in these declarations are maximum absolute row sums.
The estimates for a restricted edge family are proved from its incidence
matrix and its actual rooted degrees.
-/

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace EndpointMatching.Fractional.RobustWeights

noncomputable section

section MatrixBounds

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Entrywise absolute row sums control precisely the norm being used. -/
theorem matrix_norm_le_of_row_sum_le (A : Matrix V W ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ v, ∑ w, |A v w| ≤ C) : ‖A‖ ≤ C := by
  have hnn : ‖A‖₊ ≤ Real.toNNReal C := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro v _
    change (∑ w : W, ‖A v w‖₊) ≤ Real.toNNReal C
    exact NNReal.coe_le_coe.mp (by
      simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs,
        Real.coe_toNNReal _ hC] using hrow v)
  have hreal := NNReal.coe_le_coe.mpr hnn
  simpa only [coe_nnnorm, Real.coe_toNNReal _ hC] using hreal

/-- Conversely, every absolute row sum is below the matrix norm. -/
theorem row_sum_le_matrix_norm (A : Matrix V W ℝ) (v : V) :
    ∑ w, |A v w| ≤ ‖A‖ := by
  have hnn : (∑ w, ‖A v w‖₊) ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun v => ∑ w, ‖A v w‖₊) (Finset.mem_univ v)
  simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using
    (NNReal.coe_le_coe.mpr hnn)

end MatrixBounds

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

/-- Rooted degree in a specified actual edge family. -/
def familyDegree (edge : E → Fin 3 → I) (S : Finset E) (v : Fin 3 × I) : ℕ :=
  (S.filter (fun e => v.2 = edge e v.1)).card

/-- The Gram matrix of a specified edge family, on the full actual vertex type. -/
def familyGram (edge : E → Fin 3 → I) (S : Finset E) :
    Matrix (Fin 3 × I) (Fin 3 × I) ℝ :=
  fun v u => ∑ e ∈ S, incidence edge v e * incidence edge u e

omit [Fintype I] [Fintype E] [DecidableEq E] in
theorem familyGram_eq_gram_subtype (edge : E → Fin 3 → I) (S : Finset E) :
    familyGram edge S = gram (fun e : S => edge e) := by
  ext v u
  simp only [familyGram, gram, Matrix.mul_apply, Matrix.transpose_apply, incidence]
  exact Finset.sum_subtype S (by simp) (fun e =>
    (if v.2 = edge e v.1 then (1 : ℝ) else 0) * (if u.2 = edge e u.1 then 1 else 0))

omit [Fintype I] [DecidableEq E] in
@[simp] theorem familyGram_univ (edge : E → Fin 3 → I) :
    familyGram edge Finset.univ = gram edge := by
  ext v u
  simp [familyGram, gram, Matrix.mul_apply, Matrix.transpose_apply]

/-- Deleting a ban subtracts its vertex Gram matrix exactly. -/
theorem familyGram_compl (edge : E → Fin 3 → I) (F : Finset E) :
    familyGram edge (Finset.univ \ F) = gram edge - familyGram edge F := by
  ext v u
  have hsum := Finset.sum_sdiff (f := fun e => incidence edge v e * incidence edge u e)
    (Finset.subset_univ F)
  simpa only [familyGram, Matrix.sub_apply, ← familyGram_univ] using (eq_sub_iff_add_eq.mpr hsum)

omit [Fintype I] [Fintype E] [DecidableEq E] in
theorem incidence_nonneg (edge : E → Fin 3 → I) (v : Fin 3 × I) (e : E) :
    0 ≤ incidence edge v e := by unfold incidence; split_ifs <;> norm_num

theorem familyGram_nonneg (edge : E → Fin 3 → I) (S : Finset E)
    (v u : Fin 3 × I) : 0 ≤ familyGram edge S v u := by
  exact Finset.sum_nonneg (fun e _ =>
    mul_nonneg (incidence_nonneg edge v e) (incidence_nonneg edge u e))

omit [Fintype E] [DecidableEq E] in
theorem sum_incidence (edge : E → Fin 3 → I) (e : E) :
    (∑ v, incidence edge v e) = 3 := by
  rw [Fintype.sum_prod_type]
  simp [incidence]

omit [Fintype I] [Fintype E] [DecidableEq E] in
theorem sum_family_incidence (edge : E → Fin 3 → I) (S : Finset E) (v : Fin 3 × I) :
    (∑ e ∈ S, incidence edge v e) = (familyDegree edge S v : ℝ) := by
  simp only [incidence, familyDegree, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Passing to the actual edge subtype preserves its rooted degrees. -/
theorem familyDegree_subtype (edge : E → Fin 3 → I) (S : Finset E) (v : Fin 3 × I) :
    familyDegree (fun e : S => edge e) Finset.univ v = familyDegree edge S v := by
  apply Nat.cast_inj (R := ℝ) |>.mp
  rw [← sum_family_incidence, ← sum_family_incidence]
  simpa only [incidence] using (Finset.sum_subtype S (by simp)
    (fun e => incidence edge v e)).symm

/-- Rooted degree loss is exactly the number of banned edges at the root. -/
theorem familyDegree_compl (edge : E → Fin 3 → I) (F : Finset E) (v : Fin 3 × I) :
    (familyDegree edge (Finset.univ \ F) v : ℝ) =
      (familyDegree edge Finset.univ v : ℝ) - (familyDegree edge F v : ℝ) := by
  rw [← sum_family_incidence, ← sum_family_incidence, ← sum_family_incidence]
  exact eq_sub_iff_add_eq.mpr (Finset.sum_sdiff (Finset.subset_univ F))

theorem sum_familyGram_row (edge : E → Fin 3 → I) (S : Finset E) (v : Fin 3 × I) :
    (∑ u, familyGram edge S v u) = 3 * (familyDegree edge S v : ℝ) := by
  simp only [familyGram]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_incidence]
  rw [← Finset.sum_mul, sum_family_incidence]
  ring

/-- The factor three in the ban norm is a proved incidence count. -/
theorem familyGram_norm_le (edge : E → Fin 3 → I) (S : Finset E)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hdeg : ∀ v, familyDegree edge S v ≤ Δ) :
    ‖familyGram edge S‖ ≤ 3 * Δ := by
  apply matrix_norm_le_of_row_sum_le _ _ (by positivity)
  intro v
  simp only [abs_of_nonneg (familyGram_nonneg edge S v _)]
  rw [sum_familyGram_row]
  exact mul_le_mul_of_nonneg_left (hdeg v) (by norm_num)

/-- Uniform initial weights have the normalized actual degree as their load. -/
theorem uniform_load (edge : E → Fin 3 → I) (d : ℝ) (v : Fin 3 × I) :
    (incidence edge *ᵥ (fun _ => 1 / d)) v =
      (familyDegree edge Finset.univ v : ℝ) / d := by
  change (∑ e, incidence edge v e * (1 / d)) = _
  rw [← Finset.sum_mul]
  have hsum := sum_family_incidence edge Finset.univ v
  rw [hsum]
  ring

/-- An absolute degree bound supplies the normalized load-defect bound. -/
theorem uniform_deficit_norm_le (edge : E → Fin 3 → I) (d η : ℝ)
    (hd : 0 < d) (hη : 0 ≤ η)
    (hdeg : ∀ v, |(familyDegree edge Finset.univ v : ℝ) - d| ≤ η * d) :
    ‖(fun _ => 1) - incidence edge *ᵥ (fun _ => 1 / d)‖ ≤ η := by
  apply (pi_norm_le_iff_of_nonneg hη).mpr
  intro v
  simp only [Pi.sub_apply, Real.norm_eq_abs, uniform_load]
  have hrewrite : 1 - (familyDegree edge Finset.univ v : ℝ) / d =
      -((familyDegree edge Finset.univ v : ℝ) - d) / d := by field_simp; ring
  rw [hrewrite, abs_div, abs_neg, abs_of_pos hd]
  exact (div_le_iff₀ hd).mpr (hdeg v)

end
end EndpointMatching.Fractional.RobustWeights
