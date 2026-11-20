import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Neumann

/-!
# The actual incidence Gram matrix and its role kernel

The vertex type is `Fin 3 × I`: the equal role sizes are part of the indexing,
and an edge specifies one actual vertex in every role.  Numerical coordinates
and the equation `y - x = c` may be supplied separately.  No edge or matching
existence assumption is built into this representation.
-/

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace EndpointMatching.Fractional.RobustWeights

noncomputable section

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E]

/-- One actual tagged vertex in each of the three roles. -/
def edgeSet (edge : E → Fin 3 → I) (e : E) : Finset (Fin 3 × I) :=
  Finset.univ.image (fun r => (r, edge e r))

omit [Fintype I] [Fintype E] in
@[simp] theorem mem_edgeSet (edge : E → Fin 3 → I) (e : E) (v : Fin 3 × I) :
    v ∈ edgeSet edge e ↔ v.2 = edge e v.1 := by
  simp only [edgeSet, Finset.mem_image, Finset.mem_univ, true_and]
  aesop

omit [Fintype I] [Fintype E] in
@[simp] theorem card_edgeSet (edge : E → Fin 3 → I) (e : E) :
    (edgeSet edge e).card = 3 := by
  rw [edgeSet, Finset.card_image_of_injective]
  · decide
  · exact fun r s h => congrArg Prod.fst h

/-- The zero-one vertex-by-edge incidence matrix. -/
def incidence (edge : E → Fin 3 → I) : Matrix (Fin 3 × I) E ℝ :=
  fun v e => if v.2 = edge e v.1 then 1 else 0

/-- The vertex-by-vertex Gram matrix.  In particular this is `B Bᵀ`, not
the edge Gram matrix `Bᵀ B`. -/
def gram (edge : E → Fin 3 → I) : Matrix (Fin 3 × I) (Fin 3 × I) ℝ :=
  incidence edge * (incidence edge)ᵀ

omit [Fintype I] in
/-- Unit-load equations in the finite-set convention used by rounding. -/
theorem incidence_load (edge : E → Fin 3 → I) (w : E → ℝ) (v : Fin 3 × I) :
    (incidence edge *ᵥ w) v = ∑ e, if v ∈ edgeSet edge e then w e else 0 := by
  simp [Matrix.mulVec, dotProduct, incidence, ite_mul]

omit [Fintype E] in
@[simp] theorem transpose_incidence_mulVec (edge : E → Fin 3 → I)
    (z : (Fin 3 × I) → ℝ) (e : E) :
    ((incidence edge)ᵀ *ᵥ z) e = ∑ r : Fin 3, z (r, edge e r) := by
  simp [Matrix.mulVec, dotProduct, incidence, Fintype.sum_prod_type, ite_mul]

/-- Total load in a role, before or after deleting arbitrary indexed edges. -/
def roleSum (z : (Fin 3 × I) → ℝ) (r : Fin 3) : ℝ := ∑ i, z (r, i)

theorem roleSum_load (edge : E → Fin 3 → I) (w : E → ℝ) (r : Fin 3) :
    roleSum (incidence edge *ᵥ w) r = ∑ e, w e := by
  simp only [roleSum, Matrix.mulVec, dotProduct, incidence]
  rw [Finset.sum_comm]
  simp

/-- The regularized equation has precisely the expected role-constant kernel. -/
theorem gram_roleConstant (edge : E → Fin 3 → I) (c : Fin 3 → ℝ)
    (hc : ∑ r, c r = 0) :
    gram edge *ᵥ (fun v => c v.1) = 0 := by
  rw [gram, ← Matrix.mulVec_mulVec]
  have hz : (incidence edge)ᵀ *ᵥ (fun v => c v.1) = 0 := by
    ext e
    simpa using hc
  rw [hz, Matrix.mulVec_zero]

section Projections

variable [Nonempty I]

omit [DecidableEq I] in
private theorem card_ne_zero : (Fintype.card I : ℝ) ≠ 0 := by
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card I ≠ 0)

/-- Orthogonal averaging separately in each role. -/
def roleProjection : Matrix (Fin 3 × I) (Fin 3 × I) ℝ :=
  fun v u => if v.1 = u.1 then 1 / (Fintype.card I : ℝ) else 0

/-- Orthogonal projection onto globally constant vectors. -/
def constantProjection : Matrix (Fin 3 × I) (Fin 3 × I) ℝ :=
  fun _ _ => 1 / (3 * (Fintype.card I : ℝ))

/-- Orthogonal projection onto role-constant vectors whose constants sum to zero. -/
def roleKernelProjection : Matrix (Fin 3 × I) (Fin 3 × I) ℝ :=
  roleProjection - constantProjection

omit [DecidableEq I] [Nonempty I] in
theorem roleProjection_apply (z : (Fin 3 × I) → ℝ) (v : Fin 3 × I) :
    (roleProjection *ᵥ z) v = roleSum z v.1 / (Fintype.card I : ℝ) := by
  simp [Matrix.mulVec, dotProduct, roleProjection, Fintype.sum_prod_type,
    roleSum, ← Finset.mul_sum, div_eq_mul_inv, mul_comm]

omit [DecidableEq I] [Nonempty I] in
theorem constantProjection_apply (z : (Fin 3 × I) → ℝ) (v : Fin 3 × I) :
    (constantProjection *ᵥ z) v =
      (∑ r, roleSum z r) / (3 * (Fintype.card I : ℝ)) := by
  simp [Matrix.mulVec, dotProduct, constantProjection, Fintype.sum_prod_type,
    roleSum, ← Finset.mul_sum, div_eq_mul_inv, mul_comm]

omit [DecidableEq I] [Nonempty I] in
theorem roleKernelProjection_apply (z : (Fin 3 × I) → ℝ) (v : Fin 3 × I) :
    (roleKernelProjection *ᵥ z) v =
      roleSum z v.1 / (Fintype.card I : ℝ) -
        (∑ r, roleSum z r) / (3 * (Fintype.card I : ℝ)) := by
  simp only [roleKernelProjection, Matrix.sub_mulVec, Pi.sub_apply,
    roleProjection_apply, constantProjection_apply]

omit [DecidableEq I] in
theorem roleSum_roleKernelProjection (z : (Fin 3 × I) → ℝ) (r : Fin 3) :
    roleSum (roleKernelProjection *ᵥ z) r = roleSum z r - (∑ s, roleSum z s) / 3 := by
  simp only [roleSum, roleKernelProjection_apply, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp [card_ne_zero (I := I)]

omit [DecidableEq I] in
theorem sum_roleSum_roleKernelProjection (z : (Fin 3 × I) → ℝ) :
    (∑ r, roleSum (roleKernelProjection *ᵥ z) r) = 0 := by
  simp only [roleSum_roleKernelProjection, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem roleKernelProjection_idempotent :
    (roleKernelProjection (I := I)) * roleKernelProjection = roleKernelProjection := by
  apply Matrix.mulVec_injective
  funext z v
  rw [← Matrix.mulVec_mulVec, roleKernelProjection_apply,
    roleSum_roleKernelProjection, sum_roleSum_roleKernelProjection,
    roleKernelProjection_apply]
  field_simp [card_ne_zero (I := I)]
  ring

omit [DecidableEq I] [Nonempty I] in
theorem roleKernelProjection_symmetric :
    (roleKernelProjection (I := I))ᵀ = roleKernelProjection := by
  ext v u
  simp only [Matrix.transpose_apply, roleKernelProjection, Matrix.sub_apply,
    roleProjection, constantProjection]
  simp [eq_comm]

omit [DecidableEq I] in
/-- Equal role masses are exactly what is needed for the load-deficit vector. -/
theorem roleKernelProjection_eq_zero_of_balanced (z : (Fin 3 × I) → ℝ)
    (hbalanced : ∀ r s, roleSum z r = roleSum z s) :
    roleKernelProjection *ᵥ z = 0 := by
  ext v
  rw [roleKernelProjection_apply]
  have hsum : (∑ r, roleSum z r) = 3 * roleSum z v.1 := by
    calc
      (∑ r, roleSum z r) = ∑ _ : Fin 3, roleSum z v.1 :=
        Finset.sum_congr rfl (fun r _ => hbalanced r v.1)
      _ = 3 * roleSum z v.1 := by simp
  rw [hsum]
  change _ = (0 : ℝ)
  field_simp
  ring

theorem roleKernelProjection_load_deficit (edge : E → Fin 3 → I) (w : E → ℝ) :
    roleKernelProjection *ᵥ ((fun _ => 1) - incidence edge *ᵥ w) = 0 := by
  apply roleKernelProjection_eq_zero_of_balanced
  intro r s
  change (∑ i, (1 - (incidence edge *ᵥ w) (r, i))) =
    ∑ i, (1 - (incidence edge *ᵥ w) (s, i))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  change _ - roleSum (incidence edge *ᵥ w) r = _ - roleSum (incidence edge *ᵥ w) s
  rw [roleSum_load, roleSum_load]

theorem gram_mul_roleKernelProjection (edge : E → Fin 3 → I) :
    gram edge * roleKernelProjection = 0 := by
  apply Matrix.mulVec_injective
  funext z
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  have hker := funext (roleKernelProjection_apply z)
  rw [hker]
  apply gram_roleConstant edge
    (fun r => roleSum z r / (Fintype.card I : ℝ) -
      (∑ s, roleSum z s) / (3 * (Fintype.card I : ℝ)))
  · simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    norm_num

omit [Fintype I] [Nonempty I] in
@[simp] theorem gram_symmetric (edge : E → Fin 3 → I) :
    (gram edge)ᵀ = gram edge := by
  simp [gram, Matrix.transpose_mul]

theorem roleKernelProjection_mul_gram (edge : E → Fin 3 → I) :
    roleKernelProjection * gram edge = 0 := by
  have h := congrArg Matrix.transpose (gram_mul_roleKernelProjection edge)
  simpa [Matrix.transpose_mul, roleKernelProjection_symmetric] using h

omit [DecidableEq I] in
/-- The projector fixes role-constant vectors with zero sum. -/
theorem roleKernelProjection_roleConstant (c : Fin 3 → ℝ) (hc : ∑ r, c r = 0) :
    roleKernelProjection (I := I) *ᵥ (fun v => c v.1) = (fun v => c v.1) := by
  ext v
  rw [roleKernelProjection_apply]
  simp only [roleSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, hc, mul_zero, zero_div, sub_zero]
  exact mul_div_cancel_left₀ _ (card_ne_zero (I := I))

omit [DecidableEq I] in
/-- The global averaging matrix really is a projection. -/
theorem constantProjection_idempotent :
    (constantProjection (I := I)) * constantProjection = constantProjection := by
  ext v u
  simp only [Matrix.mul_apply, constantProjection, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [card_ne_zero (I := I)]
  norm_num

end Projections

end
end EndpointMatching.Fractional.RobustWeights
