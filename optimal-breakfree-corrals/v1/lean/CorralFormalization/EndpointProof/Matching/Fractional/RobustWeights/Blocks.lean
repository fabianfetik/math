import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.RawEstimates
import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Adaptive

/-!
# Constructive raw and edit blocks

Coordinates here are the signed numerical coordinates, so a third coordinate
is always `-(a+b)`.  The role tags remain distinct even if coordinates agree.
The edit-matrix bound is proved by injectivity of each completion map; it
does not assume spectral accuracy of the later target.
-/

open scoped Classical BigOperators Matrix Matrix.Norms.Operator symmDiff

namespace EndpointMatching.Fractional.RobustWeights

open EndpointFractionalRawEvent
noncomputable section

/-- The remaining role when two different roles have been specified.
The value on equal roles is immaterial because diagonal blocks are zero. -/
def thirdRole : Fin 3 → Fin 3 → Fin 3 :=
  ![![0, 2, 1], ![2, 1, 0], ![1, 0, 2]]

variable {G I E : Type*} [AddCommGroup G] [Fintype G] [Fintype I]
  [DecidableEq I] [Fintype E]

/-- Signed coordinate required at the third role. -/
def requiredCoordinate (coord : (Fin 3 × I) → G) (v u : Fin 3 × I) : G :=
  -(coord v + coord u)

/-- The raw third-role indicator restricted to the actual target rows and
columns, minus its density.  Its diagonal role blocks are exactly zero. -/
def offDiagonal (coord : (Fin 3 × I) → G) (R : Fin 3 → Finset G) (q : ℝ) :
    Matrix (Fin 3 × I) (Fin 3 × I) ℝ :=
  fun v u => if v.1 = u.1 then 0 else
    setBit (R (thirdRole v.1 u.1)) (requiredCoordinate coord v u) - q

/-- The later membership edits only; the raw density term cancels. -/
def editMatrix (coord : (Fin 3 × I) → G) (T R : Fin 3 → Finset G) :
    Matrix (Fin 3 × I) (Fin 3 × I) ℝ := offDiagonal coord T 0 - offDiagonal coord R 0

theorem editMatrix_apply (coord : (Fin 3 × I) → G) (T R : Fin 3 → Finset G)
    (v u : Fin 3 × I) :
    editMatrix coord T R v u = if v.1 = u.1 then 0 else
      setBit (T (thirdRole v.1 u.1)) (requiredCoordinate coord v u) -
        setBit (R (thirdRole v.1 u.1)) (requiredCoordinate coord v u) := by
  by_cases h : v.1 = u.1 <;> simp [editMatrix, offDiagonal, h]

theorem offDiagonal_target_eq_raw_add_edits (coord : (Fin 3 × I) → G)
    (T R : Fin 3 → Finset G) (q : ℝ) :
    offDiagonal coord T q = editMatrix coord T R + offDiagonal coord R q := by
  ext v u
  by_cases h : v.1 = u.1 <;> simp [editMatrix, offDiagonal, h]

private theorem bit_abs_sub (T R : Finset G) (g : G) :
    |setBit T g - setBit R g| = setBit (T ∆ R) g := by
  by_cases hT : g ∈ T <;> by_cases hR : g ∈ R <;>
    norm_num [setBit, Finset.mem_symmDiff, hT, hR]

private theorem bit_nonneg (T : Finset G) (g : G) : 0 ≤ setBit T g := by
  unfold setBit
  split_ifs <;> norm_num

/-- Restricting an injective partner-coordinate map cannot increase the
number of changed third-role entries. -/
theorem completion_edit_row_le (T R : Finset G) (f : I → G) (hf : Function.Injective f) :
    (∑ i, |setBit T (f i) - setBit R (f i)|) ≤ ((T ∆ R).card : ℝ) := by
  simp_rw [bit_abs_sub]
  calc
    (∑ i, setBit (T ∆ R) (f i)) = ∑ g ∈ Finset.univ.image f, setBit (T ∆ R) g :=
      (Finset.sum_image (fun i _ j _ hij => hf hij)).symm
    _ ≤ ∑ g, setBit (T ∆ R) g :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun g _ _ => bit_nonneg _ g)
    _ = ((T ∆ R).card : ℝ) := by simp [setBit]

theorem requiredCoordinate_injective (coord : (Fin 3 × I) → G)
    (hcoord : ∀ r, Function.Injective (fun i => coord (r, i)))
    (v : Fin 3 × I) (s : Fin 3) :
    Function.Injective (fun i => requiredCoordinate coord v (s, i)) := by
  intro i j hij
  apply hcoord s
  exact add_left_cancel (neg_injective hij)

/-- The total local edit bound, including all later target changes.
It holds for every actual row and every signed raw/target set system. -/
theorem editMatrix_row_sum_le (coord : (Fin 3 × I) → G)
    (hcoord : ∀ r, Function.Injective (fun i => coord (r, i)))
    (T R : Fin 3 → Finset G) (v : Fin 3 × I) :
    (∑ u, |editMatrix coord T R v u|) ≤ editDistance T R := by
  rw [Fintype.sum_prod_type]
  have hblock (s : Fin 3) : (∑ i, |editMatrix coord T R v (s, i)|) ≤
      if v.1 = s then 0 else (((T (thirdRole v.1 s)) ∆ (R (thirdRole v.1 s))).card : ℝ) := by
    by_cases h : v.1 = s
    · simp [editMatrix_apply, h]
    · simp only [editMatrix_apply, h, if_false]
      exact completion_edit_row_le _ _ _ (requiredCoordinate_injective coord hcoord v s)
  apply (Finset.sum_le_sum (fun s _ => hblock s)).trans
  rcases v with ⟨r, i⟩
  fin_cases r <;> simp [thirdRole, editDistance, Fin.sum_univ_succ] <;>
    linarith [Nat.cast_nonneg (α := ℝ) (T 0 ∆ R 0).card,
      Nat.cast_nonneg (α := ℝ) (T 1 ∆ R 1).card,
      Nat.cast_nonneg (α := ℝ) (T 2 ∆ R 2).card]

theorem editMatrix_norm_le (coord : (Fin 3 × I) → G)
    (hcoord : ∀ r, Function.Injective (fun i => coord (r, i)))
    (T R : Fin 3 → Finset G) :
    ‖editMatrix coord T R‖ ≤ editDistance T R := by
  apply matrix_norm_le_of_row_sum_le _ _
    (Finset.sum_nonneg (fun r _ => Nat.cast_nonneg _))
  exact editMatrix_row_sum_le coord hcoord T R

/-- The actual degree deviation, with the correct vertex Gram indexing. -/
def degreeDiagonal (edge : E → Fin 3 → I) (d : ℝ) :
    Matrix (Fin 3 × I) (Fin 3 × I) ℝ :=
  Matrix.diagonal (fun v => (familyDegree edge Finset.univ v : ℝ) - d)

theorem degreeDiagonal_norm_le (edge : E → Fin 3 → I) (d C : ℝ) (hC : 0 ≤ C)
    (hdegree : ∀ v, |(familyDegree edge Finset.univ v : ℝ) - d| ≤ C) :
    ‖degreeDiagonal edge d‖ ≤ C := by
  rw [degreeDiagonal, Matrix.linfty_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).mpr (fun v => by simpa using hdegree v)

theorem gram_diagonal (edge : E → Fin 3 → I) (v : Fin 3 × I) :
    gram edge v v = (familyDegree edge Finset.univ v : ℝ) := by
  rw [← sum_family_incidence]
  unfold gram
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incidence]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> norm_num

theorem gram_same_role_off_diagonal (edge : E → Fin 3 → I)
    (v u : Fin 3 × I) (hrole : v.1 = u.1) (hvu : v ≠ u) :
    gram edge v u = 0 := by
  have hcoord : v.2 ≠ u.2 := fun h => hvu (Prod.ext hrole h)
  unfold gram
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incidence]
  apply Finset.sum_eq_zero
  intro e _
  by_cases hv : v.2 = edge e v.1
  · have hu : u.2 ≠ edge e u.1 := by intro hu; exact hcoord (hv.trans (hrole ▸ hu).symm)
    simp [hu]
  · simp [hv]

section Decomposition

variable [Nonempty I]

/-- The diagonal and edit matrices are constructed explicitly.  The only
structural input is the cross-role codegree formula for the actual edge
family; no matrix norm, inverse or fractional weights occur in that input. -/
theorem gram_eq_ideal_add_degree_edit_raw
    (edge : E → Fin 3 → I) (coord : (Fin 3 × I) → G)
    (T R : Fin 3 → Finset G) (q : ℝ)
    (hcross : ∀ v u, v.1 ≠ u.1 → gram edge v u =
      setBit (T (thirdRole v.1 u.1)) (requiredCoordinate coord v u)) :
    gram edge = idealGram (q * (Fintype.card I : ℝ)) +
      (degreeDiagonal edge (q * (Fintype.card I : ℝ)) + editMatrix coord T R) +
        offDiagonal coord R q := by
  have hm : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext v u
  simp only [Matrix.add_apply]
  rw [idealGram_apply]
  by_cases hrole : v.1 = u.1
  · by_cases hvu : v = u
    · subst u
      simp [degreeDiagonal, offDiagonal, editMatrix, gram_diagonal]
    · rw [gram_same_role_off_diagonal edge v u hrole hvu]
      simp [degreeDiagonal, offDiagonal, editMatrix, hrole, hvu, Matrix.diagonal_apply_ne _ hvu]
  · have hvu : v ≠ u := fun h => hrole (congrArg Prod.fst h)
    rw [hcross v u hrole]
    have hq : q * (Fintype.card I : ℝ) / (Fintype.card I : ℝ) = q := mul_div_cancel_right₀ _ hm
    simp [degreeDiagonal, offDiagonal, editMatrix, hrole, hvu, hq,
      Matrix.diagonal_apply_ne _ hvu]
    ring

end Decomposition

end
end EndpointMatching.Fractional.RobustWeights
