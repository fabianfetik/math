import Mathlib

/-!
# The exact single-matching probability in Lemma E.T

This file supplies the finite counting part of (T2). It does not assume either
expansion condition from the selection-graph construction.
-/

open scoped Classical BigOperators

namespace EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Probability of a predicate under the uniform distribution on a finite
sample space, written as a real cardinality ratio. -/
def uniformProbability {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω

/-- This cardinality ratio is the actual probability under Mathlib's
uniform probability mass function. -/
theorem uniformProbability_eq_pmf_toReal {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) :
    uniformProbability P =
      ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | P ω}).toReal := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp [uniformProbability, ENNReal.toReal_div, Fintype.card_subtype]

/-- The finite product sample space supplies independence; it is not an
additional hypothesis about the coordinate events. -/
theorem uniformProbability_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (P : (i : ι) → β i → Prop) :
    uniformProbability (fun f : (i : ι) → β i => ∀ i, P i (f i)) =
      ∏ i, uniformProbability (P i) := by
  classical
  unfold uniformProbability
  calc
    _ = ((Fintype.piFinset (fun i => Finset.univ.filter (P i))).card : ℝ) /
        Fintype.card ((i : ι) → β i) := by
      congr 2
      congr 1
      ext f
      simp
    _ = _ := by
      simp only [Fintype.card_piFinset, Fintype.card_pi, Nat.cast_prod,
        Finset.prod_div_distrib]

/-- Relabelling a finite uniform sample space by a bijection preserves
probabilities. -/
theorem uniformProbability_equiv {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    (e : Ω ≃ Ψ) (P : Ψ → Prop) :
    uniformProbability (fun ω => P (e ω)) = uniformProbability P := by
  unfold uniformProbability
  congr 1
  · congr 1
    refine Finset.card_bij (fun ω _ => e ω) ?_ ?_ ?_
    · intro ω hω
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hω
    · intro ω _ ω' _ h
      exact e.injective h
    · intro ψ hψ
      refine ⟨e.symm ψ, ?_, e.apply_symm_apply ψ⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.apply_symm_apply] using hψ
  · exact_mod_cast Fintype.card_congr e

theorem uniformProbability_congr {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop)
    (hPQ : ∀ ω, P ω ↔ Q ω) : uniformProbability P = uniformProbability Q := by
  have h : P = Q := funext (fun ω => propext (hPQ ω))
  rw [h]

theorem uniformProbability_nonneg {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    0 ≤ uniformProbability P := by
  unfold uniformProbability
  positivity

theorem uniformProbability_true {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    uniformProbability (fun _ : Ω => True) = 1 := by
  simp [uniformProbability, Fintype.card_ne_zero]

theorem uniformProbability_mono {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop)
    (hPQ : ∀ ω, P ω → Q ω) : uniformProbability P ≤ uniformProbability Q := by
  unfold uniformProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show
    Finset.univ.filter P ⊆ Finset.univ.filter Q from
      fun ω hω => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hPQ ω (Finset.mem_filter.mp hω).2⟩)

/-- The union bound on a finite uniform sample space. -/
theorem uniformProbability_exists_finset {Ω ι : Type*} [Fintype Ω]
    (S : Finset ι) (P : ι → Ω → Prop) :
    uniformProbability (fun ω => ∃ i ∈ S, P i ω) ≤
      ∑ i ∈ S, uniformProbability (P i) := by
  classical
  unfold uniformProbability
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Nat.cast_sum]
  norm_cast
  calc
    _ = (S.biUnion (fun i => Finset.univ.filter (P i))).card := by
      congr 1
      ext ω
      simp
    _ ≤ _ := Finset.card_biUnion_le

theorem uniformProbability_double_exists_le {Ω ι κ : Type*} [Fintype Ω]
    (S : Finset ι) (T : Finset κ) (P : ι → κ → Ω → Prop) (q : ℝ)
    (hP : ∀ i ∈ S, ∀ j ∈ T, uniformProbability (P i j) ≤ q) :
    uniformProbability (fun ω => ∃ i ∈ S, ∃ j ∈ T, P i j ω) ≤
      (S.card : ℝ) * T.card * q := by
  calc
    _ ≤ ∑ i ∈ S, uniformProbability (fun ω => ∃ j ∈ T, P i j ω) :=
      uniformProbability_exists_finset S _
    _ ≤ ∑ i ∈ S, ∑ _j ∈ T, q := by
      apply Finset.sum_le_sum
      intro i hi
      exact (uniformProbability_exists_finset T (P i)).trans
        (Finset.sum_le_sum (fun j hj => hP i hi j hj))
    _ = _ := by simp; ring

theorem uniformProbability_or_le {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop) :
    uniformProbability (fun ω => P ω ∨ Q ω) ≤ uniformProbability P + uniformProbability Q := by
  let E := fun (i : Fin 2) (ω : Ω) => if i = 0 then P ω else Q ω
  have hevent : uniformProbability (fun ω => P ω ∨ Q ω) =
      uniformProbability (fun ω => ∃ i ∈ (Finset.univ : Finset (Fin 2)), E i ω) := by
    apply uniformProbability_congr
    intro ω
    constructor
    · rintro (hP | hQ)
      · exact ⟨0, Finset.mem_univ _, by simpa [E] using hP⟩
      · exact ⟨1, Finset.mem_univ _, by simpa [E] using hQ⟩
    · rintro ⟨i, _, hi⟩
      fin_cases i
      · exact Or.inl (by simpa [E] using hi)
      · exact Or.inr (by simpa [E] using hi)
  rw [hevent]
  simpa only [Fin.sum_univ_two, E, if_pos rfl,
    if_neg (by decide : (1 : Fin 2) ≠ 0), ite_true] using
      uniformProbability_exists_finset (Finset.univ : Finset (Fin 2)) E

/-- A strict upper bound below one supplies an actual good outcome. -/
theorem exists_not_of_uniformProbability_lt_one {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) (hP : uniformProbability P < 1) : ∃ ω, ¬ P ω := by
  by_contra! h
  have htrue : P = fun _ => True := funext (fun ω => propext ⟨fun _ => trivial, fun _ => h ω⟩)
  rw [htrue, uniformProbability_true] at hP
  exact lt_irrefl _ hP

/-- The permutations sending precisely `S` onto `T`. -/
def imageFiber (S T : Finset α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter (fun σ => S.image σ = T)

/-- Same-sized target sets have equally many permutation preimages. -/
theorem imageFiber_card_eq (S T U : Finset α) (hTU : T.card = U.card) :
    (imageFiber S T).card = (imageFiber S U).card := by
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_map_finset_eq T U hTU
  have hπ' : T.image π = U := by
    simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using hπ
  have hπinv : U.image π.symm = T := by
    rw [← hπ', Finset.image_image]
    simp
  refine Finset.card_bij' (fun σ _ => σ.trans π) (fun σ _ => σ.trans π.symm)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    have hσ' : S.image σ = T := (Finset.mem_filter.mp hσ).2
    simp only [imageFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    change S.image (π ∘ σ) = U
    rw [← Finset.image_image, hσ', hπ']
  · intro σ hσ
    have hσ' : S.image σ = U := (Finset.mem_filter.mp hσ).2
    simp only [imageFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    change S.image (π.symm ∘ σ) = T
    rw [← Finset.image_image, hσ', hπinv]
  · intro σ _
    ext x
    exact π.symm_apply_apply (σ x)
  · intro σ _
    ext x
    exact π.apply_symm_apply (σ x)

/-- Count permutations by their image of a fixed set. -/
theorem count_image_subset (S Y : Finset α) :
    (Finset.univ.filter (fun σ : Equiv.Perm α => S.image σ ⊆ Y)).card =
      Y.card.choose S.card * (imageFiber S S).card := by
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Equiv.Perm α)) (Y.powersetCard S.card)
    (fun σ => S.image σ)
  have hfilter :
      (Finset.univ.filter (fun σ : Equiv.Perm α => S.image σ ∈ Y.powersetCard S.card)) =
        Finset.univ.filter (fun σ : Equiv.Perm α => S.image σ ⊆ Y) := by
    ext σ
    simp [Finset.card_image_of_injective S σ.injective]
  rw [hfilter] at hfiber
  rw [← hfiber]
  calc
    _ = ∑ T ∈ Y.powersetCard S.card, (imageFiber S S).card := by
      apply Finset.sum_congr rfl
      intro T hT
      exact imageFiber_card_eq S T S (Finset.mem_powersetCard.mp hT).2
    _ = _ := by simp

/-- Every permutation belongs to exactly one image fiber. -/
theorem count_all_permutations (S : Finset α) :
    Fintype.card (Equiv.Perm α) =
      (Fintype.card α).choose S.card * (imageFiber S S).card := by
  simpa using count_image_subset S Finset.univ

/-- Exact finite probability that a uniformly chosen permutation sends `S`
inside `Y`, the equality in (T2). This also covers `S.card > Y.card`. -/
theorem uniform_image_subset_exact (S Y : Finset α) :
    ((Finset.univ.filter (fun σ : Equiv.Perm α => S.image σ ⊆ Y)).card : ℝ) /
        Fintype.card (Equiv.Perm α) =
      (Y.card.choose S.card : ℝ) / (Fintype.card α).choose S.card := by
  have hc : (imageFiber S S).card ≠ 0 := by
    apply Finset.card_ne_zero.mpr
    refine ⟨Equiv.refl α, ?_⟩
    simp [imageFiber]
  rw [count_image_subset, count_all_permutations]
  push_cast
  exact mul_div_mul_right _ _ (by exact_mod_cast hc)

/-- Sampling without replacement has no larger containment probability than
independent sampling with replacement. A division-free counting form. -/
theorem descFactorial_ratio_le_pow (s y x : ℕ) (hys : y ≤ s) :
    y.descFactorial x * s ^ x ≤ s.descFactorial x * y ^ x := by
  induction x with
  | zero => simp
  | succ x ih =>
    by_cases hxy : x < y
    · have hxs : x ≤ s := by omega
      have hxy' : x ≤ y := by omega
      have hfactor : (y - x) * s ≤ (s - x) * y := by
        have hyx := Nat.sub_add_cancel hxy'
        have hsx := Nat.sub_add_cancel hxs
        nlinarith
      calc
        y.descFactorial (x + 1) * s ^ (x + 1) =
            ((y - x) * s) * (y.descFactorial x * s ^ x) := by
              rw [Nat.descFactorial_succ, pow_succ]
              ring
        _ ≤ ((s - x) * y) * (s.descFactorial x * y ^ x) :=
          Nat.mul_le_mul hfactor ih
        _ = s.descFactorial (x + 1) * y ^ (x + 1) := by
          rw [Nat.descFactorial_succ, pow_succ]
          ring
    · have h : y < x + 1 := by omega
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, zero_mul]
      exact Nat.zero_le _

/-- The binomial-coefficient inequality underlying the estimate in (T2). -/
theorem choose_ratio_le_pow_mul (s y x : ℕ) (hys : y ≤ s) :
    y.choose x * s ^ x ≤ s.choose x * y ^ x := by
  have h := descFactorial_ratio_le_pow s y x hys
  simp only [Nat.descFactorial_eq_factorial_mul_choose, mul_assoc] at h
  exact le_of_mul_le_mul_left h (Nat.factorial_pos x)

/-- The numerical inequality in (T2), including the case `x > y`. -/
theorem choose_ratio_le_pow (s y x : ℕ) (hs : 0 < s) (hys : y ≤ s)
    (hxs : x ≤ s) :
    (y.choose x : ℝ) / s.choose x ≤ ((y : ℝ) / s) ^ x := by
  have hc : (0 : ℝ) < s.choose x := by exact_mod_cast Nat.choose_pos hxs
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h := choose_ratio_le_pow_mul s y x hys
  have h' : (y.choose x : ℝ) * (s : ℝ) ^ x ≤
      (s.choose x : ℝ) * (y : ℝ) ^ x := by exact_mod_cast h
  rw [div_pow]
  apply (div_le_div_iff₀ hc (pow_pos hs' x)).mpr
  simpa only [mul_comm] using h'

/-- The estimate in (T2) for an actual uniform permutation, with no size
restriction on the source or target subset beyond membership in `α`. -/
theorem uniform_image_subset_le (hα : 0 < Fintype.card α) (S Y : Finset α) :
    ((Finset.univ.filter (fun σ : Equiv.Perm α => S.image σ ⊆ Y)).card : ℝ) /
        Fintype.card (Equiv.Perm α) ≤
      ((Y.card : ℝ) / Fintype.card α) ^ S.card := by
  rw [uniform_image_subset_exact]
  exact choose_ratio_le_pow _ _ _ hα Y.card_le_univ S.card_le_univ

/-- The containment event is impossible when the source subset is larger. -/
theorem uniform_image_subset_eq_zero (S Y : Finset α) (h : Y.card < S.card) :
    ((Finset.univ.filter (fun σ : Equiv.Perm α => S.image σ ⊆ Y)).card : ℝ) /
        Fintype.card (Equiv.Perm α) = 0 := by
  rw [uniform_image_subset_exact, Nat.choose_eq_zero_of_lt h]
  simp

theorem uniformProbability_image_subset_exact (S Y : Finset α) :
    uniformProbability (fun σ : Equiv.Perm α => S.image σ ⊆ Y) =
      (Y.card.choose S.card : ℝ) / (Fintype.card α).choose S.card := by
  unfold uniformProbability
  convert uniform_image_subset_exact S Y using 1
  congr 2
  congr 1
  ext σ
  simp

/-- Exact containment probability for all matchings in a rectangular array
of independently uniform permutations. It applies to any number of left
blocks, right blocks, and parallel matchings. -/
theorem uniform_block_image_subset_exact
    {I J K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (S : I → Finset α) (T : J → Finset α) :
    uniformProbability (fun σ : I → J → K → Equiv.Perm α =>
      ∀ i j k, (S i).image (σ i j k) ⊆ T j) =
      ∏ i, ∏ j, ((T j).card.choose (S i).card /
        ((Fintype.card α).choose (S i).card : ℝ)) ^ Fintype.card K := by
  rw [uniformProbability_pi (fun i (τ : J → K → Equiv.Perm α) =>
    ∀ j k, (S i).image (τ j k) ⊆ T j)]
  apply Finset.prod_congr rfl
  intro i _
  rw [uniformProbability_pi (fun j (τ : K → Equiv.Perm α) =>
    ∀ k, (S i).image (τ k) ⊆ T j)]
  apply Finset.prod_congr rfl
  intro j _
  rw [uniformProbability_pi (fun _k (τ : Equiv.Perm α) =>
    (S i).image τ ⊆ T j)]
  simp_rw [uniformProbability_image_subset_exact]
  simp [div_pow]

/-- The blockwise estimate obtained from (T2) and independence. No
arithmetic-geometric mean estimate or union bound is assumed here. -/
theorem uniform_block_image_subset_le
    {I J K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (hα : 0 < Fintype.card α) (S : I → Finset α) (T : J → Finset α) :
    uniformProbability (fun σ : I → J → K → Equiv.Perm α =>
      ∀ i j k, (S i).image (σ i j k) ⊆ T j) ≤
      (∏ j, ((T j).card : ℝ) / Fintype.card α) ^
        ((∑ i, (S i).card) * Fintype.card K) := by
  rw [uniform_block_image_subset_exact]
  calc
    _ ≤ ∏ i, ∏ j, ((((T j).card : ℝ) / Fintype.card α) ^ (S i).card) ^
          Fintype.card K := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        apply Finset.prod_le_prod
        · intro j _
          positivity
        · intro j _
          exact pow_le_pow_left₀ (by positivity)
            (choose_ratio_le_pow _ _ _ hα (T j).card_le_univ (S i).card_le_univ) _
    _ = _ := by
      simp_rw [← pow_mul]
      calc
        _ = ∏ i, (∏ j, ((T j).card : ℝ) / Fintype.card α) ^
              ((S i).card * Fintype.card K) := by
          apply Finset.prod_congr rfl
          intro i _
          rw [Finset.prod_pow]
        _ = _ := by
          rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_mul]

/-- The same estimate for inverse matchings, in the actual orientation of
the right-to-left neighborhood event used in (T4). -/
theorem uniform_inverse_block_image_subset_le
    {I J K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (hα : 0 < Fintype.card α) (S : J → Finset α) (T : I → Finset α) :
    uniformProbability (fun σ : I → J → K → Equiv.Perm α =>
      ∀ i j k, (S j).image (σ i j k).symm ⊆ T i) ≤
      (∏ i, ((T i).card : ℝ) / Fintype.card α) ^
        ((∑ j, (S j).card) * Fintype.card K) := by
  let e : (J → I → K → Equiv.Perm α) ≃ (I → J → K → Equiv.Perm α) :=
    { toFun := fun σ i j k => (σ j i k).symm
      invFun := fun σ j i k => (σ i j k).symm
      left_inv := by intro σ; funext j i k; exact Equiv.symm_symm _
      right_inv := by intro σ; funext i j k; exact Equiv.symm_symm _ }
  rw [← uniformProbability_equiv e]
  have hevent :
      uniformProbability (fun σ : J → I → K → Equiv.Perm α =>
        ∀ i j k, (S j).image ((e σ) i j k).symm ⊆ T i) =
      uniformProbability (fun σ : J → I → K → Equiv.Perm α =>
        ∀ j i k, (S j).image (σ j i k) ⊆ T i) := by
    apply uniformProbability_congr
    intro σ
    simp only [e, Equiv.coe_fn_mk, Equiv.symm_symm]
    exact forall_comm
  rw [hevent]
  exact uniform_block_image_subset_le hα S T

end

end EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence
