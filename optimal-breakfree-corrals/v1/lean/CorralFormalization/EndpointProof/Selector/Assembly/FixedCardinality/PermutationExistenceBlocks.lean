import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.PermutationExistence

/-!
# Fixed-set event estimates for Lemma E.T

The left estimate uses three source blocks, two fixed target blocks and four
independent matchings per block pair. The right estimate uses the actual
three-by-four-by-four permutation space and inverse matchings. These are
fixed-set estimates, preceding the union bounds in (T3) and (T4).
-/

open scoped Classical BigOperators

namespace EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence

noncomputable section

/-- The two-variable arithmetic-geometric mean estimate in polynomial form. -/
theorem two_product_le_mean_square (x y : ℝ) : x * y ≤ ((x + y) / 2) ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- The three-variable arithmetic-geometric mean estimate in polynomial form. -/
theorem three_product_le_mean_cube (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) : x * y * z ≤ ((x + y + z) / 3) ^ 3 := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (3 : ℝ)⁻¹) (w₂ := (3 : ℝ)⁻¹) (w₃ := (3 : ℝ)⁻¹)
    (by norm_num) (by norm_num) (by norm_num) hx hy hz (by norm_num)
  have hp := pow_le_pow_left₀ (by positivity) h 3
  simp only [mul_pow] at hp
  have h3 (t : ℝ) (ht : 0 ≤ t) : (t ^ ((3 : ℝ)⁻¹)) ^ 3 = t := by
    simpa only [Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow ht (by norm_num : (3 : ℕ) ≠ 0)
  rw [h3 x hx, h3 y hy, h3 z hz] at hp
  have hmean : (3 : ℝ)⁻¹ * x + (3 : ℝ)⁻¹ * y + (3 : ℝ)⁻¹ * z =
      (x + y + z) / 3 := by ring
  rw [hmean] at hp
  exact hp

/-- The fixed-`A,T` bound preceding (T3). `hT` is implied by `|T|=a-1`.
There is no lower threshold other than the block size being positive. -/
theorem left_fixed_block_event_bound (s a : ℕ) (hs : 0 < s)
    (A : Fin 3 → Finset (Fin s)) (T : Fin 2 → Finset (Fin s))
    (hA : ∑ i, (A i).card = a) (hT : ∑ j, (T j).card ≤ a) :
    uniformProbability (fun σ : Fin 3 → Fin 2 → Fin 4 → Equiv.Perm (Fin s) =>
      ∀ i j k, (A i).image (σ i j k) ⊆ T j) ≤
      ((a : ℝ) / (2 * s)) ^ (8 * a) := by
  have h := uniform_block_image_subset_le (K := Fin 4)
    (by simpa using hs : 0 < Fintype.card (Fin s)) A T
  simp only [Fintype.card_fin, hA, Fin.prod_univ_two] at h
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsum : ((T 0).card : ℝ) + (T 1).card ≤ a := by
    exact_mod_cast (by simpa only [Fin.sum_univ_two] using hT :
      (T 0).card + (T 1).card ≤ a)
  have hbase : ((T 0).card : ℝ) / s * ((T 1).card : ℝ) / s ≤
      ((a : ℝ) / (2 * s)) ^ 2 := by
    have hm := two_product_le_mean_square (((T 0).card : ℝ) / s)
      (((T 1).card : ℝ) / s)
    have hmean : (((T 0).card : ℝ) / s + ((T 1).card : ℝ) / s) / 2 ≤
        (a : ℝ) / (2 * s) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
        (mul_pos (by norm_num) hs')).mpr
      field_simp
      nlinarith
    have hm' := hm.trans (pow_le_pow_left₀ (by positivity) hmean 2)
    simpa only [mul_div_assoc] using hm'
  calc
    _ ≤ (((T 0).card : ℝ) / s * (((T 1).card : ℝ) / s)) ^ (a * 4) := h
    _ ≤ (((a : ℝ) / (2 * s)) ^ 2) ^ (a * 4) :=
      pow_le_pow_left₀ (by positivity) (by simpa only [mul_div_assoc] using hbase) _
    _ = _ := by rw [← pow_mul]; congr 1; omega

/-- The fixed-`B,A` bound preceding (T4), with the same 48-permutation
sample space as the selection graph. `hA` is implied by `|A|=b-1`. -/
theorem right_fixed_block_event_bound (s b : ℕ) (hs : 0 < s)
    (B : Fin 4 → Finset (Fin s)) (A : Fin 3 → Finset (Fin s))
    (hB : ∑ j, (B j).card = b) (hA : ∑ i, (A i).card ≤ b) :
    uniformProbability (fun σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s) =>
      ∀ i j k, (B j).image (σ i j k).symm ⊆ A i) ≤
      ((b : ℝ) / (3 * s)) ^ (12 * b) := by
  have h := uniform_inverse_block_image_subset_le (K := Fin 4)
    (by simpa using hs : 0 < Fintype.card (Fin s)) B A
  simp only [Fintype.card_fin, hB, Fin.prod_univ_three] at h
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsum : ((A 0).card : ℝ) + (A 1).card + (A 2).card ≤ b := by
    exact_mod_cast (by simpa only [Fin.sum_univ_three] using hA :
      (A 0).card + (A 1).card + (A 2).card ≤ b)
  have hbase : ((A 0).card : ℝ) / s * (((A 1).card : ℝ) / s) *
      (((A 2).card : ℝ) / s) ≤ ((b : ℝ) / (3 * s)) ^ 3 := by
    have hm := three_product_le_mean_cube (((A 0).card : ℝ) / s)
      (((A 1).card : ℝ) / s) (((A 2).card : ℝ) / s)
      (by positivity) (by positivity) (by positivity)
    have hmean : (((A 0).card : ℝ) / s + ((A 1).card : ℝ) / s +
        ((A 2).card : ℝ) / s) / 3 ≤ (b : ℝ) / (3 * s) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3)
        (mul_pos (by norm_num) hs')).mpr
      field_simp
      nlinarith
    exact hm.trans (pow_le_pow_left₀ (by positivity) hmean 3)
  calc
    _ ≤ (((A 0).card : ℝ) / s * (((A 1).card : ℝ) / s) *
        (((A 2).card : ℝ) / s)) ^ (b * 4) := h
    _ ≤ (((b : ℝ) / (3 * s)) ^ 3) ^ (b * 4) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = _ := by rw [← pow_mul]; congr 1; omega

end

end EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence
