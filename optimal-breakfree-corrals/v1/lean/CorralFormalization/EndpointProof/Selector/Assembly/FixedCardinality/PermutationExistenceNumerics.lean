import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.PermutationExistence

/-!
# Numerical bounds for the permutation-graph union bound

We use `exp 1 < 3`, a deliberately weaker numerical estimate than the one
in (T5). The resulting uniform failure bound is `81/101 < 1`, which is
enough for exactly the same block parameters and every positive block size.
-/

open scoped Classical BigOperators

namespace EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence

noncomputable section

/-- An elementary exponential upper bound for binomial coefficients. -/
theorem choose_le_three_mul_div_pow (N k : ℕ) (hk : 0 < k) :
    (N.choose k : ℝ) ≤ (3 * N / k : ℝ) ^ k := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpow : (k : ℝ) ^ k / k.factorial ≤ (3 : ℝ) ^ k := by
    calc
      _ ≤ Real.exp k := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
      _ = Real.exp 1 ^ k := (Real.exp_one_pow k).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) Real.exp_one_lt_three.le k
  calc
    _ ≤ (N : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k N
    _ = ((N : ℝ) / k) ^ k * ((k : ℝ) ^ k / k.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ ((N : ℝ) / k) ^ k * (3 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

theorem left_binomial_geometric_bound (s a : ℕ) (ha : 1 ≤ a) (has : a ≤ s) :
    ((3 * s).choose a : ℝ) * (2 * s).choose (a - 1) *
        ((a : ℝ) / (2 * s)) ^ (8 * a) ≤ (27 / 128 : ℝ) ^ a := by
  have hs : 0 < s := by omega
  have ha' : 0 < a := by omega
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha'.ne'
  have hmono : (2 * s).choose (a - 1) ≤ (2 * s).choose a := by
    have h := Nat.choose_le_succ_of_lt_half_left (n := 2 * s) (r := a - 1)
      (by omega)
    simpa only [Nat.sub_add_cancel ha] using h
  have hleft := choose_le_three_mul_div_pow (3 * s) a ha'
  push_cast at hleft
  have hright : ((2 * s).choose (a - 1) : ℝ) ≤
      (3 * (2 * s) / a : ℝ) ^ a := by
    calc
      _ ≤ ((2 * s).choose a : ℝ) := by exact_mod_cast hmono
      _ ≤ _ := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          choose_le_three_mul_div_pow (2 * s) a ha'
  have hbase : (3 * (3 * s) / a : ℝ) * (3 * (2 * s) / a : ℝ) *
      ((a : ℝ) / (2 * s)) ^ 8 = (27 / 128 : ℝ) * ((a : ℝ) / s) ^ 6 := by
    field_simp
    ring
  have hratio : (a : ℝ) / s ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hs : (0 : ℝ) < s)).mpr
    exact_mod_cast has
  have hbasele : (27 / 128 : ℝ) * ((a : ℝ) / s) ^ 6 ≤ 27 / 128 := by
    have hpower : ((a : ℝ) / s) ^ 6 ≤ 1 :=
      pow_le_one₀ (by positivity : (0 : ℝ) ≤ (a : ℝ) / s) hratio
    nlinarith
  calc
    _ ≤ (3 * (3 * s) / a : ℝ) ^ a * (3 * (2 * s) / a : ℝ) ^ a *
        ((a : ℝ) / (2 * s)) ^ (8 * a) := by
      gcongr
    _ = ((3 * (3 * s) / a : ℝ) * (3 * (2 * s) / a : ℝ) *
        ((a : ℝ) / (2 * s)) ^ 8) ^ a := by
      rw [mul_pow, mul_pow, ← pow_mul]
    _ = ((27 / 128 : ℝ) * ((a : ℝ) / s) ^ 6) ^ a := by rw [hbase]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hbasele a

theorem right_predecessor_choose_le (s b : ℕ) (hb : 1 ≤ b) (hbs : b ≤ 2 * s) :
    (3 * s).choose (b - 1) ≤ 2 * (3 * s).choose b := by
  have hsucc : b - 1 + 1 = b := by omega
  have hrec := Nat.choose_succ_right_eq (3 * s) (b - 1)
  rw [hsucc] at hrec
  have hden : 0 < 3 * s - (b - 1) := by omega
  have hratio : b ≤ 2 * (3 * s - (b - 1)) := by omega
  have hmul := Nat.mul_le_mul_left ((3 * s).choose b) hratio
  nlinarith

theorem right_binomial_geometric_bound (s b : ℕ) (hb : 1 ≤ b) (hbs : b ≤ 2 * s) :
    ((4 * s).choose b : ℝ) * (3 * s).choose (b - 1) *
        ((b : ℝ) / (3 * s)) ^ (12 * b) ≤ 2 * (27 / 128 : ℝ) ^ b := by
  have hs : 0 < s := by omega
  have hb' : 0 < b := by omega
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb'.ne'
  have hleft := choose_le_three_mul_div_pow (4 * s) b hb'
  push_cast at hleft
  have hright : ((3 * s).choose (b - 1) : ℝ) ≤
      2 * (3 * (3 * s) / b : ℝ) ^ b := by
    calc
      _ ≤ 2 * ((3 * s).choose b : ℝ) := by
        exact_mod_cast right_predecessor_choose_le s b hb hbs
      _ ≤ _ := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          mul_le_mul_of_nonneg_left (choose_le_three_mul_div_pow (3 * s) b hb')
            (by norm_num : (0 : ℝ) ≤ 2)
  have hbase : (3 * (4 * s) / b : ℝ) * (3 * (3 * s) / b : ℝ) *
      ((b : ℝ) / (3 * s)) ^ 12 = (4 / 19683 : ℝ) * ((b : ℝ) / s) ^ 10 := by
    field_simp
    ring
  have hratio : (b : ℝ) / s ≤ 2 := by
    apply (div_le_iff₀ (by exact_mod_cast hs : (0 : ℝ) < s)).mpr
    exact_mod_cast hbs
  have hbasele : (4 / 19683 : ℝ) * ((b : ℝ) / s) ^ 10 ≤ 27 / 128 := by
    have hpower := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (b : ℝ) / s) hratio 10
    norm_num at hpower
    nlinarith
  calc
    _ ≤ (3 * (4 * s) / b : ℝ) ^ b * (2 * (3 * (3 * s) / b : ℝ) ^ b) *
        ((b : ℝ) / (3 * s)) ^ (12 * b) := by
      gcongr
    _ = 2 * ((3 * (4 * s) / b : ℝ) * (3 * (3 * s) / b : ℝ) *
        ((b : ℝ) / (3 * s)) ^ 12) ^ b := by
      rw [mul_pow, mul_pow, ← pow_mul]
      ring
    _ = 2 * ((4 / 19683 : ℝ) * ((b : ℝ) / s) ^ 10) ^ b := by rw [hbase]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbasele b)
      (by norm_num)

/-- Finite positive-index geometric sums have the same bound for all n. -/
theorem geometric_Icc_bound (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, (27 / 128 : ℝ) ^ j) ≤ 27 / 101 := by
  have hsum := (summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 27 / 128) (by norm_num : (27 / 128 : ℝ) < 1)).sum_le_tsum
      (insert 0 (Finset.Icc 1 n)) (fun j _ => pow_nonneg (by norm_num) j)
  rw [Finset.sum_insert (by simp), pow_zero,
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hsum
  norm_num at hsum
  linarith

end

end EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence
