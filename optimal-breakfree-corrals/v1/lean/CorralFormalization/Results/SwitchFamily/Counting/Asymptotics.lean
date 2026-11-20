import CorralFormalization.Results.SwitchFamily.Counting.Periods

/-!
# Uniform proper-divisor estimates with a height-dependent decoration alphabet

These are proved transfer theorems. The base layout growth hypotheses in
`moving_alphabet_asymptotic` are explicit: the plastic-constant spectral
calculation supplying them is not silently assumed as an axiom.
-/

namespace CorralFormalization.Results.SwitchFamily.Counting

open Finset Filter Topology

noncomputable def properMoebiusSum (F : ℕ → ℝ) (h : ℕ) (Q : ℝ) : ℝ :=
  ∑ d ∈ h.divisors.erase 1, (ArithmeticFunction.moebius d : ℝ) * F (h/d) * Q^(h/d)

/-- Every divisor term other than d=1 has quotient exponent at most h/2. -/
theorem proper_quotient_le_half {h d : ℕ} (hd : d ∈ h.divisors.erase 1) :
    h/d ≤ h/2 := by
  have hd0 : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_erase.mp hd).2
  have hd1 : d ≠ 1 := (Finset.mem_erase.mp hd).1
  have hd2 : 2 ≤ d := by omega
  have hprod := Nat.div_mul_le_self h d
  have hprod2 := Nat.mul_le_mul_left (h/d) hd2
  omega

theorem proper_quotient_pos {h d : ℕ} (hd : d ∈ h.divisors.erase 1) : 0 < h/d := by
  have hdiv := (Nat.mem_divisors.mp (Finset.mem_erase.mp hd).2).1
  have hd0 := Nat.pos_of_mem_divisors (Finset.mem_erase.mp hd).2
  have hh0 := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr
    ⟨dvd_refl h,(Nat.mem_divisors.mp (Finset.mem_erase.mp hd).2).2⟩)
  exact Nat.div_pos (Nat.le_of_dvd hh0 hdiv) hd0

/-- The O(h (lambda Q)^(h/2)) estimate is uniform in every Q >= 1. -/
theorem properMoebiusSum_bound (F : ℕ → ℝ) {K lam Q : ℝ}
    (hK : 0 ≤ K) (hlam : 1 ≤ lam) (hQ : 1 ≤ Q)
    (hF : ∀ j > 0, |F j| ≤ K*lam^j) (h : ℕ) :
    |properMoebiusSum F h Q| ≤ K * h * (lam*Q)^(h/2) := by
  have hlam0 : 0 ≤ lam := le_trans (by norm_num) hlam
  have hQ0 : 0 ≤ Q := le_trans (by norm_num) hQ
  have hbase : 1 ≤ lam*Q := by nlinarith
  have hterm : ∀ d ∈ h.divisors.erase 1,
      |(ArithmeticFunction.moebius d : ℝ) * F (h/d) * Q^(h/d)| ≤ K*(lam*Q)^(h/2) := by
    intro d hd
    have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    calc
      |(ArithmeticFunction.moebius d : ℝ) * F (h/d) * Q^(h/d)| =
          |(ArithmeticFunction.moebius d : ℝ)| * |F (h/d)| * Q^(h/d) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hQ0 _)]
      _ ≤ 1 * (K*lam^(h/d)) * Q^(h/d) := by
        gcongr
        exact hF _ (proper_quotient_pos hd)
      _ = K*(lam*Q)^(h/d) := by rw [mul_pow]; ring
      _ ≤ K*(lam*Q)^(h/2) := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (proper_quotient_le_half hd)) hK
  calc
    |properMoebiusSum F h Q| ≤ ∑ d ∈ h.divisors.erase 1,
        |(ArithmeticFunction.moebius d : ℝ) * F (h/d) * Q^(h/d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ h.divisors.erase 1, K*(lam*Q)^(h/2) := Finset.sum_le_sum hterm
    _ = ((h.divisors.erase 1).card : ℝ) * (K*(lam*Q)^(h/2)) := by simp
    _ ≤ (h : ℝ) * (K*(lam*Q)^(h/2)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (Finset.card_erase_le (s := h.divisors) (a := 1)).trans (Nat.card_divisors_le_self h)
    _ = K*h*(lam*Q)^(h/2) := by ring

/-- After division by the main exponential, Q disappears from the bound. -/
theorem properMoebiusSum_relative_bound (F : ℕ → ℝ) {K lam Q : ℝ}
    (hK : 0 ≤ K) (hlam : 1 < lam) (hQ : 1 ≤ Q)
    (hF : ∀ j > 0, |F j| ≤ K*lam^j) (h : ℕ) :
    |properMoebiusSum F h Q / (lam*Q)^h| ≤ K*h/lam^(h-h/2) := by
  have hlam0 : 0 < lam := lt_trans (by norm_num) hlam
  have hQ0 : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hb0 : 0 < lam*Q := mul_pos hlam0 hQ0
  have hpow : (lam*Q)^h = (lam*Q)^(h/2) * (lam*Q)^(h-h/2) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self h 2)]
  have hbase : lam ≤ lam*Q := by nlinarith
  calc
    |properMoebiusSum F h Q / (lam*Q)^h| =
        |properMoebiusSum F h Q| / (lam*Q)^h := by
      rw [abs_div, abs_of_pos (pow_pos hb0 _)]
    _ ≤ (K*h*(lam*Q)^(h/2))/(lam*Q)^h := by
      exact div_le_div_of_nonneg_right (properMoebiusSum_bound F hK hlam.le hQ hF h)
        (le_of_lt (pow_pos hb0 _))
    _ = K*h/(lam*Q)^(h-h/2) := by
      rw [hpow]
      field_simp
    _ ≤ K*h/lam^(h-h/2) := by
      apply div_le_div_of_nonneg_left (by positivity) (pow_pos hlam0 _)
      exact pow_le_pow_left₀ hlam0.le hbase _

private theorem tendsto_half : Tendsto (fun h : ℕ => h/2) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro k
  filter_upwards [Filter.eventually_ge_atTop (2*k)] with h hh
  omega

/-- An explicit Q-independent error envelope tends to zero. -/
theorem relative_envelope_tendsto_zero {K lam : ℝ} (hK : 0 ≤ K) (hlam : 1 < lam) :
    Tendsto (fun h : ℕ => K*h/lam^(h-h/2)) atTop (𝓝 0) := by
  have hlam0 : 0 < lam := lt_trans (by norm_num) hlam
  have hk : Tendsto (fun k : ℕ => K*(2*k+1)/lam^k) atTop (𝓝 0) := by
    have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 1 hlam).const_mul (2*K)
    have h0 := (tendsto_pow_const_div_const_pow_of_one_lt 0 hlam).const_mul K
    convert h1.add h0 using 1
    · funext k
      simp only [pow_one, pow_zero]
      ring
    · simp
  apply squeeze_zero (fun h => by positivity) _ (hk.comp tendsto_half)
  intro h
  have hhnum : (h : ℝ) ≤ 2*(h/2 : ℕ)+1 := by
    have hh : h ≤ 2*(h/2)+1 := by omega
    exact_mod_cast hh
  have hhexp : h/2 ≤ h-h/2 := by omega
  calc
    K*h/lam^(h-h/2) ≤ K*(2*(h/2 : ℕ)+1)/lam^(h-h/2) := by
      gcongr
    _ ≤ K*(2*(h/2 : ℕ)+1)/lam^(h/2) := by
      apply div_le_div_of_nonneg_left (by positivity) (pow_pos hlam0 _)
      exact pow_le_pow_right₀ hlam.le hhexp

/-- Q may be any function of h, including 2^(m(h)) with unbounded m. -/
theorem moving_alphabet_proper_error (F : ℕ → ℝ) {K lam : ℝ}
    (hK : 0 ≤ K) (hlam : 1 < lam) (hF : ∀ j > 0, |F j| ≤ K*lam^j)
    (Q : ℕ → ℝ) (hQ : ∀ h, 1 ≤ Q h) :
    Tendsto (fun h : ℕ => properMoebiusSum F h (Q h)/(lam*Q h)^h) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_norm_tendsto_zero).mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun _ => abs_nonneg _) (fun h =>
    properMoebiusSum_relative_bound F hK hlam (hQ h) hF h)
    (relative_envelope_tendsto_zero hK hlam)

end CorralFormalization.Results.SwitchFamily.Counting

namespace CorralFormalization.Results.SwitchFamily.Counting

open Finset Filter Topology

noncomputable def moebiusSum (F : ℕ → ℝ) (h : ℕ) (Q : ℝ) : ℝ :=
  ∑ d ∈ h.divisors, (ArithmeticFunction.moebius d : ℝ) * F (h/d) * Q^(h/d)

theorem moebiusSum_eq_main_add_proper (F : ℕ → ℝ) (h : ℕ) (Q : ℝ) (hh : h ≠ 0) :
    moebiusSum F h Q = F h * Q^h + properMoebiusSum F h Q := by
  have hmem : 1 ∈ h.divisors := Nat.mem_divisors.mpr ⟨one_dvd _,hh⟩
  rw [moebiusSum, properMoebiusSum, ← Finset.add_sum_erase _ _ hmem]
  simp

/-- Uniform passage from base growth to the Möbius numerator, even when the
alphabet size changes with h. The base spectral asymptotic is an explicit
hypothesis and has not been replaced by an axiom. -/
theorem moving_alphabet_asymptotic (F : ℕ → ℝ) {K lam : ℝ}
    (hK : 0 ≤ K) (hlam : 1 < lam)
    (hF : ∀ j > 0, |F j| ≤ K*lam^j)
    (hbase : Tendsto (fun h : ℕ => F h/lam^h) atTop (𝓝 1))
    (Q : ℕ → ℝ) (hQ : ∀ h, 1 ≤ Q h) :
    Tendsto (fun h : ℕ => moebiusSum F h (Q h)/(lam*Q h)^h) atTop (𝓝 1) := by
  have he := hbase.add (moving_alphabet_proper_error F hK hlam hF Q hQ)
  simp only [add_zero] at he
  apply he.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with h hh
  have hlam0 : lam ≠ 0 := ne_of_gt (lt_trans (by norm_num) hlam)
  have hQ0 : Q h ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (hQ h))
  rw [moebiusSum_eq_main_add_proper F h (Q h) (by omega)]
  rw [add_div, mul_pow]
  field_simp

/-- The preceding theorem applies to the actual marked primitive count.
Q(h) is chosen once at each h; all divisor terms use that same Q(h). -/
theorem moving_primitive_asymptotic {K lam : ℝ}
    (hK : 0 ≤ K) (hlam : 1 < lam)
    (hC : ∀ j > 0, |(C j : ℝ)| ≤ K*lam^j)
    (hbase : Tendsto (fun h : ℕ => (C h : ℝ)/lam^h) atTop (𝓝 1))
    (Q : ℕ → ℕ) (hQ : ∀ h, 1 ≤ Q h) :
    Tendsto (fun h : ℕ => (primitiveCount h (Q h) : ℝ)/(lam*(Q h : ℝ))^h)
      atTop (𝓝 1) := by
  have he := moving_alphabet_asymptotic (fun h => (C h : ℝ)) hK hlam hC hbase
    (fun h => (Q h : ℝ)) (fun h => by exact_mod_cast hQ h)
  apply he.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with h hh
  letI : NeZero h := ⟨by omega⟩
  congr 1
  unfold moebiusSum
  have hi := congrArg (fun z : ℤ => (z : ℝ)) (primitiveCount_moebius h (Q h)).symm
  push_cast at hi
  exact hi

/-- The normalized count of actual primitive cyclic orbits has the same
asymptotic. This theorem still displays the exact two base-growth inputs. -/
theorem moving_aperiodic_orbit_asymptotic {K lam : ℝ}
    (hK : 0 ≤ K) (hlam : 1 < lam)
    (hC : ∀ j > 0, |(C j : ℝ)| ≤ K*lam^j)
    (hbase : Tendsto (fun h : ℕ => (C h : ℝ)/lam^h) atTop (𝓝 1))
    (Q : ℕ → ℕ) (hQ : ∀ h, 1 ≤ Q h) :
    Tendsto (fun h : ℕ => ((aperiodicOrbitCount h (Q h) : ℝ)*h)/(lam*(Q h : ℝ))^h)
      atTop (𝓝 1) := by
  have he := moving_primitive_asymptotic hK hlam hC hbase Q hQ
  apply he.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with h hh
  letI : NeZero h := ⟨by omega⟩
  congr 1
  exact_mod_cast (aperiodic_orbit_mul h (Q h)).symm

end CorralFormalization.Results.SwitchFamily.Counting
