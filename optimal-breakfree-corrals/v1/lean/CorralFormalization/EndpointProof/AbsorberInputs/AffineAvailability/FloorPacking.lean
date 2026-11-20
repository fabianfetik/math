import CorralFormalization.EndpointProof.Probability.RateBudget

/-! Elementary floor and exponential-budget estimates for actual packed
families. No existence or probabilistic event is assumed here. -/

namespace AbsorberInputs.AffineAvailability

/-- A quotient is at least half its real value once the dividend is at least
    twice the positive divisor. -/
theorem nat_div_linear_lower (n d : ℕ) (hd : 0 < d) (hn : 2*d ≤ n) :
    (n : ℝ) / (2*(d : ℝ)) ≤ (n / d : ℕ) := by
  have hq : 1 ≤ n / d := Nat.div_pos (by omega) hd
  have hqd : d ≤ d*(n/d) := by
    calc
      d = d*1 := by simp
      _ ≤ d*(n/d) := Nat.mul_le_mul_left d hq
  have hrem := Nat.mod_lt n hd
  have hsum := Nat.div_add_mod n d
  have hnat : n ≤ 2*(d*(n/d)) := by omega
  have hreal : (n : ℝ) ≤ (n/d : ℕ) * (2*(d : ℝ)) := by
    have hx : (n : ℝ) ≤ 2 * ((d : ℝ) * ((n/d : ℕ) : ℝ)) := by exact_mod_cast hnat
    nlinarith
  have hden : (0 : ℝ) < 2*(d : ℝ) := by positivity
  exact (div_le_iff₀ hden).2 hreal

/-- The size `floor(n/(4m²))` used by the deterministic packing is at
least a fixed positive fraction of n. -/
theorem affine_packing_floor_linear (n m : ℕ) (hm : 0 < m)
    (hn : 2*(4*m*m) ≤ n) :
    (1 / (2*(4*(m : ℝ)*m))) * n ≤ (n/(4*m*m) : ℕ) := by
  have hd : 0 < 4*m*m := by positivity
  have h := nat_div_linear_lower n (4*m*m) hd hn
  convert h using 1
  all_goals push_cast
  all_goals ring

/-- A fixed polynomial union factor is eventually absorbed by retaining
half of any positive exponential rate. -/
theorem polynomial_failure_absorbed (C a : ℝ) (k : ℕ) (ha : 0 < a) :
    ∃ N : ℕ, ∀ n ≥ N,
      C * (n : ℝ)^k * Real.exp (-a*n) ≤ Real.exp (-(a/2)*n) := by
  exact CorralFormalization.EndpointProof.RateBudget.polynomial_union_absorbed
    C a (a/2) k (by linarith)

end AbsorberInputs.AffineAvailability
