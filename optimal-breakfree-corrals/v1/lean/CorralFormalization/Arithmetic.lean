import CorralFormalization.Basic

namespace CorralFormalization

theorem width_mul_two (n : ℕ) : width n * 2 = n * (n + 1) := by
  unfold width
  exact Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self n))

theorem width_pos (n : ℕ) (hn : 0 < n) : 0 < width n := by
  have hw := width_mul_two n
  nlinarith

theorem width_succ (n : ℕ) : width (n + 1) = width n + (n + 1) := by
  have hw := width_mul_two n
  have hw' := width_mul_two (n + 1)
  nlinarith

theorem mul_add_mod_eq (q r K : ℕ) (hr : r < K) :
    (q * K + r) % K = r := by
  rw [Nat.add_mod]
  simp [Nat.mod_eq_of_lt hr]

end CorralFormalization
