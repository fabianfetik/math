import CorralFormalization.Arithmetic

namespace CorralFormalization

/-- The counting lower bound in the introduction, for a positive order. -/
theorem originalCorral_order_lower_bound (h n : ℕ) (hn : 0 < n)
    (hc : OriginalCorral h n) : 2 * h - 1 ≤ n := by
  have hwidth : 0 < width n := by
    unfold width
    apply Nat.div_pos
    · nlinarith
    · omega
  letI : NeZero (width n) := ⟨by omega⟩
  obtain ⟨ρ, τ, hinj⟩ := hc
  have hcard := Fintype.card_le_of_injective (originalResidue ρ τ) hinj
  simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card] at hcard
  have hdiv : width n * 2 = n * (n + 1) := by
    unfold width
    exact Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self n))
  have hdouble := Nat.mul_le_mul_right 2 hcard
  have hmul : n * (2 * h) ≤ n * (n + 1) := by nlinarith
  have hbound := Nat.le_of_mul_le_mul_left hmul hn
  omega

end CorralFormalization
