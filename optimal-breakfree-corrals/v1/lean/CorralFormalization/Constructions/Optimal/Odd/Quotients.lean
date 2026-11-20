import CorralFormalization.Constructions.Optimal.Odd.Transversal

namespace CorralFormalization

/-! This module uses the earlier two-swap odd construction. References to
the paper and its numbered equations below concern that earlier manuscript,
not the one-swap odd construction printed in the manuscript. -/

/-- The physical point obtained by shifting a proper prefix as in §4.3. -/
def oddConstructionShiftedPoint (A j : ℕ) : ℕ :=
  (oddConstructionPrefix A j + (2 * A - 3)) % ((2 * A + 3) * (4 * A + 3))

/-- A bounded quotient/remainder pair represents its own physical point. -/
theorem oddConstructionShiftedPoint_eq_block
    (A j q r : ℕ) (hq : q < 2 * A + 3) (hr : r < 4 * A + 3)
    (hpoint : oddConstructionPrefix A j + (2 * A - 3) = q * (4 * A + 3) + r) :
    oddConstructionShiftedPoint A j = q * (4 * A + 3) + r := by
  unfold oddConstructionShiftedPoint
  rw [hpoint]
  apply Nat.mod_eq_of_lt
  have hmul := Nat.mul_le_mul_right (4 * A + 3) (by omega : q + 1 ≤ 2 * A + 3)
  nlinarith

/-- The `L_t` prefix in (5), indexed by its position in the actual word. -/
theorem oddConstructionPrefix_L (A t : ℕ) (ht : t ≤ A) :
    oddConstructionPrefix A (2 + 2 * t) = (t + 2) * (4 * A + 3) + 2 * t + 1 := by
  unfold oddConstructionPrefix
  rw [oddConstructionGapWord_take_before_middle A (2 + 2 * t) (by omega) (by omega)]
  rw [List.sum_append]
  simp only [List.sum_cons, List.sum_nil]
  have heq : 2 + 2 * t - 2 = 2 * t := by omega
  rw [heq, oddConstructionFirstPairs_take_complete_sum A t ht]
  ring

/-- The `H_t` prefix in (5), indexed by its position in the actual word. -/
theorem oddConstructionPrefix_H (A t : ℕ) (ht : t < A) :
    oddConstructionPrefix A (3 + 2 * t) =
      (t + 2) * (4 * A + 3) + (4 * A + 3 - 2 * t - 2) := by
  unfold oddConstructionPrefix
  rw [oddConstructionGapWord_take_before_middle A (3 + 2 * t) (by omega) (by omega)]
  rw [List.sum_append]
  simp only [List.sum_cons, List.sum_nil]
  have heq : 3 + 2 * t - 2 = 2 * t + 1 := by omega
  rw [heq, oddConstructionFirstPairs_take_one_more_sum A t ht]
  have hgap : 4 * A + 3 - 3 - 4 * t = 4 * A - 4 * t := by omega
  rw [hgap]
  have hrem : 4 * A + 3 - 2 * t - 2 = 4 * A + 1 - 2 * t := by omega
  rw [hrem]
  ring_nf
  omega

/-- The `E_t` prefix in (5), indexed by its position in the actual word. -/
theorem oddConstructionPrefix_E (A t : ℕ) (hA : 2 ≤ A) (ht : t < A) :
    oddConstructionPrefix A (2 * A + 3 + 2 * t) =
      (A + 3 + t) * (4 * A + 3) + (2 * A + 2 - 2 * t) := by
  unfold oddConstructionPrefix
  rw [oddConstructionGapWord_take_second_block A (2 * A + 3 + 2 * t) (by omega) (by omega)]
  rw [List.sum_append, oddConstructionPreSecond_sum]
  have heq : 2 * A + 3 + 2 * t - (2 * A + 3) = 2 * t := by omega
  rw [heq, oddConstructionSecondPairs_take_complete_sum A t (by omega)]
  ring_nf
  omega

/-- The `F_t` prefix in (5), indexed by its position in the actual word. -/
theorem oddConstructionPrefix_F (A t : ℕ) (hA : 2 ≤ A) (ht : t < A - 1) :
    oddConstructionPrefix A (2 * A + 4 + 2 * t) =
      (A + 3 + t) * (4 * A + 3) + (2 * A + 4 + 2 * t) := by
  unfold oddConstructionPrefix
  rw [oddConstructionGapWord_take_second_block A (2 * A + 4 + 2 * t) (by omega) (by omega)]
  rw [List.sum_append, oddConstructionPreSecond_sum]
  have heq : 2 * A + 4 + 2 * t - (2 * A + 3) = 2 * t + 1 := by omega
  rw [heq, oddConstructionSecondPairs_take_one_more_sum A t ht]
  ring_nf

/-- The shifted prefix `0` in the paper's quotient/remainder table (10). -/
theorem oddConstructionShifted_zero (A : ℕ) (hA : 2 ≤ A) :
    oddConstructionShiftedPoint A 0 = 2 * A - 3 := by
  have hpoint : oddConstructionPrefix A 0 + (2 * A - 3) =
      0 * (4 * A + 3) + (2 * A - 3) := by simp [oddConstructionPrefix_zero]
  simpa using oddConstructionShiftedPoint_eq_block A 0 0 (2 * A - 3)
    (by omega) (by omega) hpoint

/-- The shifted prefix `K+2` in table (10). -/
theorem oddConstructionShifted_one (A : ℕ) (hA : 2 ≤ A) :
    oddConstructionShiftedPoint A 1 = 1 * (4 * A + 3) + (2 * A - 1) := by
  apply oddConstructionShiftedPoint_eq_block A 1 1 (2 * A - 1) (by omega) (by omega)
  rw [oddConstructionPrefix_one]
  omega

/-- The `L_t` quotient/remainder pair in (10). -/
theorem oddConstructionShifted_L (A t : ℕ) (hA : 2 ≤ A) (ht : t ≤ A) :
    oddConstructionShiftedPoint A (2 + 2 * t) =
      (t + 2) * (4 * A + 3) + (2 * A + 2 * t - 2) := by
  apply oddConstructionShiftedPoint_eq_block A (2 + 2 * t) (t + 2)
    (2 * A + 2 * t - 2) (by omega) (by omega)
  rw [oddConstructionPrefix_L A t ht]
  omega

/-- The first range of `H_t` pairs in (10), before the quotient changes. -/
theorem oddConstructionShifted_H_early (A t : ℕ) (hA : 2 ≤ A) (ht : t + 3 ≤ A) :
    oddConstructionShiftedPoint A (3 + 2 * t) =
      (t + 3) * (4 * A + 3) + (2 * A - 2 * t - 5) := by
  apply oddConstructionShiftedPoint_eq_block A (3 + 2 * t) (t + 3)
    (2 * A - 2 * t - 5) (by omega) (by omega)
  rw [oddConstructionPrefix_H A t (by omega)]
  have hmul : (t + 3) * (4 * A + 3) = (t + 2) * (4 * A + 3) + (4 * A + 3) := by ring
  rw [hmul]
  omega

/-- The final two `H_t` pairs in (10), after the quotient change. -/
theorem oddConstructionShifted_H_late (A t : ℕ) (hA : 2 ≤ A)
    (ht : t < A) (hlate : A ≤ t + 2) :
    oddConstructionShiftedPoint A (3 + 2 * t) =
      (t + 2) * (4 * A + 3) + (4 * A + 3 + 2 * A - 2 * t - 5) := by
  apply oddConstructionShiftedPoint_eq_block A (3 + 2 * t) (t + 2)
    (4 * A + 3 + 2 * A - 2 * t - 5) (by omega) (by omega)
  rw [oddConstructionPrefix_H A t ht]
  omega

/-- The `E_t` quotient/remainder pair in (10). -/
theorem oddConstructionShifted_E (A t : ℕ) (hA : 2 ≤ A) (ht : t < A) :
    oddConstructionShiftedPoint A (2 * A + 3 + 2 * t) =
      (A + 3 + t) * (4 * A + 3) + (4 * A + 3 - 4 - 2 * t) := by
  apply oddConstructionShiftedPoint_eq_block A (2 * A + 3 + 2 * t) (A + 3 + t)
    (4 * A + 3 - 4 - 2 * t) (by omega) (by omega)
  rw [oddConstructionPrefix_E A t hA ht]
  omega

/-- The special `F_0` pair in (10). -/
theorem oddConstructionShifted_F_zero (A : ℕ) (hA : 2 ≤ A) :
    oddConstructionShiftedPoint A (2 * A + 4) =
      (A + 3) * (4 * A + 3) + (4 * A + 3 - 2) := by
  apply oddConstructionShiftedPoint_eq_block A (2 * A + 4) (A + 3)
    (4 * A + 3 - 2) (by omega) (by omega)
  have hp := oddConstructionPrefix_F A 0 hA (by omega)
  simp only [mul_zero, add_zero] at hp
  rw [hp]
  omega

/-- The remaining `F_t` pairs in (10), after crossing a block boundary. -/
theorem oddConstructionShifted_F_pos (A t : ℕ) (hA : 2 ≤ A)
    (ht : t < A - 1) (htpos : 1 ≤ t) :
    oddConstructionShiftedPoint A (2 * A + 4 + 2 * t) =
      (A + 4 + t) * (4 * A + 3) + (2 * t - 2) := by
  apply oddConstructionShiftedPoint_eq_block A (2 * A + 4 + 2 * t) (A + 4 + t)
    (2 * t - 2) (by omega) (by omega)
  rw [oddConstructionPrefix_F A t hA ht]
  have hmul : (A + 4 + t) * (4 * A + 3) =
      (A + 3 + t) * (4 * A + 3) + (4 * A + 3) := by ring
  rw [hmul]
  omega

/-- The last proper prefix wraps to the first block, as in (10). -/
theorem oddConstructionShifted_final (A : ℕ) (hA : 2 ≤ A) :
    oddConstructionShiftedPoint A (4 * A + 2) = 2 * A - 4 := by
  unfold oddConstructionShiftedPoint
  rw [oddConstructionPrefix_final_value A hA]
  have heq : (2 * A + 2) * (4 * A + 3) + (4 * A + 2) + (2 * A - 3) =
      (2 * A + 3) * (4 * A + 3) + (2 * A - 4) := by
    have hmul : (2 * A + 3) * (4 * A + 3) =
        (2 * A + 2) * (4 * A + 3) + (4 * A + 3) := by ring
    rw [hmul]
    omega
  rw [heq, Nat.add_mod]
  simp only [Nat.mod_self, zero_add]
  have hwidth : 2 * A + 3 ≤ (2 * A + 3) * (4 * A + 3) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hlt : 2 * A - 4 < (2 * A + 3) * (4 * A + 3) := by omega
  simp [Nat.mod_eq_of_lt hlt]

end CorralFormalization
