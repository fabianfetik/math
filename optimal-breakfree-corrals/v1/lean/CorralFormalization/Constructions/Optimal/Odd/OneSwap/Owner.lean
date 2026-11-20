import CorralFormalization.Constructions.Optimal.Odd.OneSwap.Endpoints

namespace CorralFormalization.OneSwapOdd

/-- The owner permutation: first swap inputs `h-2,h-1`, then add
`A+2` modulo `h`. This exchanges exactly the two specified images of the
initial rotation. -/
def owner (A : ℕ) : Equiv.Perm (Fin (h A)) := by
  letI : NeZero (h A) := ⟨by unfold h; omega⟩
  let i : Fin (h A) := ⟨2 * A + 1, by unfold h; omega⟩
  let j : Fin (h A) := ⟨2 * A + 2, by unfold h; omega⟩
  let z : Fin (h A) := ⟨A + 2, by unfold h; omega⟩
  exact (Equiv.swap i j).trans (Equiv.addRight z)

theorem owner_val (A : ℕ) (s : Fin (h A)) :
    (owner A s).val =
      ((if s.val = 2 * A + 1 then 2 * A + 2 else
        if s.val = 2 * A + 2 then 2 * A + 1 else s.val) + A + 2) % h A := by
  classical
  simp [owner, Equiv.swap_apply_def, Fin.ext_iff, Fin.val_add, Nat.add_assoc]
  split_ifs <;> rfl

/-- The five endpoint values used for seam matching. -/
theorem owner_cases (A : ℕ) (hA : 1 ≤ A) (s : Fin (h A)) :
    (owner A s).val =
      if s.val < A then s.val + A + 2 else
      if s.val = A then 2 * A + 2 else
      if s.val ≤ 2 * A then s.val - A - 1 else
      if s.val = 2 * A + 1 then A + 1 else A := by
  have hs : s.val < 2 * A + 3 := s.isLt
  rw [owner_val]
  by_cases hs0 : s.val < A
  · have hi : s.val ≠ 2 * A + 1 := by omega
    have hj : s.val ≠ 2 * A + 2 := by omega
    simp only [if_neg hi, if_neg hj, if_pos hs0]
    rw [Nat.mod_eq_of_lt (by unfold h; omega)]
  · by_cases hs1 : s.val = A
    · have hi : s.val ≠ 2 * A + 1 := by omega
      have hj : s.val ≠ 2 * A + 2 := by omega
      simp only [if_neg hi, if_neg hj, if_neg hs0, if_pos hs1]
      rw [Nat.mod_eq_of_lt (by unfold h; omega)]
      omega
    · by_cases hs2 : s.val ≤ 2 * A
      · have hi : s.val ≠ 2 * A + 1 := by omega
        have hj : s.val ≠ 2 * A + 2 := by omega
        simp only [if_neg hi, if_neg hj, if_neg hs0, if_neg hs1, if_pos hs2]
        rw [Nat.mod_eq_sub_mod (by unfold h; omega)]
        rw [Nat.mod_eq_of_lt (by unfold h; omega)]
        unfold h
        omega
      · by_cases hs3 : s.val = 2 * A + 1
        · simp only [if_pos hs3, if_neg hs0, if_neg hs1, if_neg hs2]
          rw [Nat.mod_eq_sub_mod (by unfold h; omega)]
          rw [Nat.mod_eq_of_lt (by unfold h; omega)]
          unfold h
          omega
        · have hs4 : s.val = 2 * A + 2 := by omega
          simp only [if_neg hs3, if_pos hs4, if_neg hs0, if_neg hs1, if_neg hs2]
          rw [Nat.mod_eq_sub_mod (by unfold h; omega)]
          rw [Nat.mod_eq_of_lt (by unfold h; omega)]
          unfold h
          omega

/-- The actual one-swap owner matches a physical endpoint of the two
literal factors in every row. -/
theorem owner_endpoint_match (A : ℕ) (hA : 1 ≤ A) (s : Fin (h A)) :
    (C A s).min' (C_nonempty A s) =
        (D A (owner A s)).min' (D_nonempty A (owner A s)) ∨
      U A - (C A s).max' (C_nonempty A s) =
        2 * h A - (D A (owner A s)).max' (D_nonempty A (owner A s)) := by
  obtain ⟨hcmin, hctail⟩ := C_endpoints A hA s
  rw [hcmin, hctail, D_min, D_tail, owner_cases A hA s]
  have hs : s.val < 2 * A + 3 := s.isLt
  simp only [cutGap, cutDeficit, K]
  split_ifs <;> omega

end CorralFormalization.OneSwapOdd
