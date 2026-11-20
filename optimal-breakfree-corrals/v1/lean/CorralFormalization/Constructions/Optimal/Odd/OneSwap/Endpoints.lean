import CorralFormalization.Constructions.Optimal.Odd.OneSwap.Factors
import CorralFormalization.Constructions.Optimal.Odd.OneSwap.Cut

namespace CorralFormalization.OneSwapOdd

theorem prefix_E_successor (A t : ℕ) (hA : 1 ≤ A) (ht : t < A) :
    oddConstructionPrefix A (2 * A + 3 + 2 * t + 1) =
      oddConstructionPrefix A (2 * A + 3 + 2 * t) + (4 * t + 2) := by
  by_cases htlast : t = A - 1
  · have hindex : 2 * A + 3 + 2 * t + 1 = 4 * A + 2 := by omega
    rw [hindex, prefix_final A hA, prefix_E A t hA ht]
    have hAt : A = t + 1 := by omega
    rw [hAt]
    unfold U h K
    ring_nf
    omega
  · have hindex : 2 * A + 3 + 2 * t + 1 = 2 * A + 4 + 2 * t := by omega
    rw [hindex, prefix_F A t hA (by omega), prefix_E A t hA ht]
    omega

/-- Position of the prefix before the cut in the five rows of the seam
certificate table. -/
def cutIndex (A s : ℕ) : ℕ :=
  if s < A then 2 * A + 3 + 2 * (A - 1 - s) else
  if s = A then 2 + 2 * A else
  if s ≤ 2 * A then 2 + 2 * (2 * A - s) else
  if s = 2 * A + 1 then 1 else 0

def cutGap (A s : ℕ) : ℕ :=
  if s < A then 4 * A - 2 - 4 * s else
  if s = A then K A + 1 else
  if s ≤ 2 * A then 4 * (s - A) else
  if s = 2 * A + 1 then K A - 1 else K A + 2

def cutDeficit (A s : ℕ) : ℕ :=
  if s < A then 2 * A - 1 - 2 * s else
  if s = A then 2 else
  if s ≤ 2 * A then 2 * s - 2 * A + 2 else
  if s = 2 * A + 1 then 2 * A + 1 else 2 * A + 3

/-- Every row of the manuscript's five-case table is a cut certificate for
the actual positive word, including the final E-gap when `A = 1`. -/
theorem cut_certificate (A : ℕ) (hA : 1 ≤ A) (s : Fin (h A)) :
    cutIndex A s.val + 1 < K A ∧
      0 < cutDeficit A s.val ∧ cutDeficit A s.val ≤ cutGap A s.val ∧
      oddConstructionPrefix A (cutIndex A s.val) + (2 * A + K A * s.val) +
        cutDeficit A s.val = U A ∧
      oddConstructionPrefix A (cutIndex A s.val + 1) =
        oddConstructionPrefix A (cutIndex A s.val) + cutGap A s.val := by
  have hs : s.val < 2 * A + 3 := s.isLt
  by_cases hs0 : s.val < A
  · simp only [cutIndex, cutGap, cutDeficit, if_pos hs0]
    have ht : A - 1 - s.val < A := by omega
    have htEq : A = (A - 1 - s.val) + s.val + 1 := by omega
    refine ⟨by unfold K; omega, by omega, by omega, ?_, ?_⟩
    · rw [prefix_E A _ hA ht]
      have hrem : 2 * A + 2 - 2 * (A - 1 - s.val) = 4 + 2 * s.val := by omega
      rw [hrem]
      have hmul := congrArg (fun x : ℕ => x * K A) htEq
      have hdelta : 2 * A - 1 - 2 * s.val + 2 * s.val + 1 = 2 * A := by omega
      simp only [Nat.add_mul] at hmul
      unfold U h K at *
      nlinarith
    · rw [prefix_E_successor A _ hA ht]
      congr 1
      omega
  · by_cases hs1 : s.val = A
    · simp only [cutIndex, cutGap, cutDeficit, if_neg hs0, if_pos hs1]
      refine ⟨by unfold K; omega, by omega, by unfold K; omega, ?_, ?_⟩
      · rw [oddConstructionPrefix_L A A (by omega), hs1]
        unfold U h K
        ring
      · have hindex : 2 + 2 * A + 1 = 2 * A + 3 := by omega
        rw [hindex, oddConstructionPrefix_L A A (by omega)]
        have hp := prefix_E A 0 hA (by omega)
        simp only [mul_zero, add_zero, Nat.sub_zero] at hp
        rw [hp]
        unfold K
        ring
    · by_cases hs2 : s.val ≤ 2 * A
      · simp only [cutIndex, cutGap, cutDeficit, if_neg hs0, if_neg hs1, if_pos hs2]
        have ht : 2 * A - s.val < A := by omega
        have htEq : 2 * A - s.val + s.val = 2 * A := by omega
        refine ⟨by unfold K; omega, by omega, by omega, ?_, ?_⟩
        · rw [oddConstructionPrefix_L A _ (by omega)]
          have hmul := congrArg (fun x : ℕ => x * K A) htEq
          have hdelta : 2 * s.val - 2 * A + 2 + 2 * A = 2 * s.val + 2 := by omega
          simp only [Nat.add_mul] at hmul
          unfold U h K at *
          nlinarith
        · have hindex : 2 + 2 * (2 * A - s.val) + 1 =
              3 + 2 * (2 * A - s.val) := by omega
          rw [hindex, oddConstructionPrefix_H A _ ht, oddConstructionPrefix_L A _ (by omega)]
          omega
      · by_cases hs3 : s.val = 2 * A + 1
        · simp only [cutIndex, cutGap, cutDeficit, if_neg hs0, if_neg hs1,
            if_neg hs2, if_pos hs3]
          refine ⟨by unfold K; omega, by omega, by unfold K; omega, ?_, ?_⟩
          · rw [oddConstructionPrefix_one, hs3]
            unfold U h K
            ring
          · have hp := oddConstructionPrefix_L A 0 (by omega)
            simp only [mul_zero, add_zero] at hp
            rw [hp, oddConstructionPrefix_one]
            unfold K
            omega
        · have hs4 : s.val = 2 * A + 2 := by omega
          simp only [cutIndex, cutGap, cutDeficit, if_neg hs0, if_neg hs1,
            if_neg hs2, if_neg hs3]
          refine ⟨by unfold K; omega, by omega, by unfold K; omega, ?_, ?_⟩
          · rw [oddConstructionPrefix_zero, hs4]
            unfold U h K
            ring
          · rw [oddConstructionPrefix_zero, oddConstructionPrefix_one]
            unfold K
            omega

theorem C_endpoints (A : ℕ) (hA : 1 ≤ A) (s : Fin (h A)) :
    (C A s).min' (C_nonempty A s) = cutGap A s.val - cutDeficit A s.val ∧
      U A - (C A s).max' (C_nonempty A s) = cutDeficit A s.val := by
  obtain ⟨hj, hδ, hδg, hcut, hnext⟩ := cut_certificate A hA s
  have hq : 2 * A + K A * s.val < U A := by
    have hs := s.isLt
    have hmul := Nat.mul_le_mul_left (K A) (by omega : s.val + 1 ≤ h A)
    unfold U K h at *
    nlinarith
  obtain ⟨hne, hmin, htail⟩ := prefix_cut_endpoints (K A) (U A)
    (2 * A + K A * s.val) (cutIndex A s.val) (cutGap A s.val)
    (cutDeficit A s.val) (oddConstructionPrefix A) (by unfold U h K; positivity)
    hq (prefix_monotone A) (fun j hj => prefix_lt A hA ⟨j, hj⟩) hj hδ hδg hcut hnext
  constructor
  · simpa only [C, Nat.add_assoc] using hmin
  · simpa only [C, Nat.add_assoc] using htail

end CorralFormalization.OneSwapOdd
