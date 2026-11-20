import CorralFormalization.DiversityCompletion.EvenSwitchesB

namespace CorralFormalization.EvenSwitches

theorem liftB_lower (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (j : ℕ) :
    liftB m a (4 * m + 2 + 2 * j) = lowerB m a.1 j + clock m := by
  have hq : 4 * m + 2 + 2 * j - (4 * m + 2) = 2 * j := by omega
  have hp : (2 * j) % 2 = 0 := by omega
  have hd : (2 * j) / 2 = j := by omega
  have h0 : 4 * m + 2 + 2 * j ≠ 0 := by omega
  have h1 : 4 * m + 2 + 2 * j ≠ 1 := by omega
  have h2 : 4 * m + 2 + 2 * j ≠ 2 := by omega
  have hl : ¬ (4 * m + 2 + 2 * j < 4 * m) := by omega
  have h4 : 4 * m + 2 + 2 * j ≠ 4 * m := by omega
  have h41 : 4 * m + 2 + 2 * j ≠ 4 * m + 1 := by omega
  simp only [liftB, if_neg h0, if_neg h1, if_neg h2, if_neg hl, if_neg h4, if_neg h41, hq, if_pos hp, hd]

theorem liftB_middle (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (j : ℕ) (hj : 0 < j) :
    liftB m a (4 * m + 1 + 2 * j) = middleB m j + clock m := by
  have hq : 4 * m + 1 + 2 * j - (4 * m + 2) = 2 * j - 1 := by omega
  have hp : (2 * j - 1) % 2 ≠ 0 := by omega
  have hd : (2 * j - 1 + 1) / 2 = j := by omega
  have h0 : 4 * m + 1 + 2 * j ≠ 0 := by omega
  have h1 : 4 * m + 1 + 2 * j ≠ 1 := by omega
  have h2 : 4 * m + 1 + 2 * j ≠ 2 := by omega
  have hl : ¬ (4 * m + 1 + 2 * j < 4 * m) := by omega
  have h4 : 4 * m + 1 + 2 * j ≠ 4 * m := by omega
  have h41 : 4 * m + 1 + 2 * j ≠ 4 * m + 1 := by omega
  simp only [liftB, if_neg h0, if_neg h1, if_neg h2, if_neg hl, if_neg h4, if_neg h41, hq, if_neg hp, hd]

theorem liftB_upper (m : ℕ) (a : Choices m) (j : ℕ) (hj0 : 0 < j) (hj : j < 2 * m) :
    liftB m a (2 * j + 1) = upperB m a.2 j := by
  have hp : (2 * j + 1) % 2 = 1 := by omega
  have hd : (2 * j + 1 - 1) / 2 = j := by omega
  have h0 : 2 * j + 1 ≠ 0 := by omega
  have h1 : 2 * j + 1 ≠ 1 := by omega
  have h2 : 2 * j + 1 ≠ 2 := by omega
  have hl : 2 * j + 1 < 4 * m := by omega
  simp only [liftB, if_neg h0, if_neg h1, if_neg h2, if_pos hl, if_pos hp, hd]

theorem liftB_endpoints (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    liftB m a 0 = (height m) ^ 2 - 1 ∧ liftB m a 1 = (height m) ^ 2 ∧
    liftB m a 2 = upperB m a.2 0 ∧
    liftB m a (4 * m) = upperB m a.2 (2 * m) ∧
    liftB m a (4 * m + 1) = clock m - 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp (disch := omega) [liftB]
  all_goals (try split_ifs) <;> omega

theorem liftB_fixed (m : ℕ) (a : Choices m) (r : ℕ) (hr : r + 1 < m) :
    liftB m a (4 + 4 * r) = fixedB m r ∧
    liftB m a (6 + 4 * r) = fixedB m r + height m - 1 := by
  have hp : (4 + 4 * r) % 2 ≠ 1 := by omega
  have hp' : (6 + 4 * r) % 2 ≠ 1 := by omega
  have hq : (4 + 4 * r) % 4 = 0 := by omega
  have hq' : (6 + 4 * r) % 4 ≠ 0 := by omega
  have hd : (4 + 4 * r - 4) / 4 = r := by omega
  have hd' : (6 + 4 * r - 6) / 4 = r := by omega
  have h10 : 4 + 4 * r ≠ 0 := by omega
  have h11 : 4 + 4 * r ≠ 1 := by omega
  have h12 : 4 + 4 * r ≠ 2 := by omega
  have hl : 4 + 4 * r < 4 * m := by omega
  have h20 : 6 + 4 * r ≠ 0 := by omega
  have h21 : 6 + 4 * r ≠ 1 := by omega
  have h22 : 6 + 4 * r ≠ 2 := by omega
  have hl' : 6 + 4 * r < 4 * m := by omega
  simp only [liftB, if_neg h10, if_neg h11, if_neg h12, if_pos hl, if_neg hp, if_pos hq, hd,
    if_neg h20, if_neg h21, if_neg h22, if_pos hl', if_neg hp', if_neg hq', hd']
  simp

set_option maxHeartbeats 1000000 in
theorem B_fixed_seams (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    ((height m) ^ 2 - 1) + 1 = (height m) ^ 2 ∧
    (height m) ^ 2 + (height m - 2) = upperB m a.2 0 ∧
    upperB m a.2 0 + order m = upperB m a.2 1 ∧
    upperB m a.2 (2 * m - 1) + (2 * height m - 3) = upperB m a.2 (2 * m) ∧
    upperB m a.2 (2 * m) + (height m - 1) = clock m - 1 ∧
    (clock m - 1) + height m = lowerB m a.1 0 + clock m ∧
    lowerB m a.1 0 + (height m + 1) = middleB m 1 ∧
    middleB m (2 * m) + 2 = lowerB m a.1 (2 * m) ∧
    lowerB m a.1 (2 * m) + (2 * height m - 2) = (height m) ^ 2 - 1 := by
  have hheight : height m - 1 = 4 * m + 1 := by unfold height; omega
  have hheight' : height m - 2 = 4 * m := by unfold height; omega
  have htwice : 2 * height m - 3 = 8 * m + 1 := by unfold height; omega
  have htwice' : 2 * height m - 2 = 8 * m + 2 := by unfold height; omega
  have hcoef : 2 * (2 * m) + 2 - 1 = 4 * m + 1 := by omega
  have hmod : (2 * m) % 2 = 0 := by omega
  have hpred : 2 * m - 1 + 1 = 2 * m := by omega
  have hpredmul := congrArg (fun t => m * t) hpred
  have hsq := Nat.sub_add_cancel (show 1 ≤ (height m) ^ 2 by unfold height; nlinarith)
  have hMpos : 0 < clock m := by unfold clock height order; positivity
  have hM := Nat.sub_add_cancel (show 1 ≤ clock m by omega)
  have hmid := Nat.sub_add_cancel (show 1 ≤ 2 * height m * (2 * m) by unfold height; nlinarith)
  unfold lowerB upperB middleB
  simp only [eta_zero, eta_last, epsilon_zero, epsilon_last, epsilon_one m hm,
    epsilon_penultimate m hm, hheight, hheight', htwice, htwice', hcoef,
    Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.one_mod, hmod,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.sub_self, Nat.mul_one, Nat.one_mul]
  unfold clock at *
  unfold height order at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem B_extra_upper_seams (m : ℕ) (hm : 2 ≤ m) (a : Choices m) :
    upperB m a.2 1 + (height m + 3) = fixedB m 0 ∧
    (fixedB m (m - 2) + height m - 1) + (height m + 4) = upperB m a.2 (2 * m - 1) := by
  have hheight : height m - 1 = 4 * m + 1 := by unfold height; omega
  have hpred : 2 * m - 1 + 1 = 2 * m := by omega
  have hpredmul := congrArg (fun t => m * t) hpred
  have hm' : m - 2 + 2 = m := by omega
  have hmul := congrArg (fun t => m * t) hm'
  have hw := Nat.sub_add_cancel (show 1 ≤ fixedB m (m - 2) + height m by unfold height; omega)
  unfold upperB fixedB at *
  simp only [epsilon_one m (by omega), epsilon_penultimate m (by omega), hheight,
    Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
  unfold height halfHeight at *
  constructor <;> nlinarith

theorem switchEdgeBNat_fixed (m : ℕ) (a : Choices m) (i : ℕ)
    (hl : ¬ (2 ≤ i ∧ i < 4 * m)) (hu : ¬ (4 * m + 3 ≤ i ∧ i ≤ 8 * m)) :
    switchEdgeBNat m a i = i := by simp [switchEdgeBNat, hl, hu]

theorem switchEdgeBNat_upper_ends (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    switchEdgeBNat m a 2 = 2 ∧ switchEdgeBNat m a 3 = 3 ∧
    switchEdgeBNat m a (4 * m - 2) = 4 * m - 2 ∧
    switchEdgeBNat m a (4 * m - 1) = 4 * m - 1 := by
  have h2 : 2 ≤ 2 ∧ 2 < 4 * m := by omega
  have h3 : 2 ≤ 3 ∧ 3 < 4 * m := by omega
  have h2' : 2 ≤ 4 * m - 2 ∧ 4 * m - 2 < 4 * m := by omega
  have h3' : 2 ≤ 4 * m - 1 ∧ 4 * m - 1 < 4 * m := by omega
  have hd2 : (4 * m - 2) / 2 = 2 * m - 1 := by omega
  have hd3 : (4 * m - 1) / 2 = 2 * m - 1 := by omega
  simp only [switchEdgeBNat, if_pos h2, if_pos h3, if_pos h2', if_pos h3', hd2, hd3,
    show 2 / 2 = 1 by decide, show 3 / 2 = 1 by decide,
    epsilon_one m hm, epsilon_penultimate m hm, if_pos rfl]
  simp

theorem switched_B_fixed_gaps (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    baselineGapB m (switchEdgeBNat m a 0) = 1 ∧
    baselineGapB m (switchEdgeBNat m a 1) = height m - 2 ∧
    baselineGapB m (switchEdgeBNat m a 2) = order m ∧
    baselineGapB m (switchEdgeBNat m a (4 * m - 1)) = 2 * height m - 3 ∧
    baselineGapB m (switchEdgeBNat m a (4 * m)) = height m - 1 ∧
    baselineGapB m (switchEdgeBNat m a (4 * m + 1)) = height m ∧
    baselineGapB m (switchEdgeBNat m a (4 * m + 2)) = height m + 1 ∧
    baselineGapB m (switchEdgeBNat m a (8 * m + 1)) = 2 ∧
    baselineGapB m (switchEdgeBNat m a (8 * m + 2)) = 2 * height m - 2 := by
  have he := switchEdgeBNat_upper_ends m hm a
  rw [he.1, he.2.2.2]
  have hf := baselineGapB_fixed m hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try rw [switchEdgeBNat_fixed m a _ (by omega) (by omega)]
  all_goals try simp only [height, order] at *
  all_goals omega

theorem switched_B_extra_gaps (m : ℕ) (hm : 2 ≤ m) (a : Choices m) :
    baselineGapB m (switchEdgeBNat m a 3) = height m + 3 ∧
    baselineGapB m (switchEdgeBNat m a (4 * m - 2)) = height m + 4 := by
  rw [(switchEdgeBNat_upper_ends m (by omega) a).2.1,
    (switchEdgeBNat_upper_ends m (by omega) a).2.2.1]
  rw [baselineGapB_upper_formula m 3 (by omega) (by omega),
    baselineGapB_upper_formula m (4 * m - 2) (by omega) (by omega)]
  constructor <;> unfold height <;> split_ifs <;> omega

theorem B_lower_edges (m : ℕ) (hm : 1 ≤ m) (a : Choices m)
    (j : ℕ) (hj0 : 0 < j) (hj : j < 2 * m) :
    liftB m a (4 * m + 2 * j + 1) + baselineGapB m (switchEdgeBNat m a (4 * m + 2 * j + 1)) =
      liftB m a (4 * m + 2 * j + 2) ∧
    liftB m a (4 * m + 2 * j + 2) + baselineGapB m (switchEdgeBNat m a (4 * m + 2 * j + 2)) =
      liftB m a (4 * m + 2 * j + 3) := by
  have hbefore : liftB m a (4 * m + 2 * j + 1) = middleB m j + clock m := by
    convert liftB_middle m hm a j hj0 using 1 <;> congr 1 <;> omega
  have hcenter : liftB m a (4 * m + 2 * j + 2) = lowerB m a.1 j + clock m := by
    convert liftB_lower m hm a j using 1 <;> congr 1 <;> omega
  have hafter : liftB m a (4 * m + 2 * j + 3) = middleB m (j + 1) + clock m := by
    convert liftB_middle m hm a (j + 1) (by omega) using 1 <;> congr 1 <;> omega
  rw [hbefore, hcenter, hafter, (switched_lower_B m a j hj0 hj).1, (switched_lower_B m a j hj0 hj).2]
  have hd := lowerB_distances m hm a.1 j hj0 hj
  omega

theorem B_upper_even_edges (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (r : ℕ) (hr : r + 1 < m) :
    liftB m a (4 * r + 4) + baselineGapB m (switchEdgeBNat m a (4 * r + 4)) = liftB m a (4 * r + 5) ∧
    liftB m a (4 * r + 5) + baselineGapB m (switchEdgeBNat m a (4 * r + 5)) = liftB m a (4 * r + 6) := by
  have hbefore : liftB m a (4 * r + 4) = fixedB m r := by
    convert (liftB_fixed m a r hr).1 using 1 <;> congr 1 <;> omega
  have hcenter : liftB m a (4 * r + 5) = upperB m a.2 (2 * r + 2) := by
    convert liftB_upper m a (2 * r + 2) (by omega) (by omega) using 1 <;> congr 1 <;> omega
  have hafter : liftB m a (4 * r + 6) = fixedB m r + height m - 1 := by
    convert (liftB_fixed m a r hr).2 using 1 <;> congr 1 <;> omega
  rw [hbefore, hcenter, hafter]
  have hi : 4 * r + 4 = 2 * (2 * r + 2) := by omega
  have ho : 4 * r + 5 = 2 * (2 * r + 2) + 1 := by omega
  rw [hi, ho, (switched_upper_B m a (2 * r + 2) (by omega) (by omega)).1,
    (switched_upper_B m a (2 * r + 2) (by omega) (by omega)).2]
  exact upperB_even_distances m hm a.2 r hr

theorem B_upper_odd_edges (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (r : ℕ) (hr : r + 2 < m) :
    liftB m a (4 * r + 6) + baselineGapB m (switchEdgeBNat m a (4 * r + 6)) = liftB m a (4 * r + 7) ∧
    liftB m a (4 * r + 7) + baselineGapB m (switchEdgeBNat m a (4 * r + 7)) = liftB m a (4 * r + 8) := by
  have hbefore : liftB m a (4 * r + 6) = fixedB m r + height m - 1 := by
    convert (liftB_fixed m a r (by omega)).2 using 1 <;> congr 1 <;> omega
  have hcenter : liftB m a (4 * r + 7) = upperB m a.2 (2 * r + 3) := by
    convert liftB_upper m a (2 * r + 3) (by omega) (by omega) using 1 <;> congr 1 <;> omega
  have hafter : liftB m a (4 * r + 8) = fixedB m (r + 1) := by
    convert (liftB_fixed m a (r + 1) (by omega)).1 using 1 <;> congr 1 <;> omega
  rw [hbefore, hcenter, hafter]
  have hi : 4 * r + 6 = 2 * (2 * r + 3) := by omega
  have ho : 4 * r + 7 = 2 * (2 * r + 3) + 1 := by omega
  rw [hi, ho, (switched_upper_B m a (2 * r + 3) (by omega) (by omega)).1,
    (switched_upper_B m a (2 * r + 3) (by omega) (by omega)).2]
  exact upperB_odd_distances m hm a.2 r hr

set_option maxHeartbeats 1000000 in
/-- The C-start D7 lift visits exactly the literal B site set after physical
reduction. No row validity is assumed in this representation theorem. -/
theorem liftB_image_mod (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    (Finset.range (order m)).image (fun i => liftB m a i % clock m) = rowB m a := by
  have hmod (x : ℕ) (hx : x ∈ rowB m a) : x % clock m = x :=
    Nat.mod_eq_of_lt (rowB_bounded m hm a x hx)
  have hmod' (x : ℕ) (hx : x ∈ rowB m a) : (x + clock m) % clock m = x := by
    simpa using hmod x hx
  have hC : (height m) ^ 2 - 1 ∈ rowB m a := by rw [rowB_mem_iff]; aesop
  have hSquare : (height m) ^ 2 ∈ rowB m a := by rw [rowB_mem_iff]; aesop
  have hM : clock m - 1 ∈ rowB m a := by rw [rowB_mem_iff]; aesop
  have hlo (j : ℕ) (hj : j < halfHeight m) : lowerB m a.1 j ∈ rowB m a := by rw [rowB_mem_iff]; aesop
  have hmi (j : ℕ) (hj0 : 1 ≤ j) (hj : j < halfHeight m) : middleB m j ∈ rowB m a := by rw [rowB_mem_iff]; aesop
  have hup (j : ℕ) (hj : j < halfHeight m) : upperB m a.2 j ∈ rowB m a := by rw [rowB_mem_iff]; aesop
  have hfi (r : ℕ) (hr : r < m - 1) : fixedB m r ∈ rowB m a ∧ fixedB m r + height m - 1 ∈ rowB m a := by
    constructor <;> rw [rowB_mem_iff] <;> aesop
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hib : i < 8 * m + 3 := by simpa [order] using Finset.mem_range.mp hi
    by_cases hi0 : i = 0
    · subst i; rw [(liftB_endpoints m hm a).1, hmod _ hC]; exact hC
    by_cases hi1 : i = 1
    · subst i; rw [(liftB_endpoints m hm a).2.1, hmod _ hSquare]; exact hSquare
    by_cases hi2 : i = 2
    · subst i
      have hx := hup 0 (by unfold halfHeight; omega)
      rw [(liftB_endpoints m hm a).2.2.1, hmod _ hx]; exact hx
    by_cases hil : i < 4 * m
    · by_cases hip : i % 2 = 1
      · have hj0 : 0 < (i - 1) / 2 := by omega
        have hj : (i - 1) / 2 < 2 * m := by omega
        have hlift : liftB m a i = upperB m a.2 ((i - 1) / 2) := by
          convert liftB_upper m a ((i - 1) / 2) hj0 hj using 1 <;> congr 1 <;> omega
        have hx := hup ((i - 1) / 2) (by unfold halfHeight; omega)
        rw [hlift, hmod _ hx]; exact hx
      · by_cases hip4 : i % 4 = 0
        · have hr : (i - 4) / 4 + 1 < m := by omega
          have hlift : liftB m a i = fixedB m ((i - 4) / 4) := by
            convert (liftB_fixed m a ((i - 4) / 4) hr).1 using 1 <;> congr 1 <;> omega
          have hx := (hfi ((i - 4) / 4) (by omega)).1
          rw [hlift, hmod _ hx]; exact hx
        · have hr : (i - 6) / 4 + 1 < m := by omega
          have hlift : liftB m a i = fixedB m ((i - 6) / 4) + height m - 1 := by
            convert (liftB_fixed m a ((i - 6) / 4) hr).2 using 1 <;> congr 1 <;> omega
          have hx := (hfi ((i - 6) / 4) (by omega)).2
          rw [hlift, hmod _ hx]; exact hx
    by_cases hi4 : i = 4 * m
    · subst i
      have hx := hup (2 * m) (by unfold halfHeight; omega)
      rw [(liftB_endpoints m hm a).2.2.2.1, hmod _ hx]; exact hx
    by_cases hi41 : i = 4 * m + 1
    · subst i; rw [(liftB_endpoints m hm a).2.2.2.2, hmod _ hM]; exact hM
    let q := i - (4 * m + 2)
    by_cases hip : q % 2 = 0
    · have hlift : liftB m a i = lowerB m a.1 (q / 2) + clock m := by
        convert liftB_lower m hm a (q / 2) using 1 <;> congr 1 <;> dsimp [q] at * <;> omega
      have hx := hlo (q / 2) (by unfold halfHeight; dsimp [q]; omega)
      rw [hlift, hmod' _ hx]; exact hx
    · have hj0 : 0 < (q + 1) / 2 := by omega
      have hlift : liftB m a i = middleB m ((q + 1) / 2) + clock m := by
        convert liftB_middle m hm a ((q + 1) / 2) hj0 using 1 <;> congr 1 <;> dsimp [q] at * <;> omega
      have hx := hmi ((q + 1) / 2) (by omega) (by unfold halfHeight; dsimp [q]; omega)
      rw [hlift, hmod' _ hx]; exact hx
  · intro hx
    have hxb := rowB_bounded m hm a x hx
    rcases (rowB_mem_iff m a x).mp hx with hx | hx | hx | ⟨j, hj, hx⟩ | ⟨j, hj0, hj, hx⟩ | ⟨j, hj, hx⟩ | ⟨r, hr, hx⟩
    · refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by unfold order; omega), ?_⟩
      rw [(liftB_endpoints m hm a).1, ← hx, Nat.mod_eq_of_lt hxb]
    · refine Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by unfold order; omega), ?_⟩
      rw [(liftB_endpoints m hm a).2.1, ← hx, Nat.mod_eq_of_lt hxb]
    · refine Finset.mem_image.mpr ⟨4 * m + 1, Finset.mem_range.mpr (by unfold order; omega), ?_⟩
      rw [(liftB_endpoints m hm a).2.2.2.2, ← hx, Nat.mod_eq_of_lt hxb]
    · refine Finset.mem_image.mpr ⟨4 * m + 2 + 2 * j,
        Finset.mem_range.mpr (by unfold order halfHeight at *; omega), ?_⟩
      rw [liftB_lower m hm a j, hx]
      simpa using Nat.mod_eq_of_lt hxb
    · refine Finset.mem_image.mpr ⟨4 * m + 1 + 2 * j,
        Finset.mem_range.mpr (by unfold order halfHeight at *; omega), ?_⟩
      rw [liftB_middle m hm a j (by omega), hx]
      simpa using Nat.mod_eq_of_lt hxb
    · by_cases hj0 : j = 0
      · subst j
        refine Finset.mem_image.mpr ⟨2, Finset.mem_range.mpr (by unfold order; omega), ?_⟩
        rw [(liftB_endpoints m hm a).2.2.1, hx]
        exact Nat.mod_eq_of_lt hxb
      · by_cases hjlast : j = 2 * m
        · subst j
          refine Finset.mem_image.mpr ⟨4 * m, Finset.mem_range.mpr (by unfold order; omega), ?_⟩
          rw [(liftB_endpoints m hm a).2.2.2.1, hx]
          exact Nat.mod_eq_of_lt hxb
        · refine Finset.mem_image.mpr ⟨2 * j + 1,
            Finset.mem_range.mpr (by unfold order halfHeight at *; omega), ?_⟩
          rw [liftB_upper m a j (by omega) (by unfold halfHeight at hj; omega), hx]
          exact Nat.mod_eq_of_lt hxb
    · rcases hx with hx | hx
      · refine Finset.mem_image.mpr ⟨4 + 4 * r, Finset.mem_range.mpr (by unfold order; omega), ?_⟩
        rw [(liftB_fixed m a r (by omega)).1, ← hx, hmod _ (by rw [hx]; exact (hfi r hr).1)]
      · refine Finset.mem_image.mpr ⟨6 + 4 * r, Finset.mem_range.mpr (by unfold order; omega), ?_⟩
        rw [(liftB_fixed m a r (by omega)).2, ← hx, hmod _ (by rw [hx]; exact (hfi r hr).2)]

theorem B_fixed_edges (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    liftB m a 0 + baselineGapB m (switchEdgeBNat m a 0) = liftB m a 1 ∧
    liftB m a 1 + baselineGapB m (switchEdgeBNat m a 1) = liftB m a 2 ∧
    liftB m a 2 + baselineGapB m (switchEdgeBNat m a 2) = liftB m a 3 ∧
    liftB m a (4 * m - 1) + baselineGapB m (switchEdgeBNat m a (4 * m - 1)) = liftB m a (4 * m) ∧
    liftB m a (4 * m) + baselineGapB m (switchEdgeBNat m a (4 * m)) = liftB m a (4 * m + 1) ∧
    liftB m a (4 * m + 1) + baselineGapB m (switchEdgeBNat m a (4 * m + 1)) = liftB m a (4 * m + 2) ∧
    liftB m a (4 * m + 2) + baselineGapB m (switchEdgeBNat m a (4 * m + 2)) = liftB m a (4 * m + 3) ∧
    liftB m a (8 * m + 1) + baselineGapB m (switchEdgeBNat m a (8 * m + 1)) = liftB m a (8 * m + 2) ∧
    liftB m a (8 * m + 2) + baselineGapB m (switchEdgeBNat m a (8 * m + 2)) =
      (height m) ^ 2 - 1 + clock m := by
  have hbefore : liftB m a (4 * m - 1) = upperB m a.2 (2 * m - 1) := by
    convert liftB_upper m a (2 * m - 1) (by omega) (by omega) using 1 <;> congr 1 <;> omega
  have h3 : liftB m a 3 = upperB m a.2 1 := by simpa using liftB_upper m a 1 (by omega) (by omega)
  have hlo0 : liftB m a (4 * m + 2) = lowerB m a.1 0 + clock m := by simpa using liftB_lower m hm a 0
  have hmi1 : liftB m a (4 * m + 3) = middleB m 1 + clock m := by
    convert liftB_middle m hm a 1 (by omega) using 1 <;> congr 1 <;> omega
  have hmilast : liftB m a (8 * m + 1) = middleB m (2 * m) + clock m := by
    convert liftB_middle m hm a (2 * m) (by omega) using 1 <;> congr 1 <;> omega
  have hlolast : liftB m a (8 * m + 2) = lowerB m a.1 (2 * m) + clock m := by
    convert liftB_lower m hm a (2 * m) using 1 <;> congr 1 <;> omega
  have hl := liftB_endpoints m hm a
  have hg := switched_B_fixed_gaps m hm a
  have hs := B_fixed_seams m hm a
  rw [hbefore, h3, hlo0, hmi1, hmilast, hlolast,
    hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2,
    hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1,
    hg.2.2.2.2.2.1, hg.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.2]
  omega

theorem B_extra_edges (m : ℕ) (hm : 2 ≤ m) (a : Choices m) :
    liftB m a 3 + baselineGapB m (switchEdgeBNat m a 3) = liftB m a 4 ∧
    liftB m a (4 * m - 2) + baselineGapB m (switchEdgeBNat m a (4 * m - 2)) = liftB m a (4 * m - 1) := by
  have h3 : liftB m a 3 = upperB m a.2 1 := by simpa using liftB_upper m a 1 (by omega) (by omega)
  have h4 : liftB m a 4 = fixedB m 0 := by simpa using (liftB_fixed m a 0 (by omega)).1
  have hprev : liftB m a (4 * m - 2) = fixedB m (m - 2) + height m - 1 := by
    convert (liftB_fixed m a (m - 2) (by omega)).2 using 1 <;> congr 1 <;> omega
  have hlast : liftB m a (4 * m - 1) = upperB m a.2 (2 * m - 1) := by
    convert liftB_upper m a (2 * m - 1) (by omega) (by omega) using 1 <;> congr 1 <;> omega
  rw [h3, h4, hprev, hlast, (switched_B_extra_gaps m hm a).1, (switched_B_extra_gaps m hm a).2]
  exact B_extra_upper_seams m hm a

theorem liftB_succ (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (i : ℕ)
    (hi : i + 1 < order m) :
    liftB m a i + baselineGapB m (switchEdgeBNat m a i) = liftB m a (i + 1) := by
  have hf := B_fixed_edges m hm a
  by_cases h0 : i = 0
  · simpa [h0] using hf.1
  by_cases h1 : i = 1
  · simpa [h1] using hf.2.1
  by_cases h2 : i = 2
  · simpa [h2] using hf.2.2.1
  by_cases h4p : i = 4 * m - 1
  · have he : 4 * m - 1 + 1 = 4 * m := by omega
    simpa only [h4p, he] using hf.2.2.2.1
  by_cases h4 : i = 4 * m
  · simpa [h4] using hf.2.2.2.2.1
  by_cases h41 : i = 4 * m + 1
  · simpa [h41, Nat.add_assoc] using hf.2.2.2.2.2.1
  by_cases h42 : i = 4 * m + 2
  · simpa [h42, Nat.add_assoc] using hf.2.2.2.2.2.2.1
  by_cases h81 : i = 8 * m + 1
  · simpa [h81, Nat.add_assoc] using hf.2.2.2.2.2.2.2.1
  by_cases h3 : i = 3
  · have hm2 : 2 ≤ m := by omega
    simpa [h3] using (B_extra_edges m hm2 a).1
  by_cases h4pp : i = 4 * m - 2
  · have hm2 : 2 ≤ m := by omega
    have he : 4 * m - 2 + 1 = 4 * m - 1 := by omega
    simpa only [h4pp, he] using (B_extra_edges m hm2 a).2
  by_cases hl : i < 4 * m
  · let q := i - 4
    have hil : 4 ≤ i := by omega
    have hih : i ≤ 4 * m - 3 := by omega
    by_cases hp : q % 4 = 0 ∨ q % 4 = 1
    · have hr : q / 4 + 1 < m := by dsimp [q]; omega
      have he := B_upper_even_edges m hm a (q / 4) hr
      rcases hp with hp | hp
      · have heq : 4 * (q / 4) + 4 = i := by dsimp [q] at *; omega
        have heq' : 4 * (q / 4) + 5 = i + 1 := by omega
        simpa only [heq, heq'] using he.1
      · have heq : 4 * (q / 4) + 5 = i := by dsimp [q] at *; omega
        have heq' : 4 * (q / 4) + 6 = i + 1 := by omega
        simpa only [heq, heq'] using he.2
    · have hr : q / 4 + 2 < m := by dsimp [q] at *; omega
      have he := B_upper_odd_edges m hm a (q / 4) hr
      by_cases hp' : q % 4 = 2
      · have heq : 4 * (q / 4) + 6 = i := by dsimp [q] at *; omega
        have heq' : 4 * (q / 4) + 7 = i + 1 := by omega
        simpa only [heq, heq'] using he.1
      · have heq : 4 * (q / 4) + 7 = i := by dsimp [q] at *; omega
        have heq' : 4 * (q / 4) + 8 = i + 1 := by omega
        simpa only [heq, heq'] using he.2
  · let q := i - (4 * m + 1)
    have hj0 : 0 < q / 2 := by dsimp [q]; omega
    have hj : q / 2 < 2 * m := by unfold order at hi; dsimp [q]; omega
    have he := B_lower_edges m hm a (q / 2) hj0 hj
    by_cases hp : q % 2 = 0
    · have heq : 4 * m + 2 * (q / 2) + 1 = i := by dsimp [q] at *; omega
      have heq' : 4 * m + 2 * (q / 2) + 2 = i + 1 := by omega
      simpa only [heq, heq'] using he.1
    · have heq : 4 * m + 2 * (q / 2) + 2 = i := by dsimp [q] at *; omega
      have heq' : 4 * m + 2 * (q / 2) + 3 = i + 1 := by omega
      simpa only [heq, heq'] using he.2

theorem switchedWordB_length (m : ℕ) (a : Choices m) :
    (switchedWordB m a).length = order m := by simp [switchedWordB]

theorem liftB_eq_prefix (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (i : ℕ) (hi : i < order m) :
    (height m) ^ 2 - 1 + ((switchedWordB m a).take i).sum = liftB m a i := by
  induction i with
  | zero => simpa using (liftB_endpoints m hm a).1.symm
  | succ i ih =>
    have hi' : i < order m := by omega
    have hlen : i < (switchedWordB m a).length := by rw [switchedWordB_length]; exact hi'
    have hget : (switchedWordB m a)[i]'hlen = baselineGapB m (switchEdgeBNat m a i) := by
      simp [switchedWordB, switchEdgeB]
    rw [List.sum_take_succ _ _ hlen, ← Nat.add_assoc, ih hi', hget]
    exact liftB_succ m hm a i hi

theorem switchedWordB_sum (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    (switchedWordB m a).sum = clock m := by
  rw [(switchedWordB_perm m hm a).sum_eq, fullGapList_sum, optimal_width]

theorem rowB_eq_shifted_prefixes (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    (properPrefixSites (switchedWordB m a)).toFinset.image
      (fun p => (p + ((height m) ^ 2 - 1)) % clock m) = rowB m a := by
  rw [← liftB_image_mod m hm a]
  ext x
  simp only [Finset.mem_image, List.mem_toFinset, mem_properPrefixSites_iff,
    switchedWordB_length, Finset.mem_range]
  constructor
  · rintro ⟨p, ⟨i, hi, hpi⟩, hpx⟩
    refine ⟨i, hi, ?_⟩
    have hL : liftB m a i = (height m) ^ 2 - 1 + p := by
      rw [← hpi]
      exact (liftB_eq_prefix m hm a i hi).symm
    simpa [hL, Nat.add_comm] using hpx
  · rintro ⟨i, hi, hx⟩
    refine ⟨((switchedWordB m a).take i).sum, ⟨i, hi, rfl⟩, ?_⟩
    have hL := liftB_eq_prefix m hm a i hi
    simpa [Nat.add_comm] using (congrArg (fun t => t % clock m) hL).trans hx

/-- Full validity of the literal second row D5/D7, with the physical wrap
proved through its real C-start one-winding prefix representation. -/
theorem rowB_gap_inventory (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    finiteCyclicGapInventory (clock m) (rowB m a) =
      Multiset.ofList (fullGapList (order m)) := by
  have hpos : ∀ x ∈ switchedWordB m a, 0 < x := by
    intro x hx
    exact ((fullGapList_mem _ _).mp ((switchedWordB_perm m hm a).mem_iff.mp hx)).1
  have hbound : ∀ p ∈ (properPrefixSites (switchedWordB m a)).toFinset, p < clock m := by
    intro p hp
    simpa [switchedWordB_sum m hm a] using properPrefixSites_lt_sum _ hpos p (List.mem_toFinset.mp hp)
  have hM : 0 < clock m := by unfold clock height order; positivity
  have hne : switchedWordB m a ≠ [] := by
    intro h
    have hlen := switchedWordB_length m a
    simp [h, order] at hlen
  rw [← rowB_eq_shifted_prefixes m hm a,
    finite_set_cyclic_gap_rotate _ _ _ hM hbound, ← switchedWordB_sum m hm a]
  cases hw : switchedWordB m a with
  | nil => exact False.elim (hne hw)
  | cons x xs =>
    have hpos' : ∀ z ∈ x :: xs, 0 < z := by simpa [hw] using hpos
    rw [properPrefixSites_finite_gaps x xs hpos']
    exact Multiset.coe_eq_coe.mpr (by simpa [hw] using switchedWordB_perm m hm a)

end CorralFormalization.EvenSwitches
