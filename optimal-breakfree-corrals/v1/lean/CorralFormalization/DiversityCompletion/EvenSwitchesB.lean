import CorralFormalization.DiversityCompletion.EvenSwitches

namespace CorralFormalization.EvenSwitches

theorem complementary_lower_pair (m : ℕ) (a : Fin m → Bool) (j : ℕ) :
    ({lowerA m a j, lowerB m a j} : Finset ℕ) =
      {(2 * j + 1) * (height m - 1), (2 * j + 2) * (height m - 1)} := by
  have hb := eta_le_one m a j
  by_cases h : eta m a j = 0
  · simp [lowerA, lowerB, h]
  · have h' : eta m a j = 1 := by omega
    have hs : 2 * j + 2 - 1 = 2 * j + 1 := by omega
    simp [lowerA, lowerB, h', hs, Finset.pair_comm]

theorem complementary_upper_pair (m : ℕ) (a : Fin (m - 1) → Bool) (j : ℕ) :
    ({upperA m a j, upperB m a j} : Finset ℕ) =
      {(height m + 2 + 2 * j) * (height m - 1),
       (height m + 2 + 2 * j) * (height m - 1) + 1} := by
  have hb := epsilon_le_one m a j
  by_cases h : epsilon m a j = 0
  · simp [upperA, upperB, h]
  · have h' : epsilon m a j = 1 := by omega
    simp [upperA, upperB, h', Finset.pair_comm]

theorem lowerB_distances (m : ℕ) (hm : 1 ≤ m) (a : Fin m → Bool)
    (j : ℕ) (hj0 : 0 < j) (hj : j < 2 * m) :
    middleB m j + lowInB m (eta m a j) j = lowerB m a j ∧
    lowerB m a j + lowOutB m (eta m a j) j = middleB m (j + 1) := by
  have hb := eta_le_one m a j
  have hheight : height m - 1 = 4 * m + 1 := by unfold height; omega
  have hmulb : (4 * m + 1) * eta m a j ≤ 4 * m + 1 := by
    simpa using Nat.mul_le_mul_left (4 * m + 1) hb
  have hcoef := Nat.sub_add_cancel (show eta m a j ≤ 2 * j + 2 by omega)
  have hcoefmul := congrArg (fun x => (4 * m + 1) * x) hcoef
  have hd : 1 - j % 2 ≤ 2 * height m * j := by
    have hprod := Nat.le_mul_of_pos_left j (by unfold height; omega : 0 < 2 * height m)
    omega
  have hd' : 1 - (j + 1) % 2 ≤ 2 * height m * (j + 1) := by
    have hprod := Nat.le_mul_of_pos_left (j + 1) (by unfold height; omega : 0 < 2 * height m)
    omega
  have hsub := Nat.sub_add_cancel hd
  have hsub' := Nat.sub_add_cancel hd'
  have hin : lowInB m (eta m a j) j + 2 * j + j % 2 + (4 * m + 1) * eta m a j = 8 * m + 3 := by
    unfold lowInB
    omega
  have hout : 2 * j + 2 - j % 2 + j % 2 = 2 * j + 2 := by omega
  have hpar : (j + 1) % 2 + j % 2 = 1 := by omega
  have hδ : 1 - j % 2 + j % 2 = 1 := by omega
  have hδ' : 1 - (j + 1) % 2 + (j + 1) % 2 = 1 := by omega
  unfold lowerB lowOutB
  rw [hheight]
  constructor <;> simp only [middleB] at * <;> unfold height at * <;> nlinarith

theorem upperB_even_distances (m : ℕ) (hm : 1 ≤ m) (a : Fin (m - 1) → Bool)
    (r : ℕ) (hr : r + 1 < m) :
    fixedB m r + upInB m (epsilon m a (2 * r + 2)) (2 * r + 2) = upperB m a (2 * r + 2) ∧
    upperB m a (2 * r + 2) + upOutB m (epsilon m a (2 * r + 2)) (2 * r + 2) =
      fixedB m r + height m - 1 := by
  have hb := epsilon_le_one m a (2 * r + 2)
  have hp : (2 * r + 2) % 2 = 0 := by omega
  have hheight : height m - 1 = 4 * m + 1 := by unfold height; omega
  have hi : upInB m (epsilon m a (2 * r + 2)) (2 * r + 2) + 2 * (2 * r + 2) + epsilon m a (2 * r + 2) = 4 * m + 1 := by
    simp only [upInB, if_pos hp]
    omega
  have hs := Nat.sub_add_cancel
    (show epsilon m a (2 * r + 2) ≤ (height m + 2 + 2 * (2 * r + 2)) * (height m - 1) + 1 by omega)
  have hw := Nat.sub_add_cancel (show 1 ≤ fixedB m r + height m by unfold height; omega)
  unfold upperB fixedB upOutB at *
  rw [hheight]
  simp only [hheight] at hs
  simp only [if_pos hp] at *
  unfold height halfHeight at *
  constructor <;> nlinarith

theorem upperB_odd_distances (m : ℕ) (hm : 1 ≤ m) (a : Fin (m - 1) → Bool)
    (r : ℕ) (hr : r + 2 < m) :
    (fixedB m r + height m - 1) + upInB m (epsilon m a (2 * r + 3)) (2 * r + 3) =
      upperB m a (2 * r + 3) ∧
    upperB m a (2 * r + 3) + upOutB m (epsilon m a (2 * r + 3)) (2 * r + 3) =
      fixedB m (r + 1) := by
  have hb := epsilon_le_one m a (2 * r + 3)
  have hp : (2 * r + 3) % 2 ≠ 0 := by omega
  have hheight : height m - 1 = 4 * m + 1 := by unfold height; omega
  have hi : upInB m (epsilon m a (2 * r + 3)) (2 * r + 3) + 2 * (2 * r + 3) + epsilon m a (2 * r + 3) = 8 * m + 4 := by
    simp only [upInB, if_neg hp]
    omega
  have hs := Nat.sub_add_cancel
    (show epsilon m a (2 * r + 3) ≤ (height m + 2 + 2 * (2 * r + 3)) * (height m - 1) + 1 by omega)
  have hw := Nat.sub_add_cancel (show 1 ≤ fixedB m r + height m by unfold height; omega)
  unfold upperB fixedB upOutB at *
  rw [hheight]
  simp only [hheight] at hs
  simp only [if_neg hp] at *
  unfold height halfHeight at *
  constructor <;> nlinarith

/-- Literal second-row coordinates in the support decomposition (D5)-(D7).
The equality with U\A is a further support identity, not an assumption. -/
def rowB (m : ℕ) (a : Choices m) : Finset ℕ :=
  {(height m) ^ 2 - 1, (height m) ^ 2, clock m - 1} ∪
    (Finset.range (halfHeight m)).image (lowerB m a.1) ∪
    (Finset.Ico 1 (halfHeight m)).image (middleB m) ∪
    (Finset.range (halfHeight m)).image (upperB m a.2) ∪
    (Finset.range (m - 1)).biUnion (fun r => {fixedB m r, fixedB m r + height m - 1})

theorem rowB_mem_iff (m : ℕ) (a : Choices m) (x : ℕ) :
    x ∈ rowB m a ↔ x = (height m) ^ 2 - 1 ∨ x = (height m) ^ 2 ∨ x = clock m - 1 ∨
      (∃ j, j < halfHeight m ∧ lowerB m a.1 j = x) ∨
      (∃ j, 1 ≤ j ∧ j < halfHeight m ∧ middleB m j = x) ∨
      (∃ j, j < halfHeight m ∧ upperB m a.2 j = x) ∨
      (∃ r, r < m - 1 ∧ (x = fixedB m r ∨ x = fixedB m r + height m - 1)) := by
  simp only [rowB, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert, Finset.mem_image,
    Finset.mem_range, Finset.mem_Ico, Finset.mem_biUnion]
  aesop

theorem rowB_bounded (m : ℕ) (hm : 1 ≤ m) (a : Choices m)
    (x : ℕ) (hx : x ∈ rowB m a) : x < clock m := by
  have hheight : height m - 1 = 4 * m + 1 := by unfold height; omega
  have hM : 0 < clock m := by unfold clock height order; positivity
  have hsquare : (height m) ^ 2 < clock m := by unfold clock height order; nlinarith
  have hlowmax : height m * (height m - 1) < clock m := by
    rw [hheight]; unfold clock height order; nlinarith
  have hupmax : 2 * height m * (height m - 1) + 1 < clock m := by
    rw [hheight]; unfold clock height order; nlinarith
  rcases (rowB_mem_iff m a x).mp hx with hx | hx | hx | ⟨j, hj, hx⟩ | ⟨j, hj0, hj, hx⟩ | ⟨j, hj, hx⟩ | ⟨r, hr, hx⟩
  · omega
  · omega
  · omega
  · have hcoef : 2 * j + 2 - eta m a.1 j ≤ height m := by unfold halfHeight height at *; omega
    have hmul := Nat.mul_le_mul_right (height m - 1) hcoef
    unfold lowerB at hx
    omega
  · have hj' : j ≤ 2 * m := by unfold halfHeight at hj; omega
    have hmul := Nat.mul_le_mul_left (2 * height m) hj'
    have hmax : 2 * height m * (2 * m) < clock m := by unfold clock height order; nlinarith
    have hs : middleB m j ≤ 2 * height m * j := Nat.sub_le _ _
    omega
  · have hcoef : height m + 2 + 2 * j ≤ 2 * height m := by unfold halfHeight height at *; omega
    have hmul := Nat.mul_le_mul_right (height m - 1) hcoef
    have hs : upperB m a.2 j ≤ (height m + 2 + 2 * j) * (height m - 1) + 1 := Nat.sub_le _ _
    omega
  · have hcoef : halfHeight m + 2 + 2 * r ≤ 4 * m - 1 := by unfold halfHeight; omega
    have hmul := Nat.mul_le_mul_left (2 * height m) hcoef
    have hmax : 2 * height m * (4 * m - 1) + height m < clock m := by
      have hs : 4 * m - 1 + 1 = 4 * m := by omega
      have hs' := congrArg (fun t => m * t) hs
      unfold clock height order
      nlinarith
    unfold fixedB at hx
    rcases hx with hx | hx <;> omega

def liftB (m : ℕ) (a : Choices m) (i : ℕ) : ℕ :=
  if i = 0 then (height m) ^ 2 - 1
  else if i = 1 then (height m) ^ 2
  else if i = 2 then upperB m a.2 0
  else if i < 4 * m then
    if i % 2 = 1 then upperB m a.2 ((i - 1) / 2)
    else if i % 4 = 0 then fixedB m ((i - 4) / 4)
    else fixedB m ((i - 6) / 4) + height m - 1
  else if i = 4 * m then upperB m a.2 (2 * m)
  else if i = 4 * m + 1 then clock m - 1
  else let q := i - (4 * m + 2)
    if q % 2 = 0 then lowerB m a.1 (q / 2) + clock m
    else middleB m ((q + 1) / 2) + clock m

/-- Complete baseline B word, starting at C as in §6.2, including the
physical wrap from M-1 to s_0 and the final return from s_(2m) to C. -/
def baselineGapB (m i : ℕ) : ℕ :=
  if i = 0 then 1
  else if i = 1 then 4 * m
  else if i = 2 then 8 * m + 3
  else if i < 4 * m - 1 then
    let q := i - 3
    if q % 4 = 0 then 4 * m + 5 + q
    else if q % 4 = 1 then 4 * m - 2 - q
    else if q % 4 = 2 then q + 2
    else 8 * m + 1 - q
  else if i = 4 * m - 1 then 8 * m + 1
  else if i = 4 * m then 4 * m + 1
  else if i = 4 * m + 1 then 4 * m + 2
  else if i = 8 * m + 2 then 8 * m + 2
  else if i = 4 * m + 2 then 4 * m + 3
  else if i = 8 * m + 1 then 2
  else if i % 2 = 0 then
    let j := (i - 4 * m) / 2
    2 * j - 1 + j % 2
  else let j := (i - (4 * m + 1)) / 2
    8 * m + 3 - 2 * j - j % 2

theorem baselineGapB_upper_formula (m i : ℕ) (hi : 3 ≤ i) (hi' : i < 4 * m - 1) :
    baselineGapB m i =
      (if (i - 3) % 4 = 0 then 4 * m + 5 + (i - 3)
      else if (i - 3) % 4 = 1 then 4 * m - 2 - (i - 3)
      else if (i - 3) % 4 = 2 then (i - 3) + 2 else 8 * m + 1 - (i - 3)) := by
  simp only [baselineGapB, if_neg (show i ≠ 0 by omega), if_neg (show i ≠ 1 by omega),
    if_neg (show i ≠ 2 by omega), if_pos hi']

theorem baselineGapB_large_formula (m i : ℕ) (hm : 1 ≤ m) (hi : 4 * m ≤ i) :
    baselineGapB m i =
      (if i = 4 * m then 4 * m + 1
      else if i = 4 * m + 1 then 4 * m + 2
      else if i = 8 * m + 2 then 8 * m + 2
      else if i = 4 * m + 2 then 4 * m + 3
      else if i = 8 * m + 1 then 2
      else if i % 2 = 0 then 2 * ((i - 4 * m) / 2) - 1 + ((i - 4 * m) / 2) % 2
      else 8 * m + 3 - 2 * ((i - (4 * m + 1)) / 2) - ((i - (4 * m + 1)) / 2) % 2) := by
  simp only [baselineGapB, if_neg (show i ≠ 0 by omega), if_neg (show i ≠ 1 by omega),
    if_neg (show i ≠ 2 by omega), if_neg (show ¬ i < 4 * m - 1 by omega),
    if_neg (show i ≠ 4 * m - 1 by omega)]

theorem baselineGapB_lower_formula (m i : ℕ) (hm : 1 ≤ m) (hi : 4 * m + 3 ≤ i) (hi' : i ≤ 8 * m) :
    baselineGapB m i =
      (if i % 2 = 0 then 2 * ((i - 4 * m) / 2) - 1 + ((i - 4 * m) / 2) % 2
      else 8 * m + 3 - 2 * ((i - (4 * m + 1)) / 2) - ((i - (4 * m + 1)) / 2) % 2) := by
  rw [baselineGapB_large_formula m i hm (by omega)]
  simp only [if_neg (show i ≠ 4 * m by omega), if_neg (show i ≠ 4 * m + 1 by omega),
    if_neg (show i ≠ 8 * m + 2 by omega), if_neg (show i ≠ 4 * m + 2 by omega),
    if_neg (show i ≠ 8 * m + 1 by omega)]

theorem baselineGapB_fixed (m : ℕ) (hm : 1 ≤ m) :
    baselineGapB m 0 = 1 ∧ baselineGapB m 1 = 4 * m ∧ baselineGapB m 2 = 8 * m + 3 ∧
    baselineGapB m (4 * m - 1) = 8 * m + 1 ∧ baselineGapB m (4 * m) = 4 * m + 1 ∧
    baselineGapB m (4 * m + 1) = 4 * m + 2 ∧ baselineGapB m (8 * m + 2) = 8 * m + 2 ∧
    baselineGapB m (4 * m + 2) = 4 * m + 3 ∧ baselineGapB m (8 * m + 1) = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [baselineGapB]
  · simp [baselineGapB]
  · simp [baselineGapB]
  · simp only [baselineGapB, if_neg (show 4 * m - 1 ≠ 0 by omega),
      if_neg (show 4 * m - 1 ≠ 1 by omega), if_neg (show 4 * m - 1 ≠ 2 by omega),
      if_neg (show ¬ 4 * m - 1 < 4 * m - 1 by omega), if_pos rfl, ↓reduceIte]
  · rw [baselineGapB_large_formula m _ hm (by omega)]
    simp
  · rw [baselineGapB_large_formula m _ hm (by omega)]
    simp only [if_neg (show 4 * m + 1 ≠ 4 * m by omega), if_pos rfl, ↓reduceIte]
  · rw [baselineGapB_large_formula m _ hm (by omega)]
    simp only [if_neg (show 8 * m + 2 ≠ 4 * m by omega),
      if_neg (show 8 * m + 2 ≠ 4 * m + 1 by omega), if_pos rfl, ↓reduceIte]
  · rw [baselineGapB_large_formula m _ hm (by omega)]
    simp only [if_neg (show 4 * m + 2 ≠ 4 * m by omega),
      if_neg (show 4 * m + 2 ≠ 4 * m + 1 by omega),
      if_neg (show 4 * m + 2 ≠ 8 * m + 2 by omega), if_pos rfl, ↓reduceIte]
  · rw [baselineGapB_large_formula m _ hm (by omega)]
    simp only [if_neg (show 8 * m + 1 ≠ 4 * m by omega),
      if_neg (show 8 * m + 1 ≠ 4 * m + 1 by omega),
      if_neg (show 8 * m + 1 ≠ 8 * m + 2 by omega),
      if_neg (show 8 * m + 1 ≠ 4 * m + 2 by omega), if_pos rfl, ↓reduceIte]

/-- Explicit inverse position of each palette label in the printed B word. -/
def labelIndexB (m x : ℕ) : ℕ :=
  if x = 1 then 0
  else if x = 2 then 8 * m + 1
  else if x = 4 * m then 1
  else if x = 4 * m + 1 then 4 * m
  else if x = 4 * m + 2 then 4 * m + 1
  else if x = 4 * m + 3 then 4 * m + 2
  else if x = 8 * m + 1 then 4 * m - 1
  else if x = 8 * m + 2 then 8 * m + 2
  else if x = 8 * m + 3 then 2
  else if x % 4 = 0 then
    if x < 4 * m then x + 1 else 12 * m + 3 - x
  else if x % 4 = 1 then
    if x < 4 * m + 1 then 4 * m + 1 - x else x - (4 * m + 2)
  else if x % 4 = 2 then
    if x < 4 * m + 2 then 4 * m + x else 8 * m + 4 - x
  else if x < 4 * m + 3 then 4 * m + x + 1 else 12 * m + 4 - x

theorem labelIndexB_bound (m x : ℕ) (hm : 1 ≤ m) (hx : 0 < x ∧ x ≤ order m) :
    labelIndexB m x < order m := by
  unfold labelIndexB order at *
  by_cases h0 : x = 1
  · rw [if_pos h0]
    omega
  · rw [if_neg h0]
    by_cases h1 : x = 2
    · rw [if_pos h1]
      omega
    · rw [if_neg h1]
      by_cases h2 : x = 4 * m
      · rw [if_pos h2]
        omega
      · rw [if_neg h2]
        by_cases h3 : x = 4 * m + 1
        · rw [if_pos h3]
          omega
        · rw [if_neg h3]
          by_cases h4 : x = 4 * m + 2
          · rw [if_pos h4]
            omega
          · rw [if_neg h4]
            by_cases h5 : x = 4 * m + 3
            · rw [if_pos h5]
              omega
            · rw [if_neg h5]
              by_cases h6 : x = 8 * m + 1
              · rw [if_pos h6]
                omega
              · rw [if_neg h6]
                by_cases h7 : x = 8 * m + 2
                · rw [if_pos h7]
                  omega
                · rw [if_neg h7]
                  by_cases h8 : x = 8 * m + 3
                  · rw [if_pos h8]
                    omega
                  · rw [if_neg h8]
                    by_cases hR0 : x % 4 = 0
                    · rw [if_pos hR0]
                      by_cases hL0 : x < 4 * m
                      · rw [if_pos hL0]
                        omega
                      · rw [if_neg hL0]
                        omega
                    · rw [if_neg hR0]
                      by_cases hR1 : x % 4 = 1
                      · rw [if_pos hR1]
                        by_cases hL1 : x < 4 * m + 1
                        · rw [if_pos hL1]
                          omega
                        · rw [if_neg hL1]
                          omega
                      · rw [if_neg hR1]
                        by_cases hR2 : x % 4 = 2
                        · rw [if_pos hR2]
                          by_cases hL2 : x < 4 * m + 2
                          · rw [if_pos hL2]
                            omega
                          · rw [if_neg hL2]
                            omega
                        · rw [if_neg hR2]
                          by_cases hL3 : x < 4 * m + 3
                          · rw [if_pos hL3]
                            omega
                          · rw [if_neg hL3]
                            omega

set_option maxHeartbeats 1000000 in
theorem labelIndexB_value (m x : ℕ) (hm : 1 ≤ m) (hx : 0 < x ∧ x ≤ order m) :
    baselineGapB m (labelIndexB m x) = x := by
  have hf := baselineGapB_fixed m hm
  unfold order at hx
  unfold labelIndexB
  by_cases h0 : x = 1
  · rw [if_pos h0]
    exact hf.1.trans h0.symm
  · rw [if_neg h0]
    by_cases h1 : x = 2
    · rw [if_pos h1]
      exact hf.2.2.2.2.2.2.2.2.trans h1.symm
    · rw [if_neg h1]
      by_cases h2 : x = 4 * m
      · rw [if_pos h2]
        exact hf.2.1.trans h2.symm
      · rw [if_neg h2]
        by_cases h3 : x = 4 * m + 1
        · rw [if_pos h3]
          exact hf.2.2.2.2.1.trans h3.symm
        · rw [if_neg h3]
          by_cases h4 : x = 4 * m + 2
          · rw [if_pos h4]
            exact hf.2.2.2.2.2.1.trans h4.symm
          · rw [if_neg h4]
            by_cases h5 : x = 4 * m + 3
            · rw [if_pos h5]
              exact hf.2.2.2.2.2.2.2.1.trans h5.symm
            · rw [if_neg h5]
              by_cases h6 : x = 8 * m + 1
              · rw [if_pos h6]
                exact hf.2.2.2.1.trans h6.symm
              · rw [if_neg h6]
                by_cases h7 : x = 8 * m + 2
                · rw [if_pos h7]
                  exact hf.2.2.2.2.2.2.1.trans h7.symm
                · rw [if_neg h7]
                  by_cases h8 : x = 8 * m + 3
                  · rw [if_pos h8]
                    exact hf.2.2.1.trans h8.symm
                  · rw [if_neg h8]
                    by_cases hR0 : x % 4 = 0
                    · rw [if_pos hR0]
                      by_cases hL0 : x < 4 * m
                      · rw [if_pos hL0]
                        rw [baselineGapB_upper_formula m _ (by omega) (by omega)]
                        split_ifs <;> omega
                      · rw [if_neg hL0]
                        rw [baselineGapB_lower_formula m _ hm (by omega) (by omega)]
                        split_ifs <;> omega
                    · rw [if_neg hR0]
                      by_cases hR1 : x % 4 = 1
                      · rw [if_pos hR1]
                        by_cases hL1 : x < 4 * m + 1
                        · rw [if_pos hL1]
                          rw [baselineGapB_upper_formula m _ (by omega) (by omega)]
                          split_ifs <;> omega
                        · rw [if_neg hL1]
                          rw [baselineGapB_upper_formula m _ (by omega) (by omega)]
                          split_ifs <;> omega
                      · rw [if_neg hR1]
                        by_cases hR2 : x % 4 = 2
                        · rw [if_pos hR2]
                          by_cases hL2 : x < 4 * m + 2
                          · rw [if_pos hL2]
                            rw [baselineGapB_lower_formula m _ hm (by omega) (by omega)]
                            split_ifs <;> omega
                          · rw [if_neg hL2]
                            rw [baselineGapB_upper_formula m _ (by omega) (by omega)]
                            split_ifs <;> omega
                        · rw [if_neg hR2]
                          by_cases hL3 : x < 4 * m + 3
                          · rw [if_pos hL3]
                            rw [baselineGapB_lower_formula m _ hm (by omega) (by omega)]
                            split_ifs <;> omega
                          · rw [if_neg hL3]
                            rw [baselineGapB_lower_formula m _ hm (by omega) (by omega)]
                            split_ifs <;> omega

def labelPositionB (m : ℕ) (hm : 1 ≤ m) (i : Fin (order m)) : Fin (order m) :=
  ⟨labelIndexB m (i.val + 1), labelIndexB_bound m _ hm (by have := i.isLt; omega)⟩

theorem labelPositionB_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (labelPositionB m hm) := by
  intro i j hij
  have hv := congrArg (fun t : Fin (order m) => baselineGapB m t.val) hij
  change baselineGapB m (labelIndexB m (i.val + 1)) =
    baselineGapB m (labelIndexB m (j.val + 1)) at hv
  rw [labelIndexB_value m _ hm (by have := i.isLt; omega),
    labelIndexB_value m _ hm (by have := j.isLt; omega)] at hv
  apply Fin.ext
  omega

theorem baselineGapB_range (m i : ℕ) (hm : 1 ≤ m) (hi : i < order m) :
    0 < baselineGapB m i ∧ baselineGapB m i ≤ order m := by
  obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.mp (labelPositionB_injective m hm)) ⟨i, hi⟩
  have hp := labelIndexB_value m (j.val + 1) hm (by have := j.isLt; omega)
  have hv := congrArg Fin.val hj
  change labelIndexB m (j.val + 1) = i at hv
  rw [hv] at hp
  have hlt := j.isLt
  omega

theorem baselineGapB_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (fun i : Fin (order m) => baselineGapB m i.val) := by
  intro i j hij
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp (labelPositionB_injective m hm)) i
  obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.mp (labelPositionB_injective m hm)) j
  have hva := congrArg Fin.val ha
  have hvb := congrArg Fin.val hb
  change labelIndexB m (a.val + 1) = i.val at hva
  change labelIndexB m (b.val + 1) = j.val at hvb
  change baselineGapB m i.val = baselineGapB m j.val at hij
  rw [← hva, ← hvb, labelIndexB_value m _ hm (by have := a.isLt; omega),
    labelIndexB_value m _ hm (by have := b.isLt; omega)] at hij
  have hab : a = b := Fin.ext (by omega)
  exact ha.symm.trans ((congrArg (labelPositionB m hm) hab).trans hb)

theorem indexed_palette_perm (n : ℕ) (f : Fin n → ℕ)
    (hrange : ∀ i, 0 < f i ∧ f i ≤ n) (hinj : Function.Injective f) :
    (List.ofFn f).Perm (fullGapList n) := by
  have hnodup := List.nodup_ofFn.mpr hinj
  apply (List.perm_ext_iff_of_nodup hnodup (fullGapList_nodup _)).mpr
  intro x
  rw [fullGapList_mem]
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hrange i
  · intro hx
    let g : Fin n → Fin n := fun i => ⟨f i - 1, by have := hrange i; omega⟩
    have hg : Function.Injective g := by
      intro i j hij
      apply hinj
      have hv : f i - 1 = f j - 1 := congrArg Fin.val hij
      have hi := hrange i
      have hj := hrange j
      omega
    obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.mp hg) ⟨x - 1, by omega⟩
    apply List.mem_ofFn.mpr
    refine ⟨i, ?_⟩
    have hv : f i - 1 = x - 1 := congrArg Fin.val hi
    have hi' := hrange i
    omega

def baselineWordB (m : ℕ) : List ℕ := List.ofFn (fun i : Fin (order m) => baselineGapB m i.val)

theorem baselineWordB_perm (m : ℕ) (hm : 1 ≤ m) :
    (baselineWordB m).Perm (fullGapList (order m)) := by
  apply indexed_palette_perm
  · intro i
    exact baselineGapB_range m i.val hm i.isLt
  · exact baselineGapB_injective m hm

def switchEdgeBNat (m : ℕ) (a : Choices m) (i : ℕ) : ℕ :=
  if 2 ≤ i ∧ i < 4 * m then
    if epsilon m a.2 (i / 2) = 0 then i else 4 * m + 1 - i
  else if 4 * m + 3 ≤ i ∧ i ≤ 8 * m then
    if eta m a.1 ((i - (4 * m + 1)) / 2) = 0 then i else 12 * m + 3 - i
  else i

theorem switchEdgeBNat_bound (m : ℕ) (a : Choices m) (i : ℕ) (hi : i < order m) :
    switchEdgeBNat m a i < order m := by
  unfold switchEdgeBNat order at *
  split_ifs <;> omega

theorem switchEdgeBNat_involutive (m : ℕ) (a : Choices m) :
    Function.Involutive (switchEdgeBNat m a) := by
  intro i
  by_cases hl : 2 ≤ i ∧ i < 4 * m
  · by_cases hb : epsilon m a.2 (i / 2) = 0
    · have heq : switchEdgeBNat m a i = i := by simp [switchEdgeBNat, hl, hb]
      rw [heq, heq]
    · have heq : switchEdgeBNat m a i = 4 * m + 1 - i := by simp [switchEdgeBNat, hl, hb]
      rw [heq]
      have hl' : 2 ≤ 4 * m + 1 - i ∧ 4 * m + 1 - i < 4 * m := by omega
      have hp : (4 * m + 1 - i) / 2 = 2 * m - i / 2 := by omega
      have hb' : epsilon m a.2 ((4 * m + 1 - i) / 2) ≠ 0 := by
        rw [hp, epsilon_symmetric m a.2 (i / 2) (by omega)]
        exact hb
      simp only [switchEdgeBNat, if_pos hl', if_neg hb']
      omega
  · by_cases hu : 4 * m + 3 ≤ i ∧ i ≤ 8 * m
    · by_cases hb : eta m a.1 ((i - (4 * m + 1)) / 2) = 0
      · have heq : switchEdgeBNat m a i = i := by simp [switchEdgeBNat, hl, hu, hb]
        rw [heq, heq]
      · have heq : switchEdgeBNat m a i = 12 * m + 3 - i := by simp [switchEdgeBNat, hl, hu, hb]
        rw [heq]
        have hl' : ¬ (2 ≤ 12 * m + 3 - i ∧ 12 * m + 3 - i < 4 * m) := by omega
        have hu' : 4 * m + 3 ≤ 12 * m + 3 - i ∧ 12 * m + 3 - i ≤ 8 * m := by omega
        have hp : (12 * m + 3 - i - (4 * m + 1)) / 2 =
            2 * m - (i - (4 * m + 1)) / 2 := by omega
        have hb' : eta m a.1 ((12 * m + 3 - i - (4 * m + 1)) / 2) ≠ 0 := by
          rw [hp, eta_symmetric m a.1 ((i - (4 * m + 1)) / 2) (by omega)]
          exact hb
        simp only [switchEdgeBNat, if_neg hl', if_pos hu', if_neg hb']
        omega
    · have heq : switchEdgeBNat m a i = i := by simp [switchEdgeBNat, hl, hu]
      rw [heq, heq]

def switchEdgeB (m : ℕ) (a : Choices m) (i : Fin (order m)) : Fin (order m) :=
  ⟨switchEdgeBNat m a i.val, switchEdgeBNat_bound m a i.val i.isLt⟩

def switchPermB (m : ℕ) (a : Choices m) : Equiv.Perm (Fin (order m)) :=
  Function.Involutive.toPerm (switchEdgeB m a) (by
    intro i
    apply Fin.ext
    exact switchEdgeBNat_involutive m a i.val)

@[simp] theorem switchPermB_apply (m : ℕ) (a : Choices m) (i : Fin (order m)) :
    switchPermB m a i = switchEdgeB m a i := rfl

/-- The simultaneous switch word is an actual gap permutation, by an
explicit involution of its edge positions. Its coordinate connection is
proved separately; validity is not a hypothesis of this statement. -/
def switchedWordB (m : ℕ) (a : Choices m) : List ℕ :=
  List.ofFn (fun i : Fin (order m) => baselineGapB m (switchEdgeB m a i).val)

theorem switchedWordB_perm (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    (switchedWordB m a).Perm (fullGapList (order m)) := by
  simpa only [switchedWordB, Function.comp_def, switchPermB_apply] using (Equiv.Perm.ofFn_comp_perm (switchPermB m a)
    (fun i : Fin (order m) => baselineGapB m i.val)).trans (baselineWordB_perm m hm)

theorem baseline_lower_B (m j : ℕ) (hj0 : 0 < j) (hj : j < 2 * m) :
    baselineGapB m (4 * m + 2 * j + 1) = lowInB m 0 j ∧
    baselineGapB m (4 * m + 2 * j + 2) = lowOutB m 0 j := by
  have hformula (i : ℕ) (hi : 4 * m + 3 ≤ i) (hi' : i ≤ 8 * m) :
      baselineGapB m i =
        (if i % 2 = 0 then 2 * ((i - 4 * m) / 2) - 1 + ((i - 4 * m) / 2) % 2
        else 8 * m + 3 - 2 * ((i - (4 * m + 1)) / 2) - ((i - (4 * m + 1)) / 2) % 2) := by
    simp only [baselineGapB, if_neg (show i ≠ 0 by omega), if_neg (show i ≠ 1 by omega),
      if_neg (show i ≠ 2 by omega), if_neg (show ¬i < 4 * m - 1 by omega),
      if_neg (show i ≠ 4 * m - 1 by omega), if_neg (show i ≠ 4 * m by omega),
      if_neg (show i ≠ 4 * m + 1 by omega), if_neg (show i ≠ 8 * m + 2 by omega),
      if_neg (show i ≠ 4 * m + 2 by omega), if_neg (show i ≠ 8 * m + 1 by omega)]
  rw [hformula _ (by omega) (by omega), hformula _ (by omega) (by omega)]
  have hdiv : (4 * m + 2 * j + 1 - (4 * m + 1)) / 2 = j := by omega
  have hdiv' : (4 * m + 2 * j + 2 - 4 * m) / 2 = j + 1 := by omega
  have hp : (4 * m + 2 * j + 1) % 2 ≠ 0 := by omega
  have hp' : (4 * m + 2 * j + 2) % 2 = 0 := by omega
  have hpar : j % 2 + (j + 1) % 2 = 1 := by omega
  constructor
  · rw [if_neg hp, hdiv]
    simp [lowInB]
  · rw [if_pos hp', hdiv']
    simp only [lowOutB, Nat.mul_zero, Nat.add_zero]
    omega

theorem baseline_upper_B (m j : ℕ) (hj0 : 1 < j) (hj : j < 2 * m - 1) :
    baselineGapB m (2 * j) = upInB m 0 j ∧
    baselineGapB m (2 * j + 1) = upOutB m 0 j := by
  have hformula (i : ℕ) (hi : 3 ≤ i) (hi' : i < 4 * m - 1) :
      baselineGapB m i =
        (if (i - 3) % 4 = 0 then 4 * m + 5 + (i - 3)
        else if (i - 3) % 4 = 1 then 4 * m - 2 - (i - 3)
        else if (i - 3) % 4 = 2 then (i - 3) + 2 else 8 * m + 1 - (i - 3)) := by
    simp only [baselineGapB, if_neg (show i ≠ 0 by omega), if_neg (show i ≠ 1 by omega),
      if_neg (show i ≠ 2 by omega), if_pos hi']
  rw [hformula _ (by omega) (by omega), hformula _ (by omega) (by omega)]
  constructor <;> simp only [upInB, upOutB, Nat.sub_zero, Nat.add_zero] <;> split_ifs <;> omega

theorem switched_lower_B (m : ℕ) (a : Choices m) (j : ℕ)
    (hj0 : 0 < j) (hj : j < 2 * m) :
    baselineGapB m (switchEdgeBNat m a (4 * m + 2 * j + 1)) = lowInB m (eta m a.1 j) j ∧
    baselineGapB m (switchEdgeBNat m a (4 * m + 2 * j + 2)) = lowOutB m (eta m a.1 j) j := by
  have hl : ¬ (2 ≤ 4 * m + 2 * j + 1 ∧ 4 * m + 2 * j + 1 < 4 * m) := by omega
  have hl' : ¬ (2 ≤ 4 * m + 2 * j + 2 ∧ 4 * m + 2 * j + 2 < 4 * m) := by omega
  have hr : 4 * m + 3 ≤ 4 * m + 2 * j + 1 ∧ 4 * m + 2 * j + 1 ≤ 8 * m := by omega
  have hr' : 4 * m + 3 ≤ 4 * m + 2 * j + 2 ∧ 4 * m + 2 * j + 2 ≤ 8 * m := by omega
  have hidx : (4 * m + 2 * j + 1 - (4 * m + 1)) / 2 = j := by omega
  have hidx' : (4 * m + 2 * j + 2 - (4 * m + 1)) / 2 = j := by omega
  simp only [switchEdgeBNat, if_neg hl, if_neg hl', if_pos hr, if_pos hr', hidx, hidx']
  by_cases hb : eta m a.1 j = 0
  · simp only [if_pos hb, hb]
    exact baseline_lower_B m j hj0 hj
  · have hb' : eta m a.1 j = 1 := by have := eta_le_one m a.1 j; omega
    simp only [if_neg hb, hb']
    have hi : 12 * m + 3 - (4 * m + 2 * j + 1) = 4 * m + 2 * (2 * m - j) + 2 := by omega
    have ho : 12 * m + 3 - (4 * m + 2 * j + 2) = 4 * m + 2 * (2 * m - j) + 1 := by omega
    rw [hi, ho]
    have hp := baseline_lower_B m (2 * m - j) (by omega) (by omega)
    have hs := lower_pair_switch m j hj0 hj
    exact ⟨hp.2.trans hs.2.2.1.symm, hp.1.trans hs.2.2.2.symm⟩

theorem switched_upper_B (m : ℕ) (a : Choices m) (j : ℕ)
    (hj0 : 1 < j) (hj : j < 2 * m - 1) :
    baselineGapB m (switchEdgeBNat m a (2 * j)) = upInB m (epsilon m a.2 j) j ∧
    baselineGapB m (switchEdgeBNat m a (2 * j + 1)) = upOutB m (epsilon m a.2 j) j := by
  have hidx : (2 * j) / 2 = j := by omega
  have hidx' : (2 * j + 1) / 2 = j := by omega
  have hr : 2 ≤ 2 * j ∧ 2 * j < 4 * m := by omega
  have hr' : 2 ≤ 2 * j + 1 ∧ 2 * j + 1 < 4 * m := by omega
  simp only [switchEdgeBNat, if_pos hr, if_pos hr', hidx, hidx']
  by_cases hb : epsilon m a.2 j = 0
  · simp only [if_pos hb, hb]
    exact baseline_upper_B m j hj0 hj
  · have hb' : epsilon m a.2 j = 1 := by have := epsilon_le_one m a.2 j; omega
    simp only [if_neg hb, hb']
    have hi : 4 * m + 1 - 2 * j = 2 * (2 * m - j) + 1 := by omega
    have ho : 4 * m + 1 - (2 * j + 1) = 2 * (2 * m - j) := by omega
    rw [hi, ho]
    have hp := baseline_upper_B m (2 * m - j) (by omega) (by omega)
    have hs := upper_pair_switch m j hj0 hj
    exact ⟨hp.2.trans hs.2.2.1.symm, hp.1.trans hs.2.2.2.symm⟩

end CorralFormalization.EvenSwitches
