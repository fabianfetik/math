import CorralFormalization.ConstructionSupport.PhysicalRows

namespace CorralFormalization.EvenSwitches

open Finset

def height (m : ℕ) : ℕ := 4 * m + 2
def halfHeight (m : ℕ) : ℕ := 2 * m + 1
def order (m : ℕ) : ℕ := 8 * m + 3
def clock (m : ℕ) : ℕ := height m * order m

/-- Exactly the independent bits in (D3): m lower and m-1 upper bits. -/
abbrev Choices (m : ℕ) := (Fin m → Bool) × (Fin (m - 1) → Bool)

/-- Expand the lower independent bits by reflection of the index. -/
def eta (m : ℕ) (a : Fin m → Bool) (j : ℕ) : ℕ :=
  if h : 0 < j ∧ j < 2 * m then
    (a ⟨min j (2 * m - j) - 1, by omega⟩).toNat
  else 1

/-- Expand the upper independent bits; indices 0,2m are one and 1,2m-1 zero. -/
def epsilon (m : ℕ) (a : Fin (m - 1) → Bool) (j : ℕ) : ℕ :=
  if h : 1 < j ∧ j < 2 * m - 1 then
    (a ⟨min j (2 * m - j) - 2, by omega⟩).toNat
  else if j = 0 ∨ j = 2 * m then 1 else 0

theorem eta_le_one (m : ℕ) (a : Fin m → Bool) (j : ℕ) : eta m a j ≤ 1 := by
  unfold eta
  split_ifs <;> simp [Bool.toNat_le]

theorem epsilon_le_one (m : ℕ) (a : Fin (m - 1) → Bool) (j : ℕ) :
    epsilon m a j ≤ 1 := by
  unfold epsilon
  split_ifs <;> simp [Bool.toNat_le]

theorem eta_symmetric (m : ℕ) (a : Fin m → Bool) (j : ℕ) (hj : j ≤ 2 * m) :
    eta m a (2 * m - j) = eta m a j := by
  have hin : (0 < 2 * m - j ∧ 2 * m - j < 2 * m) ↔ (0 < j ∧ j < 2 * m) := by omega
  unfold eta
  split_ifs with h h' h'
  · congr 2
    apply Fin.ext
    simp only [Nat.sub_sub_self hj, min_comm]
  · exact False.elim (h' (hin.mp h))
  · exact False.elim (h (hin.mpr h'))
  · rfl

theorem epsilon_symmetric (m : ℕ) (a : Fin (m - 1) → Bool) (j : ℕ)
    (hj : j ≤ 2 * m) : epsilon m a (2 * m - j) = epsilon m a j := by
  have hin : (1 < 2 * m - j ∧ 2 * m - j < 2 * m - 1) ↔
      (1 < j ∧ j < 2 * m - 1) := by omega
  have hend : (2 * m - j = 0 ∨ 2 * m - j = 2 * m) ↔ (j = 0 ∨ j = 2 * m) := by omega
  unfold epsilon
  split_ifs with h h' h' h'' h'' h''
  all_goals try omega
  congr 2
  apply Fin.ext
  simp only [Nat.sub_sub_self hj, min_comm]

@[simp] theorem eta_zero (m : ℕ) (a : Fin m → Bool) : eta m a 0 = 1 := by simp [eta]
@[simp] theorem eta_last (m : ℕ) (a : Fin m → Bool) : eta m a (2 * m) = 1 := by simp [eta]
@[simp] theorem epsilon_zero (m : ℕ) (a : Fin (m - 1) → Bool) : epsilon m a 0 = 1 := by simp [epsilon]
@[simp] theorem epsilon_last (m : ℕ) (a : Fin (m - 1) → Bool) : epsilon m a (2 * m) = 1 := by simp [epsilon]
@[simp] theorem epsilon_one (m : ℕ) (hm : 1 ≤ m) (a : Fin (m - 1) → Bool) :
    epsilon m a 1 = 0 := by simp [epsilon]; omega
@[simp] theorem epsilon_penultimate (m : ℕ) (hm : 1 ≤ m) (a : Fin (m - 1) → Bool) :
    epsilon m a (2 * m - 1) = 0 := by simp [epsilon]; omega

theorem eta_recover (m : ℕ) (a : Fin m → Bool) (i : Fin m) :
    eta m a (i.val + 1) = (a i).toNat := by
  have hi := i.isLt
  have hmin : min (i.val + 1) (2 * m - (i.val + 1)) = i.val + 1 := by omega
  rw [eta, dif_pos (show 0 < i.val + 1 ∧ i.val + 1 < 2 * m by omega)]
  congr 2
  apply Fin.ext
  simp [hmin]

theorem epsilon_recover (m : ℕ) (a : Fin (m - 1) → Bool) (i : Fin (m - 1)) :
    epsilon m a (i.val + 2) = (a i).toNat := by
  have hi := i.isLt
  have hmin : min (i.val + 2) (2 * m - (i.val + 2)) = i.val + 2 := by omega
  rw [epsilon, dif_pos (show 1 < i.val + 2 ∧ i.val + 2 < 2 * m - 1 by omega)]
  congr 2
  apply Fin.ext
  simp [hmin]

theorem choices_card (m : ℕ) (hm : 1 ≤ m) : Fintype.card (Choices m) = 2 ^ (2 * m - 1) := by
  simp only [Choices, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← pow_add]
  congr 1
  omega

/-- Literal ordinary representative coordinates in (D4)-(D5). -/
def lowerA (m : ℕ) (a : Fin m → Bool) (j : ℕ) : ℕ :=
  (2 * j + 1 + eta m a j) * (height m - 1)
def lowerB (m : ℕ) (a : Fin m → Bool) (j : ℕ) : ℕ :=
  (2 * j + 2 - eta m a j) * (height m - 1)
def middleA (m i : ℕ) : ℕ := 2 * height m * i - i % 2
def middleB (m i : ℕ) : ℕ := 2 * height m * i - (1 - i % 2)
def upperA (m : ℕ) (a : Fin (m - 1) → Bool) (j : ℕ) : ℕ :=
  (height m + 2 + 2 * j) * (height m - 1) + epsilon m a j
def upperB (m : ℕ) (a : Fin (m - 1) → Bool) (j : ℕ) : ℕ :=
  (height m + 2 + 2 * j) * (height m - 1) + 1 - epsilon m a j
def fixedA (m r : ℕ) : ℕ := 2 * height m * (halfHeight m + 1 + 2 * r)
def fixedB (m r : ℕ) : ℕ := 2 * height m * (halfHeight m + 2 + 2 * r)

/-- Actual finite site set printed as A in (D4), not a hypothetical valid row. -/
def rowA (m : ℕ) (a : Choices m) : Finset ℕ :=
  {0} ∪ (Finset.range (halfHeight m)).image (lowerA m a.1) ∪
    (Finset.Ico 1 (halfHeight m)).image (middleA m) ∪
    (Finset.range (halfHeight m)).image (upperA m a.2) ∪
    (Finset.range m).biUnion (fun r => {fixedA m r, fixedA m r + height m - 1})

/-- The baseline A gap at each edge of the actual order (D6), including
the physical wrap. This is §6.2's five-item formula, indexed from zero. -/
def baselineGapA (m i : ℕ) : ℕ :=
  if i = 0 then 8 * m + 2
  else if i < 4 * m + 1 then
    if i = 1 then 1
    else if i = 4 * m then 4 * m + 2
    else if i % 2 = 1 then 4 * m + i + 2 - ((i + 1) / 2) % 2
    else 4 * m + 1 - i + (i / 2) % 2
  else if i = 4 * m + 1 then 8 * m + 3
  else if i = 8 * m + 2 then 4 * m + 1
  else let q := i - (4 * m + 2)
    if q % 4 = 0 then 4 * m + 4 + q - (if q = 0 then 1 else 0)
    else if q % 4 = 1 then 4 * m - 1 - q
    else if q % 4 = 2 then q + 1
    else 8 * m + 2 - q + (if q = 4 * m - 1 then 1 else 0)

theorem baselineGapA_range (m i : ℕ) (hm : 1 ≤ m) (hi : i < order m) :
    0 < baselineGapA m i ∧ baselineGapA m i ≤ order m := by
  unfold baselineGapA order at *
  dsimp only
  split_ifs <;> omega

set_option maxHeartbeats 3000000 in
theorem baselineGapA_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (fun i : Fin (order m) => baselineGapA m i.val) := by
  intro i j hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  unfold baselineGapA order at *
  dsimp only at hij
  split_ifs at hij <;> omega

def baselineWordA (m : ℕ) : List ℕ := List.ofFn (fun i : Fin (order m) => baselineGapA m i.val)

theorem baselineWordA_perm (m : ℕ) (hm : 1 ≤ m) :
    (baselineWordA m).Perm (fullGapList (order m)) := by
  apply (List.perm_ext_iff_of_nodup ?_ (fullGapList_nodup _)).mpr
  · intro x
    rw [fullGapList_mem]
    constructor
    · intro hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact baselineGapA_range m i.val hm i.isLt
    · intro hx
      let f : Fin (order m) → Fin (order m) := fun i =>
        ⟨baselineGapA m i.val - 1, by have := baselineGapA_range m i.val hm i.isLt; omega⟩
      have hf : Function.Injective f := by
        intro i j hij
        apply baselineGapA_injective m hm
        have hv := congrArg Fin.val hij
        have hi := baselineGapA_range m i.val hm i.isLt
        have hj := baselineGapA_range m j.val hm j.isLt
        change baselineGapA m i.val - 1 = baselineGapA m j.val - 1 at hv
        change baselineGapA m i.val = baselineGapA m j.val
        omega
      obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.mp hf) ⟨x - 1, by omega⟩
      apply List.mem_ofFn.mpr
      refine ⟨i, ?_⟩
      have hv := congrArg Fin.val hi
      have hi' := baselineGapA_range m i.val hm i.isLt
      change baselineGapA m i.val - 1 = x - 1 at hv
      omega
  · apply List.nodup_ofFn.mpr
    exact baselineGapA_injective m hm

def lowInA (m b j : ℕ) : ℕ := 4 * m + 1 - 2 * j + j % 2 + (4 * m + 1) * b
def lowOutA (m b j : ℕ) : ℕ := 4 * m + 2 + 2 * j + j % 2 - (4 * m + 1) * b
def lowInB (m b j : ℕ) : ℕ := 8 * m + 3 - 2 * j - j % 2 - (4 * m + 1) * b
def lowOutB (m b j : ℕ) : ℕ := 2 * j + 2 - j % 2 + (4 * m + 1) * b
def upInA (m b j : ℕ) : ℕ :=
  if j % 2 = 0 then 8 * m + 3 - 2 * j + b else 4 * m - 2 * j + b
def upOutA (m b j : ℕ) : ℕ :=
  if j % 2 = 0 then 4 * m + 4 + 2 * j - b else 2 * j + 1 - b
def upInB (m b j : ℕ) : ℕ :=
  if j % 2 = 0 then 4 * m + 1 - 2 * j - b else 8 * m + 4 - 2 * j - b
def upOutB (m b j : ℕ) : ℕ :=
  if j % 2 = 0 then 2 * j + b else 4 * m + 3 + 2 * j + b

/-- Actual distances at each lower A centre, not merely formal palettes. -/
theorem lowerA_distances (m : ℕ) (hm : 1 ≤ m) (a : Fin m → Bool)
    (j : ℕ) (hj : j ≤ 2 * m) :
    middleA m j + lowInA m (eta m a j) j = lowerA m a j ∧
    lowerA m a j + lowOutA m (eta m a j) j = middleA m (j + 1) := by
  have hb := eta_le_one m a j
  have hheight : height m - 1 = 4 * m + 1 := by unfold height; omega
  have hd : j % 2 ≤ 2 * height m * j := by
    by_cases hj0 : j = 0
    · simp [hj0]
    · have hprod : j ≤ 2 * height m * j := Nat.le_mul_of_pos_left j (by unfold height; omega)
      omega
  have hd' : (j + 1) % 2 ≤ 2 * height m * (j + 1) := by
    unfold height
    nlinarith [Nat.mod_lt (j + 1) (by decide : 0 < 2)]
  have hsub := Nat.sub_add_cancel hd
  have hsub' := Nat.sub_add_cancel hd'
  have hin := Nat.sub_add_cancel (show 2 * j ≤ 4 * m + 1 by omega)
  have hout := Nat.sub_add_cancel
    (show (4 * m + 1) * eta m a j ≤ 4 * m + 2 + 2 * j + j % 2 by
      have hmul := Nat.mul_le_mul_left (4 * m + 1) hb
      omega)
  have hpar : (j + 1) % 2 + j % 2 = 1 := by omega
  unfold lowerA lowInA lowOutA
  rw [hheight]
  constructor <;> dsimp [middleA] <;> unfold height at * <;> nlinarith

/-- D8-D11's concrete paired-index arithmetic. The sums are neither a
validity assumption nor a hidden orbit assumption. -/
theorem lower_pair_switch (m j : ℕ) (hj0 : 0 < j) (hj : j < 2 * m) :
    lowInA m 1 j = lowOutA m 0 (2 * m - j) ∧
    lowOutA m 1 j = lowInA m 0 (2 * m - j) ∧
    lowInB m 1 j = lowOutB m 0 (2 * m - j) ∧
    lowOutB m 1 j = lowInB m 0 (2 * m - j) := by
  unfold lowInA lowOutA lowInB lowOutB
  omega

theorem upper_pair_switch (m j : ℕ) (hj0 : 1 < j) (hj : j < 2 * m - 1) :
    upInA m 1 j = upOutA m 0 (2 * m - j) ∧
    upOutA m 1 j = upInA m 0 (2 * m - j) ∧
    upInB m 1 j = upOutB m 0 (2 * m - j) ∧
    upOutB m 1 j = upInB m 0 (2 * m - j) := by
  unfold upInA upOutA upInB upOutB
  split_ifs <;> omega

def switchEdgeNat (m : ℕ) (a : Choices m) (i : ℕ) : ℕ :=
  if 2 ≤ i ∧ i < 4 * m then
    if eta m a.1 (i / 2) = 0 then i else 4 * m + 1 - i
  else if 4 * m + 3 ≤ i ∧ i ≤ 8 * m then
    if epsilon m a.2 ((i - (4 * m + 1)) / 2) = 0 then i else 12 * m + 3 - i
  else i

theorem switchEdgeNat_bound (m : ℕ) (a : Choices m) (i : ℕ) (hi : i < order m) :
    switchEdgeNat m a i < order m := by
  unfold switchEdgeNat order at *
  split_ifs <;> omega

theorem switchEdgeNat_involutive (m : ℕ) (a : Choices m) :
    Function.Involutive (switchEdgeNat m a) := by
  intro i
  by_cases hl : 2 ≤ i ∧ i < 4 * m
  · by_cases hb : eta m a.1 (i / 2) = 0
    · have heq : switchEdgeNat m a i = i := by simp [switchEdgeNat, hl, hb]
      rw [heq, heq]
    · have heq : switchEdgeNat m a i = 4 * m + 1 - i := by simp [switchEdgeNat, hl, hb]
      rw [heq]
      have hl' : 2 ≤ 4 * m + 1 - i ∧ 4 * m + 1 - i < 4 * m := by omega
      have hp : (4 * m + 1 - i) / 2 = 2 * m - i / 2 := by omega
      have hb' : eta m a.1 ((4 * m + 1 - i) / 2) ≠ 0 := by
        rw [hp, eta_symmetric m a.1 (i / 2) (by omega)]
        exact hb
      simp only [switchEdgeNat, if_pos hl', if_neg hb']
      omega
  · by_cases hu : 4 * m + 3 ≤ i ∧ i ≤ 8 * m
    · by_cases hb : epsilon m a.2 ((i - (4 * m + 1)) / 2) = 0
      · have heq : switchEdgeNat m a i = i := by simp [switchEdgeNat, hl, hu, hb]
        rw [heq, heq]
      · have heq : switchEdgeNat m a i = 12 * m + 3 - i := by simp [switchEdgeNat, hl, hu, hb]
        rw [heq]
        have hl' : ¬ (2 ≤ 12 * m + 3 - i ∧ 12 * m + 3 - i < 4 * m) := by omega
        have hu' : 4 * m + 3 ≤ 12 * m + 3 - i ∧ 12 * m + 3 - i ≤ 8 * m := by omega
        have hp : (12 * m + 3 - i - (4 * m + 1)) / 2 =
            2 * m - (i - (4 * m + 1)) / 2 := by omega
        have hb' : epsilon m a.2 ((12 * m + 3 - i - (4 * m + 1)) / 2) ≠ 0 := by
          rw [hp, epsilon_symmetric m a.2 ((i - (4 * m + 1)) / 2) (by omega)]
          exact hb
        simp only [switchEdgeNat, if_neg hl', if_pos hu', if_neg hb']
        omega
    · have heq : switchEdgeNat m a i = i := by simp [switchEdgeNat, hl, hu]
      rw [heq, heq]

def switchEdge (m : ℕ) (a : Choices m) (i : Fin (order m)) : Fin (order m) :=
  ⟨switchEdgeNat m a i.val, switchEdgeNat_bound m a i.val i.isLt⟩

def switchPerm (m : ℕ) (a : Choices m) : Equiv.Perm (Fin (order m)) :=
  Function.Involutive.toPerm (switchEdge m a) (by
    intro i
    apply Fin.ext
    exact switchEdgeNat_involutive m a i.val)

@[simp] theorem switchPerm_apply (m : ℕ) (a : Choices m) (i : Fin (order m)) :
    switchPerm m a i = switchEdge m a i := rfl

/-- The simultaneous switch word is an actual gap permutation, by an
explicit involution of its edge positions. Its coordinate connection is
proved separately; validity is not a hypothesis of this statement. -/
def switchedWordA (m : ℕ) (a : Choices m) : List ℕ :=
  List.ofFn (fun i : Fin (order m) => baselineGapA m (switchEdge m a i).val)

theorem switchedWordA_perm (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    (switchedWordA m a).Perm (fullGapList (order m)) := by
  simpa only [switchedWordA, Function.comp_def, switchPerm_apply] using (Equiv.Perm.ofFn_comp_perm (switchPerm m a)
    (fun i : Fin (order m) => baselineGapA m i.val)).trans (baselineWordA_perm m hm)

theorem baseline_lower_A (m j : ℕ) (hj0 : 0 < j) (hj : j < 2 * m) :
    baselineGapA m (2 * j) = lowInA m 0 j ∧
    baselineGapA m (2 * j + 1) = lowOutA m 0 j := by
  have hdiv : (2 * j) / 2 = j := by omega
  have hdiv' : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  have hpar : j % 2 + (j + 1) % 2 = 1 := by omega
  constructor
  · have h0 : 2 * j ≠ 0 := by omega
    have hl : 2 * j < 4 * m + 1 := by omega
    have h1 : 2 * j ≠ 1 := by omega
    have h4 : 2 * j ≠ 4 * m := by omega
    have hp : (2 * j) % 2 ≠ 1 := by omega
    simp [baselineGapA, h0, hl, h1, h4, hp, hdiv, lowInA]
  · have h0 : 2 * j + 1 ≠ 0 := by omega
    have hl : 2 * j + 1 < 4 * m + 1 := by omega
    have h1 : 2 * j + 1 ≠ 1 := by omega
    have h4 : 2 * j + 1 ≠ 4 * m := by omega
    have hp : (2 * j + 1) % 2 = 1 := by omega
    simp only [baselineGapA, if_neg h0, if_pos hl, if_neg h1, if_neg h4,
      if_pos hp, hdiv', lowOutA, Nat.mul_zero, Nat.sub_zero]
    omega

theorem baseline_upper_A (m j : ℕ) (hj0 : 0 < j) (hj : j < 2 * m) :
    baselineGapA m (4 * m + 2 * j + 1) = upInA m 0 j ∧
    baselineGapA m (4 * m + 2 * j + 2) = upOutA m 0 j := by
  have hformula (i : ℕ) (hi : 4 * m + 2 ≤ i) (hi' : i < 8 * m + 2) :
      baselineGapA m i =
        (if (i - (4 * m + 2)) % 4 = 0 then
          4 * m + 4 + (i - (4 * m + 2)) - (if i - (4 * m + 2) = 0 then 1 else 0)
        else if (i - (4 * m + 2)) % 4 = 1 then 4 * m - 1 - (i - (4 * m + 2))
        else if (i - (4 * m + 2)) % 4 = 2 then (i - (4 * m + 2)) + 1
        else 8 * m + 2 - (i - (4 * m + 2)) + (if i - (4 * m + 2) = 4 * m - 1 then 1 else 0)) := by
    simp only [baselineGapA, if_neg (show i ≠ 0 by omega),
      if_neg (show ¬ i < 4 * m + 1 by omega), if_neg (show i ≠ 4 * m + 1 by omega),
      if_neg (show i ≠ 8 * m + 2 by omega)]
  rw [hformula _ (by omega) (by omega), hformula _ (by omega) (by omega)]
  constructor <;> simp only [upInA, upOutA, Nat.add_zero, Nat.sub_zero] <;>
    split_ifs <;> omega

theorem switched_lower_A (m : ℕ) (a : Choices m) (j : ℕ)
    (hj0 : 0 < j) (hj : j < 2 * m) :
    baselineGapA m (switchEdgeNat m a (2 * j)) = lowInA m (eta m a.1 j) j ∧
    baselineGapA m (switchEdgeNat m a (2 * j + 1)) = lowOutA m (eta m a.1 j) j := by
  have hidx : (2 * j) / 2 = j := by omega
  have hidx' : (2 * j + 1) / 2 = j := by omega
  have hr : 2 ≤ 2 * j ∧ 2 * j < 4 * m := by omega
  have hr' : 2 ≤ 2 * j + 1 ∧ 2 * j + 1 < 4 * m := by omega
  simp only [switchEdgeNat, if_pos hr, if_pos hr', hidx, hidx']
  by_cases hb : eta m a.1 j = 0
  · simp only [if_pos hb, hb]
    exact baseline_lower_A m j hj0 hj
  · have hb' : eta m a.1 j = 1 := by have := eta_le_one m a.1 j; omega
    simp only [if_neg hb, hb']
    have hi : 4 * m + 1 - 2 * j = 2 * (2 * m - j) + 1 := by omega
    have ho : 4 * m + 1 - (2 * j + 1) = 2 * (2 * m - j) := by omega
    rw [hi, ho]
    have hp := baseline_lower_A m (2 * m - j) (by omega) (by omega)
    have hs := lower_pair_switch m j hj0 hj
    exact ⟨hp.2.trans hs.1.symm, hp.1.trans hs.2.1.symm⟩

theorem switched_upper_A (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (j : ℕ)
    (hj0 : 0 < j) (hj : j < 2 * m) :
    baselineGapA m (switchEdgeNat m a (4 * m + 2 * j + 1)) = upInA m (epsilon m a.2 j) j ∧
    baselineGapA m (switchEdgeNat m a (4 * m + 2 * j + 2)) = upOutA m (epsilon m a.2 j) j := by
  have hl : ¬ (2 ≤ 4 * m + 2 * j + 1 ∧ 4 * m + 2 * j + 1 < 4 * m) := by omega
  have hl' : ¬ (2 ≤ 4 * m + 2 * j + 2 ∧ 4 * m + 2 * j + 2 < 4 * m) := by omega
  have hr : 4 * m + 3 ≤ 4 * m + 2 * j + 1 ∧ 4 * m + 2 * j + 1 ≤ 8 * m := by omega
  have hr' : 4 * m + 3 ≤ 4 * m + 2 * j + 2 ∧ 4 * m + 2 * j + 2 ≤ 8 * m := by omega
  have hidx : (4 * m + 2 * j + 1 - (4 * m + 1)) / 2 = j := by omega
  have hidx' : (4 * m + 2 * j + 2 - (4 * m + 1)) / 2 = j := by omega
  simp only [switchEdgeNat, if_neg hl, if_neg hl', if_pos hr, if_pos hr', hidx, hidx']
  by_cases hb : epsilon m a.2 j = 0
  · simp only [if_pos hb, hb]
    exact baseline_upper_A m j hj0 hj
  · have hb' : epsilon m a.2 j = 1 := by have := epsilon_le_one m a.2 j; omega
    have hj1 : j ≠ 1 := by intro h; subst j; simp [epsilon_one m hm] at hb
    have hjlast : j ≠ 2 * m - 1 := by intro h; subst j; simp [epsilon_penultimate m hm] at hb
    simp only [if_neg hb, hb']
    have hi : 12 * m + 3 - (4 * m + 2 * j + 1) = 4 * m + 2 * (2 * m - j) + 2 := by omega
    have ho : 12 * m + 3 - (4 * m + 2 * j + 2) = 4 * m + 2 * (2 * m - j) + 1 := by omega
    rw [hi, ho]
    have hp := baseline_upper_A m (2 * m - j) (by omega) (by omega)
    have hs := upper_pair_switch m j (by omega) (by omega)
    exact ⟨hp.2.trans hs.1.symm, hp.1.trans hs.2.1.symm⟩

def siteA (m : ℕ) (a : Choices m) (i : ℕ) : ℕ :=
  if i = 0 then 0
  else if i < 4 * m + 2 then
    if i % 2 = 0 then middleA m (i / 2) else lowerA m a.1 (i / 2)
  else let q := i - (4 * m + 2)
    if q % 2 = 0 then upperA m a.2 (q / 2)
    else if q % 4 = 1 then fixedA m (q / 4)
    else fixedA m (q / 4) + height m - 1

theorem upperA_odd_distances (m : ℕ) (hm : 1 ≤ m) (a : Fin (m - 1) → Bool)
    (r : ℕ) (hr : r < m) :
    fixedA m r + upInA m (epsilon m a (2 * r + 1)) (2 * r + 1) = upperA m a (2 * r + 1) ∧
    upperA m a (2 * r + 1) + upOutA m (epsilon m a (2 * r + 1)) (2 * r + 1) =
      fixedA m r + height m - 1 := by
  have hb := epsilon_le_one m a (2 * r + 1)
  have hp : (2 * r + 1) % 2 ≠ 0 := by omega
  have hheight : height m - 1 = 4 * m + 1 := by unfold height; omega
  have hi := Nat.sub_add_cancel (show 2 * (2 * r + 1) ≤ 4 * m by omega)
  have ho := Nat.sub_add_cancel (show epsilon m a (2 * r + 1) ≤ 2 * (2 * r + 1) + 1 by omega)
  have hw := Nat.sub_add_cancel (show 1 ≤ fixedA m r + height m by unfold height; omega)
  unfold upperA fixedA upInA upOutA at *
  rw [hheight]
  simp only [if_neg hp] at *
  unfold height halfHeight at *
  constructor <;> nlinarith

theorem upperA_even_distances (m : ℕ) (hm : 1 ≤ m) (a : Fin (m - 1) → Bool)
    (r : ℕ) (hr : r + 1 < m) :
    (fixedA m r + height m - 1) + upInA m (epsilon m a (2 * r + 2)) (2 * r + 2) =
      upperA m a (2 * r + 2) ∧
    upperA m a (2 * r + 2) + upOutA m (epsilon m a (2 * r + 2)) (2 * r + 2) =
      fixedA m (r + 1) := by
  have hb := epsilon_le_one m a (2 * r + 2)
  have hp : (2 * r + 2) % 2 = 0 := by omega
  have hheight : height m - 1 = 4 * m + 1 := by unfold height; omega
  have hi := Nat.sub_add_cancel (show 2 * (2 * r + 2) ≤ 8 * m + 3 by omega)
  have ho := Nat.sub_add_cancel (show epsilon m a (2 * r + 2) ≤ 4 * m + 4 + 2 * (2 * r + 2) by omega)
  have hw := Nat.sub_add_cancel (show 1 ≤ fixedA m r + height m by unfold height; omega)
  unfold upperA fixedA upInA upOutA at *
  rw [hheight]
  simp only [if_pos hp] at *
  unfold height halfHeight at *
  constructor <;> nlinarith

/-- Every nonmoving A seam, including the physical wrap, has its actual
claimed distance for every bit choice. -/
theorem A_fixed_seams (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    lowerA m a.1 0 = 2 * height m - 2 ∧
    lowerA m a.1 0 + 1 = middleA m 1 ∧
    middleA m (2 * m) + height m = lowerA m a.1 (2 * m) ∧
    lowerA m a.1 (2 * m) + order m = upperA m a.2 0 ∧
    upperA m a.2 0 + (height m + 1) = fixedA m 0 ∧
    (fixedA m (m - 1) + height m - 1) + (height m + 2) = upperA m a.2 (2 * m) ∧
    upperA m a.2 (2 * m) + (height m - 1) = clock m := by
  have hheight : height m - 1 = 4 * m + 1 := by unfold height; omega
  have hmod : (2 * m) % 2 = 0 := by omega
  have hm' : m - 1 + 1 = m := by omega
  have hmul := congrArg (fun x => m * x) hm'
  unfold lowerA upperA middleA fixedA clock
  simp only [eta_zero, eta_last, epsilon_zero, epsilon_last, hheight, hmod,
    Nat.one_mod, Nat.sub_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
  have hs := Nat.sub_add_cancel
    (show 1 ≤ 2 * height m * (halfHeight m + 1 + 2 * (m - 1)) + height m by unfold height; omega)
  have ht : 2 * height m - 2 = 8 * m + 2 := by unfold height; omega
  have hu : 2 * height m * 1 - 1 = 8 * m + 3 := by unfold height; omega
  rw [ht, hu]
  unfold height halfHeight order at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem siteA_lower (m : ℕ) (a : Choices m) (j : ℕ) (hj : j ≤ 2 * m) :
    siteA m a (2 * j + 1) = lowerA m a.1 j := by
  have h0 : 2 * j + 1 ≠ 0 := by omega
  have hl : 2 * j + 1 < 4 * m + 2 := by omega
  have hp : (2 * j + 1) % 2 ≠ 0 := by omega
  have hq : (2 * j + 1) / 2 = j := by omega
  simp [siteA, h0, hl, hp, hq]

theorem siteA_middle (m : ℕ) (a : Choices m) (j : ℕ) (hj0 : 0 < j) (hj : j ≤ 2 * m) :
    siteA m a (2 * j) = middleA m j := by
  have h0 : 2 * j ≠ 0 := by omega
  have hl : 2 * j < 4 * m + 2 := by omega
  have hp : (2 * j) % 2 = 0 := by omega
  have hq : (2 * j) / 2 = j := by omega
  simp [siteA, h0, hl, hp, hq]

theorem siteA_upper (m : ℕ) (a : Choices m) (j : ℕ) :
    siteA m a (4 * m + 2 + 2 * j) = upperA m a.2 j := by
  have h0 : 4 * m + 2 + 2 * j ≠ 0 := by omega
  have hl : ¬ (4 * m + 2 + 2 * j < 4 * m + 2) := by omega
  have hq : 4 * m + 2 + 2 * j - (4 * m + 2) = 2 * j := by omega
  have hp : (2 * j) % 2 = 0 := by omega
  have hd : (2 * j) / 2 = j := by omega
  simp [siteA, h0, hl, hq, hp, hd]

theorem siteA_fixed (m : ℕ) (a : Choices m) (r : ℕ) :
    siteA m a (4 * m + 3 + 4 * r) = fixedA m r ∧
    siteA m a (4 * m + 5 + 4 * r) = fixedA m r + height m - 1 := by
  have h0 : 4 * m + 3 + 4 * r ≠ 0 := by omega
  have h0' : 4 * m + 5 + 4 * r ≠ 0 := by omega
  have hl : ¬ (4 * m + 3 + 4 * r < 4 * m + 2) := by omega
  have hl' : ¬ (4 * m + 5 + 4 * r < 4 * m + 2) := by omega
  have hq : 4 * m + 3 + 4 * r - (4 * m + 2) = 4 * r + 1 := by omega
  have hq' : 4 * m + 5 + 4 * r - (4 * m + 2) = 4 * r + 3 := by omega
  have hp : (4 * r + 1) % 2 ≠ 0 := by omega
  have hp' : (4 * r + 3) % 2 ≠ 0 := by omega
  have hr : (4 * r + 1) % 4 = 1 := by omega
  have hr' : (4 * r + 3) % 4 ≠ 1 := by omega
  have hd : (4 * r + 1) / 4 = r := by omega
  have hd' : (4 * r + 3) / 4 = r := by omega
  simp [siteA, h0, h0', hl, hl', hq, hq', hp, hp', hr, hr', hd, hd']

theorem rowA_mem_iff (m : ℕ) (a : Choices m) (x : ℕ) :
    x ∈ rowA m a ↔ x = 0 ∨
      (∃ j, j < halfHeight m ∧ lowerA m a.1 j = x) ∨
      (∃ j, 1 ≤ j ∧ j < halfHeight m ∧ middleA m j = x) ∨
      (∃ j, j < halfHeight m ∧ upperA m a.2 j = x) ∨
      (∃ r, r < m ∧ (x = fixedA m r ∨ x = fixedA m r + height m - 1)) := by
  simp only [rowA, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_range, Finset.mem_Ico, Finset.mem_biUnion, Finset.mem_insert]
  aesop

/-- The literal D4 point set is exactly the indexed chronological list D6.
Order and gap validity are separate theorems below. -/
theorem siteA_image_eq_rowA (m : ℕ) (a : Choices m) :
    (Finset.range (order m)).image (siteA m a) = rowA m a := by
  ext x
  rw [rowA_mem_iff]
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hib : i < 8 * m + 3 := by simpa [order] using Finset.mem_range.mp hi
    by_cases hi0 : i = 0
    · simp [siteA, hi0]
    · by_cases hil : i < 4 * m + 2
      · by_cases hip : i % 2 = 0
        · right; right; left
          refine ⟨i / 2, by omega, by unfold halfHeight; omega, ?_⟩
          simp [siteA, hi0, hil, hip]
        · right; left
          refine ⟨i / 2, by unfold halfHeight; omega, ?_⟩
          simp [siteA, hi0, hil, hip]
      · let q := i - (4 * m + 2)
        by_cases hip : q % 2 = 0
        · right; right; right; left
          refine ⟨q / 2, by unfold halfHeight; dsimp [q]; omega, ?_⟩
          simp [siteA, hi0, hil, q, hip]
        · right; right; right; right
          refine ⟨q / 4, by dsimp [q]; omega, ?_⟩
          by_cases hiq : q % 4 = 1
          · left; simp [siteA, hi0, hil, q, hip, hiq]
          · right; simp [siteA, hi0, hil, q, hip, hiq]
  · rintro (hx | ⟨j, hj, hx⟩ | ⟨j, hj0, hj, hx⟩ | ⟨j, hj, hx⟩ | ⟨r, hr, hx⟩)
    · exact Finset.mem_image.mpr ⟨0, by simp [order], by simp [siteA, hx]⟩
    · refine Finset.mem_image.mpr ⟨2 * j + 1, Finset.mem_range.mpr (by unfold order halfHeight at *; omega), ?_⟩
      exact (siteA_lower m a j (by unfold halfHeight at hj; omega)).trans hx
    · refine Finset.mem_image.mpr ⟨2 * j, Finset.mem_range.mpr (by unfold order halfHeight at *; omega), ?_⟩
      exact (siteA_middle m a j (by omega) (by unfold halfHeight at hj; omega)).trans hx
    · refine Finset.mem_image.mpr ⟨4 * m + 2 + 2 * j, Finset.mem_range.mpr (by unfold order halfHeight at *; omega), ?_⟩
      exact (siteA_upper m a j).trans hx
    · rcases hx with hx | hx
      · exact Finset.mem_image.mpr ⟨4 * m + 3 + 4 * r,
          Finset.mem_range.mpr (by unfold order; omega), (siteA_fixed m a r).1.trans hx.symm⟩
      · exact Finset.mem_image.mpr ⟨4 * m + 5 + 4 * r,
          Finset.mem_range.mpr (by unfold order; omega), (siteA_fixed m a r).2.trans hx.symm⟩

theorem switchEdgeNat_fixed (m : ℕ) (a : Choices m) (i : ℕ)
    (hl : ¬ (2 ≤ i ∧ i < 4 * m)) (hu : ¬ (4 * m + 3 ≤ i ∧ i ≤ 8 * m)) :
    switchEdgeNat m a i = i := by simp [switchEdgeNat, hl, hu]

set_option maxHeartbeats 1000000 in
theorem switched_A_fixed_gaps (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    baselineGapA m (switchEdgeNat m a 0) = 2 * height m - 2 ∧
    baselineGapA m (switchEdgeNat m a 1) = 1 ∧
    baselineGapA m (switchEdgeNat m a (4 * m)) = height m ∧
    baselineGapA m (switchEdgeNat m a (4 * m + 1)) = order m ∧
    baselineGapA m (switchEdgeNat m a (4 * m + 2)) = height m + 1 ∧
    baselineGapA m (switchEdgeNat m a (8 * m + 1)) = height m + 2 ∧
    baselineGapA m (switchEdgeNat m a (8 * m + 2)) = height m - 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [switchEdgeNat_fixed m a _ (by omega) (by omega)] <;>
    simp (disch := omega) [baselineGapA, height, order] <;> (try split_ifs) <;> omega

theorem A_lower_edges (m : ℕ) (hm : 1 ≤ m) (a : Choices m)
    (j : ℕ) (hj0 : 0 < j) (hj : j < 2 * m) :
    siteA m a (2 * j) + baselineGapA m (switchEdgeNat m a (2 * j)) = siteA m a (2 * j + 1) ∧
    siteA m a (2 * j + 1) + baselineGapA m (switchEdgeNat m a (2 * j + 1)) = siteA m a (2 * j + 2) := by
  have heq : 2 * j + 2 = 2 * (j + 1) := by omega
  rw [heq]
  rw [siteA_middle m a j hj0 (by omega), siteA_lower m a j (by omega),
    siteA_middle m a (j + 1) (by omega) (by omega),
    (switched_lower_A m a j hj0 hj).1, (switched_lower_A m a j hj0 hj).2]
  exact lowerA_distances m hm a.1 j (by omega)

theorem A_upper_odd_edges (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (r : ℕ) (hr : r < m) :
    siteA m a (4 * m + 3 + 4 * r) + baselineGapA m (switchEdgeNat m a (4 * m + 3 + 4 * r)) =
      siteA m a (4 * m + 4 + 4 * r) ∧
    siteA m a (4 * m + 4 + 4 * r) + baselineGapA m (switchEdgeNat m a (4 * m + 4 + 4 * r)) =
      siteA m a (4 * m + 5 + 4 * r) := by
  have hi : 4 * m + 3 + 4 * r = 4 * m + 2 * (2 * r + 1) + 1 := by omega
  have ho : 4 * m + 4 + 4 * r = 4 * m + 2 * (2 * r + 1) + 2 := by omega
  have hsite : siteA m a (4 * m + 4 + 4 * r) = upperA m a.2 (2 * r + 1) := by
    convert siteA_upper m a (2 * r + 1) using 1 <;> congr 1 <;> omega
  rw [(siteA_fixed m a r).1, (siteA_fixed m a r).2, hsite]
  rw [hi, ho, (switched_upper_A m hm a (2 * r + 1) (by omega) (by omega)).1,
    (switched_upper_A m hm a (2 * r + 1) (by omega) (by omega)).2]
  exact upperA_odd_distances m hm a.2 r hr

theorem A_upper_even_edges (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (r : ℕ) (hr : r + 1 < m) :
    siteA m a (4 * m + 5 + 4 * r) + baselineGapA m (switchEdgeNat m a (4 * m + 5 + 4 * r)) =
      siteA m a (4 * m + 6 + 4 * r) ∧
    siteA m a (4 * m + 6 + 4 * r) + baselineGapA m (switchEdgeNat m a (4 * m + 6 + 4 * r)) =
      siteA m a (4 * m + 7 + 4 * r) := by
  have hi : 4 * m + 5 + 4 * r = 4 * m + 2 * (2 * r + 2) + 1 := by omega
  have ho : 4 * m + 6 + 4 * r = 4 * m + 2 * (2 * r + 2) + 2 := by omega
  have hsite : siteA m a (4 * m + 6 + 4 * r) = upperA m a.2 (2 * r + 2) := by
    convert siteA_upper m a (2 * r + 2) using 1 <;> congr 1 <;> omega
  have hnext : siteA m a (4 * m + 7 + 4 * r) = fixedA m (r + 1) := by
    convert (siteA_fixed m a (r + 1)).1 using 1 <;> congr 1 <;> omega
  rw [(siteA_fixed m a r).2, hsite, hnext]
  rw [hi, ho, (switched_upper_A m hm a (2 * r + 2) (by omega) (by omega)).1,
    (switched_upper_A m hm a (2 * r + 2) (by omega) (by omega)).2]
  exact upperA_even_distances m hm a.2 r hr

theorem A_fixed_edges (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    siteA m a 0 + baselineGapA m (switchEdgeNat m a 0) = siteA m a 1 ∧
    siteA m a 1 + baselineGapA m (switchEdgeNat m a 1) = siteA m a 2 ∧
    siteA m a (4 * m) + baselineGapA m (switchEdgeNat m a (4 * m)) = siteA m a (4 * m + 1) ∧
    siteA m a (4 * m + 1) + baselineGapA m (switchEdgeNat m a (4 * m + 1)) = siteA m a (4 * m + 2) ∧
    siteA m a (4 * m + 2) + baselineGapA m (switchEdgeNat m a (4 * m + 2)) = siteA m a (4 * m + 3) ∧
    siteA m a (8 * m + 1) + baselineGapA m (switchEdgeNat m a (8 * m + 1)) = siteA m a (8 * m + 2) ∧
    siteA m a (8 * m + 2) + baselineGapA m (switchEdgeNat m a (8 * m + 2)) = clock m := by
  have hseam := A_fixed_seams m hm a
  have hgap := switched_A_fixed_gaps m hm a
  have h0 : siteA m a 0 = 0 := by simp [siteA]
  have h1 : siteA m a 1 = lowerA m a.1 0 := siteA_lower m a 0 (by omega)
  have h2 : siteA m a 2 = middleA m 1 := siteA_middle m a 1 (by omega) (by omega)
  have hlow : siteA m a (4 * m) = middleA m (2 * m) := by
    convert siteA_middle m a (2 * m) (by omega) (by omega) using 1 <;> congr 1 <;> omega
  have hlow' : siteA m a (4 * m + 1) = lowerA m a.1 (2 * m) := by
    convert siteA_lower m a (2 * m) (by omega) using 1 <;> congr 1 <;> omega
  have hu : siteA m a (4 * m + 2) = upperA m a.2 0 := by
    simpa using siteA_upper m a 0
  have hv : siteA m a (4 * m + 3) = fixedA m 0 := by simpa using (siteA_fixed m a 0).1
  have hlast : siteA m a (8 * m + 2) = upperA m a.2 (2 * m) := by
    convert siteA_upper m a (2 * m) using 1 <;> congr 1 <;> omega
  have hprev : siteA m a (8 * m + 1) = fixedA m (m - 1) + height m - 1 := by
    convert (siteA_fixed m a (m - 1)).2 using 1 <;> congr 1 <;> omega
  rw [h0, h1, h2, hlow, hlow', hu, hv, hlast, hprev,
    hgap.1, hgap.2.1, hgap.2.2.1, hgap.2.2.2.1, hgap.2.2.2.2.1,
    hgap.2.2.2.2.2.1, hgap.2.2.2.2.2.2]
  exact ⟨by simpa using hseam.1.symm, hseam.2⟩

/-- Every actual consecutive edge of D6 agrees with the simultaneous-switch
word. The final wrap is the last component of A_fixed_edges. -/
theorem siteA_succ (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (i : ℕ)
    (hi : i + 1 < order m) :
    siteA m a i + baselineGapA m (switchEdgeNat m a i) = siteA m a (i + 1) := by
  have hf := A_fixed_edges m hm a
  by_cases h0 : i = 0
  · simpa [h0] using hf.1
  by_cases h1 : i = 1
  · simpa [h1] using hf.2.1
  by_cases h4 : i = 4 * m
  · simpa [h4] using hf.2.2.1
  by_cases h41 : i = 4 * m + 1
  · simpa [h41] using hf.2.2.2.1
  by_cases h42 : i = 4 * m + 2
  · simpa [h42, Nat.add_assoc] using hf.2.2.2.2.1
  by_cases h81 : i = 8 * m + 1
  · simpa [h81, Nat.add_assoc] using hf.2.2.2.2.2.1
  by_cases hl : i < 4 * m
  · have hj0 : 0 < i / 2 := by omega
    have hj : i / 2 < 2 * m := by omega
    have he := A_lower_edges m hm a (i / 2) hj0 hj
    by_cases hp : i % 2 = 0
    · have heq : 2 * (i / 2) = i := by omega
      simpa only [heq] using he.1
    · have heq : 2 * (i / 2) + 1 = i := by omega
      have heq' : 2 * (i / 2) + 2 = i + 1 := by omega
      simpa only [heq, heq'] using he.2
  · have hil : 4 * m + 3 ≤ i := by omega
    have hih : i ≤ 8 * m := by unfold order at hi; omega
    let q := i - (4 * m + 3)
    by_cases hp : q % 4 = 0 ∨ q % 4 = 1
    · have hr : q / 4 < m := by dsimp [q]; omega
      have he := A_upper_odd_edges m hm a (q / 4) hr
      rcases hp with hp | hp
      · have heq : 4 * m + 3 + 4 * (q / 4) = i := by dsimp [q] at *; omega
        have heq' : 4 * m + 4 + 4 * (q / 4) = i + 1 := by omega
        simpa only [heq, heq'] using he.1
      · have heq : 4 * m + 4 + 4 * (q / 4) = i := by dsimp [q] at *; omega
        have heq' : 4 * m + 5 + 4 * (q / 4) = i + 1 := by omega
        simpa only [heq, heq'] using he.2
    · have hr : q / 4 + 1 < m := by dsimp [q] at *; omega
      have he := A_upper_even_edges m hm a (q / 4) hr
      by_cases hp' : q % 4 = 2
      · have heq : 4 * m + 5 + 4 * (q / 4) = i := by dsimp [q] at *; omega
        have heq' : 4 * m + 6 + 4 * (q / 4) = i + 1 := by omega
        simpa only [heq, heq'] using he.1
      · have heq : 4 * m + 6 + 4 * (q / 4) = i := by dsimp [q] at *; omega
        have heq' : 4 * m + 7 + 4 * (q / 4) = i + 1 := by omega
        simpa only [heq, heq'] using he.2

theorem switchedWordA_length (m : ℕ) (a : Choices m) :
    (switchedWordA m a).length = order m := by simp [switchedWordA]

theorem siteA_eq_prefix (m : ℕ) (hm : 1 ≤ m) (a : Choices m)
    (i : ℕ) (hi : i < order m) :
    siteA m a i = ((switchedWordA m a).take i).sum := by
  induction i with
  | zero => simp [siteA]
  | succ i ih =>
    have hi' : i < order m := by omega
    have hlen : i < (switchedWordA m a).length := by rw [switchedWordA_length]; exact hi'
    have hget : (switchedWordA m a)[i]'hlen = baselineGapA m (switchEdgeNat m a i) := by
      simp [switchedWordA, switchEdge]
    calc
      siteA m a (i + 1) = siteA m a i + baselineGapA m (switchEdgeNat m a i) :=
        (siteA_succ m hm a i hi).symm
      _ = ((switchedWordA m a).take i).sum + (switchedWordA m a)[i]'hlen := by rw [ih hi', hget]
      _ = ((switchedWordA m a).take (i + 1)).sum := (List.sum_take_succ _ _ hlen).symm

theorem optimal_width (m : ℕ) : width (order m) = clock m := by
  unfold width clock order height
  have hprod : (8 * m + 3) * (8 * m + 3 + 1) = ((4 * m + 2) * (8 * m + 3)) * 2 := by ring
  rw [hprod]
  simp

theorem switchedWordA_sum (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    (switchedWordA m a).sum = clock m := by
  rw [(switchedWordA_perm m hm a).sum_eq, fullGapList_sum, optimal_width]

theorem rowA_eq_properPrefixes (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    rowA m a = (properPrefixSites (switchedWordA m a)).toFinset := by
  rw [← siteA_image_eq_rowA]
  ext x
  simp only [Finset.mem_image, Finset.mem_range, List.mem_toFinset, mem_properPrefixSites_iff,
    switchedWordA_length]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, (siteA_eq_prefix m hm a i hi).symm.trans hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, (siteA_eq_prefix m hm a i hi).trans hx⟩

/-- Full validity of the literal switched A row (D4), for every independent
bit choice and every m>=1, including the actual physical wrap. -/
theorem rowA_gap_inventory (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    finiteCyclicGapInventory (clock m) (rowA m a) =
      Multiset.ofList (fullGapList (order m)) := by
  have hpos : ∀ x ∈ switchedWordA m a, 0 < x := by
    intro x hx
    exact (fullGapList_mem _ _).mp ((switchedWordA_perm m hm a).mem_iff.mp hx) |>.1
  have hne : switchedWordA m a ≠ [] := by
    intro h
    have hlen := switchedWordA_length m a
    simp [h, order] at hlen
  rw [rowA_eq_properPrefixes m hm a, ← switchedWordA_sum m hm a]
  cases hw : switchedWordA m a with
  | nil => exact False.elim (hne hw)
  | cons x xs =>
    have hpos' : ∀ z ∈ x :: xs, 0 < z := by simpa [hw] using hpos
    rw [properPrefixSites_finite_gaps x xs hpos']
    exact Multiset.coe_eq_coe.mpr (by simpa [hw] using switchedWordA_perm m hm a)

theorem rowA_bounded (m : ℕ) (hm : 1 ≤ m) (a : Choices m)
    (x : ℕ) (hx : x ∈ rowA m a) : x < clock m := by
  rw [rowA_eq_properPrefixes m hm a] at hx
  have hpos : ∀ z ∈ switchedWordA m a, 0 < z := by
    intro z hz
    exact ((fullGapList_mem _ _).mp ((switchedWordA_perm m hm a).mem_iff.mp hz)).1
  simpa [switchedWordA_sum m hm a] using
    properPrefixSites_lt_sum _ hpos x (List.mem_toFinset.mp hx)

end CorralFormalization.EvenSwitches
