import Pinwheel.WeakSeven
import Pinwheel.SevenStreams
import Pinwheel.WeakServiceTransport
import Pinwheel.WeakSevenBandData
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The analytic part of the WS7 tenth band

This module supplies the all-window source behind the four paired-price
guards and proves that one of those guards always succeeds above `5/44`.
The finite real-polytope coverage is assembled below from the R190/T244
certificates; it is kept separate from these analytic constructions.
-/

namespace RealPinwheel

open scoped BigOperators
open SevenStreams

def ws7PairLeftOne : List (Fin 7) := [1, 2]
def ws7PairRightOne : List (Fin 7) := [0, 3, 4, 0, 5, 6]

def ws7PairSideOne (i : Fin 7) : Prop := 1 ≤ i.val ∧ i.val ≤ 2
def ws7PairPeriodOne (i : Fin 7) : ℤ :=
  if i.val = 0 then 3 else if i.val ≤ 2 then 2 else 6
def ws7PairResidueOne (i : Fin 7) : ℤ :=
  if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 1
  else if i.val = 3 then 1 else if i.val = 4 then 2
  else if i.val = 5 then 4 else 5

def ws7PairLeftTwo : List (Fin 7) := [1, 2, 3, 4]
def ws7PairRightTwo : List (Fin 7) := [0, 5, 0, 6]

def ws7PairSideTwo (i : Fin 7) : Prop := 1 ≤ i.val ∧ i.val ≤ 4
def ws7PairPeriodTwo (i : Fin 7) : ℤ :=
  if i.val = 0 then 2 else if i.val ≤ 4 then 4 else 4
def ws7PairResidueTwo (i : Fin 7) : ℤ :=
  if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 1
  else if i.val = 3 then 2 else if i.val = 4 then 3
  else if i.val = 5 then 1 else 3

def ws7PairLeftThree : List (Fin 7) := [1, 2, 3, 4, 5, 6]
def ws7PairRightThree : List (Fin 7) := [0, 0]

def ws7PairSideThree (i : Fin 7) : Prop := 1 ≤ i.val ∧ i.val ≤ 6
def ws7PairPeriodThree (i : Fin 7) : ℤ :=
  if i.val = 0 then 1 else 6
def ws7PairResidueThree (i : Fin 7) : ℤ :=
  if i.val = 0 then 0 else (i.val : ℤ) - 1

private theorem ws7PairOne_left_periodic (i : Fin 7)
    (hi : ws7PairSideOne i) :
    SevenStreams.ListIndexPeriodic ws7PairLeftOne i (ws7PairPeriodOne i)
      (ws7PairResidueOne i) := by
  fin_cases i <;>
    simp [ws7PairSideOne, ws7PairPeriodOne, ws7PairResidueOne,
      ws7PairLeftOne, SevenStreams.ListIndexPeriodic] at hi ⊢

private theorem ws7PairOne_right_periodic (i : Fin 7)
    (hi : ¬ ws7PairSideOne i) :
    SevenStreams.ListIndexPeriodic ws7PairRightOne i (ws7PairPeriodOne i)
      (ws7PairResidueOne i) := by
  fin_cases i <;>
    simp [ws7PairSideOne, ws7PairPeriodOne, ws7PairResidueOne,
      ws7PairRightOne, SevenStreams.ListIndexPeriodic] at hi ⊢
  all_goals
    intro k
    fin_cases k <;> norm_num <;> decide

private theorem ws7PairTwo_left_periodic (i : Fin 7)
    (hi : ws7PairSideTwo i) :
    SevenStreams.ListIndexPeriodic ws7PairLeftTwo i (ws7PairPeriodTwo i)
      (ws7PairResidueTwo i) := by
  fin_cases i <;>
    simp [ws7PairSideTwo, ws7PairPeriodTwo, ws7PairResidueTwo,
      ws7PairLeftTwo, SevenStreams.ListIndexPeriodic] at hi ⊢
  all_goals
    intro k
    fin_cases k <;> norm_num <;> decide

private theorem ws7PairTwo_right_periodic (i : Fin 7)
    (hi : ¬ ws7PairSideTwo i) :
    SevenStreams.ListIndexPeriodic ws7PairRightTwo i (ws7PairPeriodTwo i)
      (ws7PairResidueTwo i) := by
  fin_cases i <;>
    simp [ws7PairSideTwo, ws7PairPeriodTwo, ws7PairResidueTwo,
      ws7PairRightTwo, SevenStreams.ListIndexPeriodic] at hi ⊢
  all_goals
    intro k
    fin_cases k <;> norm_num <;> decide

private theorem ws7PairThree_left_periodic (i : Fin 7)
    (hi : ws7PairSideThree i) :
    SevenStreams.ListIndexPeriodic ws7PairLeftThree i (ws7PairPeriodThree i)
      (ws7PairResidueThree i) := by
  fin_cases i <;>
    simp [ws7PairSideThree, ws7PairPeriodThree, ws7PairResidueThree,
      ws7PairLeftThree, SevenStreams.ListIndexPeriodic] at hi ⊢
  all_goals
    intro k
    fin_cases k <;> norm_num <;> decide

private theorem ws7PairThree_right_periodic (i : Fin 7)
    (hi : ¬ ws7PairSideThree i) :
    SevenStreams.ListIndexPeriodic ws7PairRightThree i (ws7PairPeriodThree i)
      (ws7PairResidueThree i) := by
  fin_cases i <;>
    simp [ws7PairSideThree, ws7PairPeriodThree, ws7PairResidueThree,
      ws7PairRightThree, SevenStreams.ListIndexPeriodic] at hi ⊢

private theorem ws7_heads_le_of_ordered {h : Fin 6 → ℝ}
    (ho : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (i : Fin 6) : h i ≤ h 0 := by
  exact ho 0 i (Nat.zero_le _)

private theorem ws7_head_later_le {h : Fin 6 → ℝ}
    (ho : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (i j : Fin 6) (hij : i.val ≤ j.val) : h j ≤ h i :=
  ho i j hij

private theorem ws7PairOne_left_load {h : Fin 6 → ℝ} {delta : ℝ}
    (ho : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (i : Fin 7) (hi : ws7PairSideOne i) :
    (ws7PairPeriodOne i : ℝ) * weakSevenRates h delta i ≤ 2 * h 0 := by
  fin_cases i
  · simp [ws7PairSideOne] at hi
  · have hrate : weakSevenRates h delta 1 = h 0 := by
      exact weakSevenRates_succ h delta 0
    change (ws7PairPeriodOne (1 : Fin 7) : ℝ) * weakSevenRates h delta 1 ≤ 2 * h 0
    rw [hrate]
    norm_num [ws7PairPeriodOne]
  · have hrate : weakSevenRates h delta 2 = h 1 := by
      exact weakSevenRates_succ h delta 1
    change (ws7PairPeriodOne (2 : Fin 7) : ℝ) * weakSevenRates h delta 2 ≤ 2 * h 0
    rw [hrate]
    norm_num [ws7PairPeriodOne]
    nlinarith [ho 0 1 (by norm_num)]
  · simp [ws7PairSideOne] at hi
  · simp [ws7PairSideOne] at hi
  · simp [ws7PairSideOne] at hi
  · simp [ws7PairSideOne] at hi

private theorem ws7PairOne_right_load {h : Fin 6 → ℝ} {delta : ℝ}
    (hheads : ∀ i, delta ≤ h i)
    (ho : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (i : Fin 7) (hi : ¬ ws7PairSideOne i) :
    (ws7PairPeriodOne i : ℝ) * weakSevenRates h delta i ≤ 6 * h 2 := by
  fin_cases i
  · have hrate : weakSevenRates h delta 0 = 2 * delta := by
      exact weakSevenRates_zero h delta
    change (ws7PairPeriodOne (0 : Fin 7) : ℝ) * weakSevenRates h delta 0 ≤ 6 * h 2
    rw [hrate]
    norm_num [ws7PairPeriodOne]
    nlinarith [hheads 2]
  · simp [ws7PairSideOne] at hi
  · simp [ws7PairSideOne] at hi
  · have hrate : weakSevenRates h delta 3 = h 2 := by
      exact weakSevenRates_succ h delta 2
    change (ws7PairPeriodOne (3 : Fin 7) : ℝ) * weakSevenRates h delta 3 ≤ 6 * h 2
    rw [hrate]
    norm_num [ws7PairPeriodOne]
  · have hrate : weakSevenRates h delta 4 = h 3 := by
      exact weakSevenRates_succ h delta 3
    change (ws7PairPeriodOne (4 : Fin 7) : ℝ) * weakSevenRates h delta 4 ≤ 6 * h 2
    rw [hrate]
    norm_num [ws7PairPeriodOne]
    nlinarith [ho 2 3 (by norm_num)]
  · have hrate : weakSevenRates h delta 5 = h 4 := by
      exact weakSevenRates_succ h delta 4
    change (ws7PairPeriodOne (5 : Fin 7) : ℝ) * weakSevenRates h delta 5 ≤ 6 * h 2
    rw [hrate]
    norm_num [ws7PairPeriodOne]
    nlinarith [ho 2 4 (by norm_num)]
  · have hrate : weakSevenRates h delta 6 = h 5 := by
      exact weakSevenRates_succ h delta 5
    change (ws7PairPeriodOne (6 : Fin 7) : ℝ) * weakSevenRates h delta 6 ≤ 6 * h 2
    rw [hrate]
    norm_num [ws7PairPeriodOne]
    nlinarith [ho 2 5 (by norm_num)]

private theorem ws7PairTwo_left_load {h : Fin 6 → ℝ} {delta : ℝ}
    (ho : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (i : Fin 7) (hi : ws7PairSideTwo i) :
    (ws7PairPeriodTwo i : ℝ) * weakSevenRates h delta i ≤ 4 * h 0 := by
  fin_cases i
  · simp [ws7PairSideTwo] at hi
  · have hrate : weakSevenRates h delta 1 = h 0 := by
      exact weakSevenRates_succ h delta 0
    change (ws7PairPeriodTwo (1 : Fin 7) : ℝ) * weakSevenRates h delta 1 ≤ 4 * h 0
    rw [hrate]
    norm_num [ws7PairPeriodTwo]
  · have hrate : weakSevenRates h delta 2 = h 1 := by
      exact weakSevenRates_succ h delta 1
    change (ws7PairPeriodTwo (2 : Fin 7) : ℝ) * weakSevenRates h delta 2 ≤ 4 * h 0
    rw [hrate]
    norm_num [ws7PairPeriodTwo]
    nlinarith [ho 0 1 (by norm_num)]
  · have hrate : weakSevenRates h delta 3 = h 2 := by
      exact weakSevenRates_succ h delta 2
    change (ws7PairPeriodTwo (3 : Fin 7) : ℝ) * weakSevenRates h delta 3 ≤ 4 * h 0
    rw [hrate]
    norm_num [ws7PairPeriodTwo]
    nlinarith [ho 0 2 (by norm_num)]
  · have hrate : weakSevenRates h delta 4 = h 3 := by
      exact weakSevenRates_succ h delta 3
    change (ws7PairPeriodTwo (4 : Fin 7) : ℝ) * weakSevenRates h delta 4 ≤ 4 * h 0
    rw [hrate]
    norm_num [ws7PairPeriodTwo]
    nlinarith [ho 0 3 (by norm_num)]
  · simp [ws7PairSideTwo] at hi
  · simp [ws7PairSideTwo] at hi

private theorem ws7PairTwo_right_load {h : Fin 6 → ℝ} {delta : ℝ}
    (hheads : ∀ i, delta ≤ h i)
    (ho : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (i : Fin 7) (hi : ¬ ws7PairSideTwo i) :
    (ws7PairPeriodTwo i : ℝ) * weakSevenRates h delta i ≤ 4 * h 4 := by
  fin_cases i
  · have hrate : weakSevenRates h delta 0 = 2 * delta := by
      exact weakSevenRates_zero h delta
    change (ws7PairPeriodTwo (0 : Fin 7) : ℝ) * weakSevenRates h delta 0 ≤ 4 * h 4
    rw [hrate]
    norm_num [ws7PairPeriodTwo]
    nlinarith [hheads 4]
  · simp [ws7PairSideTwo] at hi
  · simp [ws7PairSideTwo] at hi
  · simp [ws7PairSideTwo] at hi
  · simp [ws7PairSideTwo] at hi
  · have hrate : weakSevenRates h delta 5 = h 4 := by
      exact weakSevenRates_succ h delta 4
    change (ws7PairPeriodTwo (5 : Fin 7) : ℝ) * weakSevenRates h delta 5 ≤ 4 * h 4
    rw [hrate]
    norm_num [ws7PairPeriodTwo]
  · have hrate : weakSevenRates h delta 6 = h 5 := by
      exact weakSevenRates_succ h delta 5
    change (ws7PairPeriodTwo (6 : Fin 7) : ℝ) * weakSevenRates h delta 6 ≤ 4 * h 4
    rw [hrate]
    norm_num [ws7PairPeriodTwo]
    nlinarith [ho 4 5 (by norm_num)]

private theorem ws7PairThree_left_load {h : Fin 6 → ℝ} {delta : ℝ}
    (ho : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (i : Fin 7) (hi : ws7PairSideThree i) :
    (ws7PairPeriodThree i : ℝ) * weakSevenRates h delta i ≤ 6 * h 0 := by
  fin_cases i
  · simp [ws7PairSideThree] at hi
  · have hrate : weakSevenRates h delta 1 = h 0 := by
      exact weakSevenRates_succ h delta 0
    change (ws7PairPeriodThree (1 : Fin 7) : ℝ) * weakSevenRates h delta 1 ≤ 6 * h 0
    rw [hrate]
    norm_num [ws7PairPeriodThree]
  · have hrate : weakSevenRates h delta 2 = h 1 := by
      exact weakSevenRates_succ h delta 1
    change (ws7PairPeriodThree (2 : Fin 7) : ℝ) * weakSevenRates h delta 2 ≤ 6 * h 0
    rw [hrate]
    norm_num [ws7PairPeriodThree]
    nlinarith [ho 0 1 (by norm_num)]
  · have hrate : weakSevenRates h delta 3 = h 2 := by
      exact weakSevenRates_succ h delta 2
    change (ws7PairPeriodThree (3 : Fin 7) : ℝ) * weakSevenRates h delta 3 ≤ 6 * h 0
    rw [hrate]
    norm_num [ws7PairPeriodThree]
    nlinarith [ho 0 2 (by norm_num)]
  · have hrate : weakSevenRates h delta 4 = h 3 := by
      exact weakSevenRates_succ h delta 3
    change (ws7PairPeriodThree (4 : Fin 7) : ℝ) * weakSevenRates h delta 4 ≤ 6 * h 0
    rw [hrate]
    norm_num [ws7PairPeriodThree]
    nlinarith [ho 0 3 (by norm_num)]
  · have hrate : weakSevenRates h delta 5 = h 4 := by
      exact weakSevenRates_succ h delta 4
    change (ws7PairPeriodThree (5 : Fin 7) : ℝ) * weakSevenRates h delta 5 ≤ 6 * h 0
    rw [hrate]
    norm_num [ws7PairPeriodThree]
    nlinarith [ho 0 4 (by norm_num)]
  · have hrate : weakSevenRates h delta 6 = h 5 := by
      exact weakSevenRates_succ h delta 5
    change (ws7PairPeriodThree (6 : Fin 7) : ℝ) * weakSevenRates h delta 6 ≤ 6 * h 0
    rw [hrate]
    norm_num [ws7PairPeriodThree]
    nlinarith [ho 0 5 (by norm_num)]

private theorem ws7PairThree_right_load {h : Fin 6 → ℝ} {delta : ℝ}
    (i : Fin 7) (hi : ¬ ws7PairSideThree i) :
    (ws7PairPeriodThree i : ℝ) * weakSevenRates h delta i ≤ 2 * delta := by
  fin_cases i
  · have hrate : weakSevenRates h delta 0 = 2 * delta := by
      exact weakSevenRates_zero h delta
    change (ws7PairPeriodThree (0 : Fin 7) : ℝ) * weakSevenRates h delta 0 ≤ 2 * delta
    rw [hrate]
    norm_num [ws7PairPeriodThree]
  · simp [ws7PairSideThree] at hi
  · simp [ws7PairSideThree] at hi
  · simp [ws7PairSideThree] at hi
  · simp [ws7PairSideThree] at hi
  · simp [ws7PairSideThree] at hi
  · simp [ws7PairSideThree] at hi

private theorem ws7_pair_source_one {h : Fin 6 → ℝ} {delta : ℝ}
    (hdelta : (1 : ℝ) / 10 ≤ delta)
    (hheads : ∀ i, delta ≤ h i)
    (hordered : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (hprice : 2 * h 0 + 6 * h 2 ≤ 1) :
    SchedulableRates (weakSevenRates h delta) := by
  have hdpos : 0 < delta := by linarith
  have hpos : ∀ i, 0 < h i := fun i => lt_of_lt_of_le hdpos (hheads i)
  have hr : ∀ i : Fin 7, 0 < weakSevenRates h delta i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp [weakSevenRates]
      linarith
    · intro j
      simp [weakSevenRates]
      exact hpos j
  have hdisjoint : List.Disjoint ws7PairLeftOne ws7PairRightOne := by
    apply List.disjoint_left.mpr
    intro x hx hy
    simp [ws7PairLeftOne] at hx
    rcases hx with hx | hx
    · subst x
      simp [ws7PairRightOne] at hy
    · subst x
      simp [ws7PairRightOne] at hy
  apply list_stream_schedulable_of_pair_loads
    ws7PairLeftOne ws7PairRightOne (by simp [ws7PairLeftOne])
    (by simp [ws7PairRightOne]) hdisjoint
    ws7PairSideOne ws7PairPeriodOne ws7PairResidueOne
    ws7PairOne_left_periodic ws7PairOne_right_periodic
    (by exact ⟨1, by norm_num [ws7PairSideOne]⟩)
    (by exact ⟨0, by norm_num [ws7PairSideOne]⟩)
    (weakSevenRates h delta) hr ?_
  intro i j hi hj
  have hleft : (ws7PairPeriodOne i : ℝ) * weakSevenRates h delta i ≤
      2 * h 0 := ws7PairOne_left_load hordered i hi
  have hright : (ws7PairPeriodOne j : ℝ) * weakSevenRates h delta j ≤
      6 * h 2 := ws7PairOne_right_load hheads hordered j hj
  calc
    (ws7PairPeriodOne i : ℝ) * weakSevenRates h delta i +
        (ws7PairPeriodOne j : ℝ) * weakSevenRates h delta j ≤
      2 * h 0 + 6 * h 2 := add_le_add hleft hright
    _ ≤ 1 := hprice

private theorem ws7_pair_source_two {h : Fin 6 → ℝ} {delta : ℝ}
    (hdelta : (1 : ℝ) / 10 ≤ delta)
    (hheads : ∀ i, delta ≤ h i)
    (hordered : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (hprice : 4 * h 0 + 4 * h 4 ≤ 1) :
    SchedulableRates (weakSevenRates h delta) := by
  have hdpos : 0 < delta := by linarith
  have hpos : ∀ i, 0 < h i := fun i => lt_of_lt_of_le hdpos (hheads i)
  have hr : ∀ i : Fin 7, 0 < weakSevenRates h delta i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp [weakSevenRates]
      linarith
    · intro j
      simp [weakSevenRates]
      exact hpos j
  have hdisjoint : List.Disjoint ws7PairLeftTwo ws7PairRightTwo := by
    apply List.disjoint_left.mpr
    intro x hx hy
    simp [ws7PairLeftTwo] at hx
    rcases hx with hx | hx | hx | hx
    · subst x
      simp [ws7PairRightTwo] at hy
    · subst x
      simp [ws7PairRightTwo] at hy
    · subst x
      simp [ws7PairRightTwo] at hy
    · subst x
      simp [ws7PairRightTwo] at hy
  apply list_stream_schedulable_of_pair_loads
    ws7PairLeftTwo ws7PairRightTwo (by simp [ws7PairLeftTwo])
    (by simp [ws7PairRightTwo]) hdisjoint
    ws7PairSideTwo ws7PairPeriodTwo ws7PairResidueTwo
    ws7PairTwo_left_periodic ws7PairTwo_right_periodic
    (by exact ⟨1, by norm_num [ws7PairSideTwo]⟩)
    (by exact ⟨0, by norm_num [ws7PairSideTwo]⟩)
    (weakSevenRates h delta) hr ?_
  intro i j hi hj
  have hleft : (ws7PairPeriodTwo i : ℝ) * weakSevenRates h delta i ≤
      4 * h 0 := ws7PairTwo_left_load hordered i hi
  have hright : (ws7PairPeriodTwo j : ℝ) * weakSevenRates h delta j ≤
      4 * h 4 := ws7PairTwo_right_load hheads hordered j hj
  calc
    (ws7PairPeriodTwo i : ℝ) * weakSevenRates h delta i +
        (ws7PairPeriodTwo j : ℝ) * weakSevenRates h delta j ≤
      4 * h 0 + 4 * h 4 := add_le_add hleft hright
    _ ≤ 1 := hprice

private theorem ws7_pair_source_three {h : Fin 6 → ℝ} {delta : ℝ}
    (hdelta : (1 : ℝ) / 10 ≤ delta)
    (hheads : ∀ i, delta ≤ h i)
    (hordered : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (hprice : 6 * h 0 + 2 * delta ≤ 1) :
    SchedulableRates (weakSevenRates h delta) := by
  have hdpos : 0 < delta := by linarith
  have hpos : ∀ i, 0 < h i := fun i => lt_of_lt_of_le hdpos (hheads i)
  have hr : ∀ i : Fin 7, 0 < weakSevenRates h delta i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp [weakSevenRates]
      linarith
    · intro j
      simp [weakSevenRates]
      exact hpos j
  have hdisjoint : List.Disjoint ws7PairLeftThree ws7PairRightThree := by
    apply List.disjoint_left.mpr
    intro x hx hy
    simp [ws7PairLeftThree] at hx
    rcases hx with hx | hx | hx | hx | hx | hx
    · subst x
      simp [ws7PairRightThree] at hy
    · subst x
      simp [ws7PairRightThree] at hy
    · subst x
      simp [ws7PairRightThree] at hy
    · subst x
      simp [ws7PairRightThree] at hy
    · subst x
      simp [ws7PairRightThree] at hy
    · subst x
      simp [ws7PairRightThree] at hy
  apply list_stream_schedulable_of_pair_loads
    ws7PairLeftThree ws7PairRightThree (by simp [ws7PairLeftThree])
    (by simp [ws7PairRightThree]) hdisjoint
    ws7PairSideThree ws7PairPeriodThree ws7PairResidueThree
    ws7PairThree_left_periodic ws7PairThree_right_periodic
    (by exact ⟨1, by norm_num [ws7PairSideThree]⟩)
    (by exact ⟨0, by norm_num [ws7PairSideThree]⟩)
    (weakSevenRates h delta) hr ?_
  intro i j hi hj
  have hleft : (ws7PairPeriodThree i : ℝ) * weakSevenRates h delta i ≤
      6 * h 0 := ws7PairThree_left_load hordered i hi
  have hright : (ws7PairPeriodThree j : ℝ) * weakSevenRates h delta j ≤
      2 * delta := ws7PairThree_right_load j hj
  calc
    (ws7PairPeriodThree i : ℝ) * weakSevenRates h delta i +
        (ws7PairPeriodThree j : ℝ) * weakSevenRates h delta j ≤
      6 * h 0 + 2 * delta := add_le_add hleft hright
    _ ≤ 1 := hprice

/-- Four exact paired prices cover the ordinary source of the WS7 roles.
The first price is weakened to the second because `h₂ ≤ h₁`; the other three
prices use respectively one, two, or three paired head groups on the first
mechanical stream. -/
theorem weakSeven_paired_source
    {h : Fin 6 → ℝ} {delta : ℝ}
    (hdelta : (1 : ℝ) / 10 ≤ delta)
    (hheads : ∀ i, delta ≤ h i)
    (hordered : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (hprice : 8 * h 0 ≤ 1 ∨
      2 * h 0 + 6 * h 2 ≤ 1 ∨
      4 * h 0 + 4 * h 4 ≤ 1 ∨
      6 * h 0 + 2 * delta ≤ 1) :
    SchedulableRates (weakSevenRates h delta) := by
  rcases hprice with h0 | h1 | h2 | h3
  · apply ws7_pair_source_one hdelta hheads hordered
    nlinarith [hordered 0 2 (by norm_num), h0]
  · exact ws7_pair_source_one hdelta hheads hordered h1
  · exact ws7_pair_source_two hdelta hheads hordered h2
  · exact ws7_pair_source_three hdelta hheads hordered h3

/-- Analytic upper band. The weighted average of pair prices two and three is
at most `2 - 44*delta/5`, so one actual source succeeds for `delta≥5/44`. -/
theorem weakSeven_upper_pair_source
    {h : Fin 6 → ℝ} {delta : ℝ}
    (hdelta : (5 : ℝ) / 44 ≤ delta)
    (hheads : ∀ i, delta ≤ h i)
    (hsimplex : (∑ i : Fin 6, h i) + delta = (5 : ℝ) / 6)
    (hordered : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) :
    SchedulableRates (weakSevenRates h delta) := by
  let e : Fin 6 → ℝ := fun i => h i - delta
  have he_nonneg : ∀ i, 0 ≤ e i := by
    intro i
    dsimp [e]
    exact sub_nonneg.mpr (hheads i)
  have he_sum : (∑ i : Fin 6, e i) = (5 : ℝ) / 6 - 7 * delta := by
    rw [Fin.sum_univ_six]
    dsimp [e]
    have hs := hsimplex
    rw [Fin.sum_univ_six] at hs
    linarith
  have he12 : e 2 ≤ e 1 := by
    dsimp [e]
    exact sub_le_sub_right (hordered 1 2 (by norm_num)) delta
  have hebound : 12 * e 0 + 24 * e 2 + 4 * e 4 ≤
      12 * (∑ i : Fin 6, e i) := by
    rw [Fin.sum_univ_six]
    nlinarith [he12, he_nonneg 3, he_nonneg 4, he_nonneg 5]
  have havg : (4 : ℝ) / 5 * (2 * h 0 + 6 * h 2) +
      (1 : ℝ) / 5 * (4 * h 0 + 4 * h 4) ≤ 1 := by
    have hexpand :
        (4 : ℝ) / 5 * (2 * h 0 + 6 * h 2) +
          (1 : ℝ) / 5 * (4 * h 0 + 4 * h 4) =
          8 * delta + (12 * e 0 + 24 * e 2 + 4 * e 4) / 5 := by
      dsimp [e]
      ring
    rw [hexpand]
    rw [he_sum] at hebound
    have hlin : 8 * delta + (12 * e 0 + 24 * e 2 + 4 * e 4) / 5 ≤
        8 * delta + (12 * ((5 : ℝ) / 6 - 7 * delta)) / 5 := by
      nlinarith [hebound]
    have hdeltaBound : 8 * delta +
        (12 * ((5 : ℝ) / 6 - 7 * delta)) / 5 ≤ 1 := by
      nlinarith [hdelta]
    exact hlin.trans hdeltaBound
  have hchoice : 2 * h 0 + 6 * h 2 ≤ 1 ∨
      4 * h 0 + 4 * h 4 ≤ 1 := by
    by_contra hn
    push Not at hn
    have hfirst : 1 < 2 * h 0 + 6 * h 2 := hn.1
    have hsecond : 1 < 4 * h 0 + 4 * h 4 := hn.2
    nlinarith [havg]
  rcases hchoice with hp1 | hp2
  · exact weakSeven_paired_source (by linarith [hdelta]) hheads hordered
      (Or.inr (Or.inl hp1))
  · exact weakSeven_paired_source (by linarith [hdelta]) hheads hordered
      (Or.inr (Or.inr (Or.inl hp2)))

private theorem ws7_sorted_low_band_of_covers
    {h : Fin 6 → ℝ} {delta : ℝ}
    (hdelta : (1 : ℝ) / 10 ≤ delta)
    (hupper : delta ≤ (5 : ℝ) / 44)
    (hheads : ∀ i, delta ≤ h i)
    (hsimplex : (∑ i : Fin 6, h i) + delta = (5 : ℝ) / 6)
    (hordered : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (newLargest : (h 0 ≤ 2 * delta) → delta ≤ (5 : ℝ) / 48 →
      (1 < 8 * h 0 ∧ 1 < 2 * h 0 + 6 * h 2 ∧
        1 < 4 * h 0 + 4 * h 4 ∧ 1 < 6 * h 0 + 2 * delta) →
      ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S)
    (upperLargest : (5 : ℝ) / 48 ≤ delta → delta ≤ (5 : ℝ) / 44 →
      (1 < 8 * h 0 ∧ 1 < 2 * h 0 + 6 * h 2 ∧
        1 < 4 * h 0 + 4 * h 4 ∧ 1 < 6 * h 0 + 2 * delta) →
      ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S)
    (secondLargest : 2 * delta ≤ h 0 → h 1 ≤ 2 * delta →
      delta ≤ (5 : ℝ) / 44 →
      (1 < 8 * h 0 ∧ 1 < 2 * h 0 + 6 * h 2 ∧
        1 < 4 * h 0 + 4 * h 4 ∧ 1 < 6 * h 0 + 2 * delta) →
      ∃ S : ℤ → Fin 7,
        WeakValidRates
          (fun i => weakSevenRates h delta (Equiv.swap (0 : Fin 7) 1 i)) S) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  by_cases hpair : 8 * h 0 ≤ 1 ∨ 2 * h 0 + 6 * h 2 ≤ 1 ∨
      4 * h 0 + 4 * h 4 ≤ 1 ∨ 6 * h 0 + 2 * delta ≤ 1
  · obtain ⟨S, hS⟩ := weakSeven_paired_source hdelta hheads hordered hpair
    exact ⟨S, ValidRates.toWeakValidRates hS⟩
  · have hfail : 1 < 8 * h 0 ∧ 1 < 2 * h 0 + 6 * h 2 ∧
        1 < 4 * h 0 + 4 * h 4 ∧ 1 < 6 * h 0 + 2 * delta := by
      push Not at hpair
      exact hpair
    by_cases hmark : h 0 ≤ 2 * delta
    · by_cases hsmall : delta ≤ (5 : ℝ) / 48
      · exact newLargest hmark hsmall hfail
      · exact upperLargest (le_of_not_ge hsmall) hupper hfail
    · have hmark0 : 2 * delta ≤ h 0 := by
        have hlt := lt_of_not_ge hmark
        linarith
      have hmark1 : h 1 ≤ 2 * delta := by
        by_contra hn
        have hmark1Lower : 2 * delta ≤ h 1 := le_of_not_ge hn
        have hsumExpanded :
            h 0 + h 1 + h 2 + h 3 + h 4 + h 5 + delta = (5 : ℝ) / 6 := by
          simpa only [Fin.sum_univ_six] using hsimplex
        nlinarith [hheads 2, hheads 3, hheads 4, hheads 5]
      obtain ⟨S, hS⟩ := secondLargest hmark0 hmark1 hupper hfail
      refine ⟨fun t => Equiv.swap (0 : Fin 7) 1 (S t), ?_⟩
      exact WeakValidRates.relabel (Equiv.swap (0 : Fin 7) 1) hS

/-- Stable decreasing sort of the six head rates.  `Tuple.sort` sorts the
negated rates increasingly, leaving equal rates in any harmless order. -/
noncomputable def ws7HeadSort (h : Fin 6 → ℝ) : Equiv.Perm (Fin 6) :=
  Tuple.sort (fun i => -h i)

noncomputable def ws7SortedHeads (h : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun i => h (ws7HeadSort h i)

theorem ws7SortedHeads_antitone (h : Fin 6 → ℝ) :
    Antitone (ws7SortedHeads h) := by
  intro i j hij
  change h (ws7HeadSort h j) ≤ h (ws7HeadSort h i)
  have hh := Tuple.monotone_sort (fun k : Fin 6 => -h k) hij
  have hh' : -(h (ws7HeadSort h i)) ≤ -(h (ws7HeadSort h j)) := by
    simpa [ws7HeadSort, Function.comp_apply] using hh
  linarith

theorem ws7SortedHeads_sum (h : Fin 6 → ℝ) :
    (∑ i : Fin 6, ws7SortedHeads h i) = ∑ i : Fin 6, h i := by
  exact Equiv.sum_comp (ws7HeadSort h) h

/-- Relabel sorted head roles back to their original six labels, fixing the
distinguished mark at role zero. -/
def ws7HeadRoleRelabel (sigma : Equiv.Perm (Fin 6)) : Fin 7 ≃ Fin 7 :=
  (finSumFinEquiv (m := 1) (n := 6)).symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin 1)) sigma).trans
      (finSumFinEquiv (m := 1) (n := 6)))

theorem ws7HeadRoleRelabel_zero (sigma : Equiv.Perm (Fin 6)) :
    ws7HeadRoleRelabel sigma 0 = 0 := by
  unfold ws7HeadRoleRelabel
  rw [Equiv.trans_apply, Equiv.trans_apply]
  rw [show (0 : Fin 7) = Fin.castAdd 6 (0 : Fin 1) by rfl]
  rw [finSumFinEquiv_symm_apply_castAdd]
  rw [Equiv.sumCongr_apply]
  simp only [Sum.map_inl]
  rw [finSumFinEquiv_apply_left]
  simp only [Equiv.refl_apply]

theorem ws7HeadRoleRelabel_succ (sigma : Equiv.Perm (Fin 6)) (i : Fin 6) :
    ws7HeadRoleRelabel sigma i.succ = (sigma i).succ := by
  unfold ws7HeadRoleRelabel
  rw [Equiv.trans_apply, Equiv.trans_apply]
  rw [show i.succ = Fin.natAdd 1 i by
    apply Fin.ext
    simp [Fin.natAdd]
    omega]
  rw [finSumFinEquiv_symm_apply_natAdd]
  rw [Equiv.sumCongr_apply]
  simp only [Sum.map_inr]
  rw [finSumFinEquiv_apply_right]
  apply Fin.ext
  simp [Fin.natAdd]
  omega

theorem ws7SortedRoleRates_eq_relabel
    (h : Fin 6 → ℝ) (delta : ℝ) :
    (fun i : Fin 7 => weakSevenRates (ws7SortedHeads h) delta i) =
      (fun i : Fin 7 => weakSevenRates h delta (ws7HeadRoleRelabel (ws7HeadSort h) i)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [weakSevenRates, ws7HeadRoleRelabel_zero]
  · intro j
    simp [weakSevenRates, ws7SortedHeads, ws7HeadRoleRelabel_succ]

theorem ws7SortedWeakSource_relabel
    {h : Fin 6 → ℝ} {delta : ℝ} {S : ℤ → Fin 7}
    (hS : WeakValidRates (weakSevenRates (ws7SortedHeads h) delta) S) :
    WeakValidRates (weakSevenRates h delta)
      (fun t => ws7HeadRoleRelabel (ws7HeadSort h) (S t)) := by
  have hrate := ws7SortedRoleRates_eq_relabel h delta
  change WeakValidRates (fun i => weakSevenRates (ws7SortedHeads h) delta i) S at hS
  rw [hrate] at hS
  exact WeakValidRates.relabel (ws7HeadRoleRelabel (ws7HeadSort h)) hS

private theorem ws7SortedWeakSource_exists_relabel
    {h : Fin 6 → ℝ} {delta : ℝ}
    (hS : ∃ S : ℤ → Fin 7,
      WeakValidRates (weakSevenRates (ws7SortedHeads h) delta) S) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  obtain ⟨S, hS⟩ := hS
  exact ⟨fun t => ws7HeadRoleRelabel (ws7HeadSort h) (S t),
    ws7SortedWeakSource_relabel hS⟩

/-- Every seven-role WS7 point with at least one tenth of marked slack has a
single weak all-window schedule.  The strict paired sources handle all points
where one actual price succeeds; the certified covers handle the four strict
failure branches below the analytic upper band. -/
theorem weakSeven_tenth_band
    {h : Fin 6 → ℝ} {delta : ℝ}
    (hdelta : (1 : ℝ) / 10 ≤ delta)
    (hheads : ∀ i, delta ≤ h i)
    (hsimplex : (∑ i : Fin 6, h i) + delta = (5 : ℝ) / 6) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  let hs := ws7SortedHeads h
  have hsHeads : ∀ i, delta ≤ hs i := by
    intro i
    exact hheads (ws7HeadSort h i)
  have hsSimplex : (∑ i : Fin 6, hs i) + delta = (5 : ℝ) / 6 := by
    rw [ws7SortedHeads_sum]
    exact hsimplex
  have hsOrder : ∀ i j : Fin 6, i.val ≤ j.val → hs j ≤ hs i := by
    intro i j hij
    exact ws7SortedHeads_antitone h (Fin.le_def.mpr hij)
  by_cases hlarge : (5 : ℝ) / 44 ≤ delta
  · obtain ⟨S, hS⟩ := weakSeven_upper_pair_source hlarge hsHeads hsSimplex hsOrder
    exact ws7SortedWeakSource_exists_relabel
      ⟨S, ValidRates.toWeakValidRates hS⟩
  · have hsmallUpper : delta ≤ (5 : ℝ) / 44 := le_of_lt (lt_of_not_ge hlarge)
    have hsortedSource := ws7_sorted_low_band_of_covers
      hdelta hsmallUpper hsHeads hsSimplex hsOrder
      (by
        intro hmark hupper hfail
        rcases hfail with ⟨hf0, hf1, hf2, hf3⟩
        exact WeakSevenBandData.new_largest_cover hs delta hsOrder hsHeads hsSimplex
          hdelta hupper hf0 hf1 hf2 hf3 hmark)
      (by
        intro hlower hupper hfail
        rcases hfail with ⟨hf0, hf1, hf2, hf3⟩
        exact WeakSevenBandData.upper_largest_cover hs delta hsOrder hsHeads hsSimplex
          hlower hupper hf0 hf1 hf2 hf3)
      (by
        intro hmark0 hmark1 hupper hfail
        rcases hfail with ⟨hf0, hf1, hf2, hf3⟩
        exact WeakSevenBandData.second_cover hs delta hsOrder hsHeads hsSimplex
          hdelta hupper hf0 hf1 hf2 hf3 hmark0 hmark1)
    exact ws7SortedWeakSource_exists_relabel hsortedSource

/-- Ordinary marked-source corollary from the tenth band.  The pointwise
balance hypothesis is equivalent to `B ≤ 2 * min y` on this finite alphabet. -/
theorem weakSeven_ordinary_marked_source
    {y : Fin 7 → ℝ} (mark : Fin 7)
    (hypos : ∀ i, 0 < y i)
    (T : ℝ)
    (hsum : (∑ i : Fin 7, y i) = T)
    (hbalanced : ∀ i, y mark ≤ 2 * y i)
    (hdiscount : T - y mark / 2 < (5 : ℝ) / 6)
    (hratio : (3 : ℝ) * T / 14 ≤ y mark) :
    SchedulableRates y := by
  classical
  let align : Fin 7 ≃ Fin 7 := Equiv.swap 0 mark
  have halign_zero : align 0 = mark := by simp [align]
  let C : ℝ := T - y mark / 2
  have hmark_le_sum : y mark ≤ ∑ i : Fin 7, y i :=
    Finset.single_le_sum (fun i _ => (hypos i).le) (Finset.mem_univ mark)
  have hhalf : y mark / 2 < y mark := by nlinarith [hypos mark]
  have hCpos : 0 < C := by
    dsimp [C]
    nlinarith [hmark_le_sum, hsum, hhalf]
  have hClt : C < (5 : ℝ) / 6 := by
    dsimp [C]
    exact hdiscount
  let lambda : ℝ := ((5 : ℝ) / 6) / C
  have hlambda_pos : 0 < lambda := by
    dsimp [lambda]
    positivity
  have hlambda_gt_one : 1 < lambda := by
    dsimp [lambda]
    apply (lt_div_iff₀ hCpos).2
    simpa using hClt
  let delta : ℝ := lambda * y mark / 2
  let heads : Fin 6 → ℝ := fun i => lambda * y (align i.succ)
  have hcross : 6 * C ≤ 25 * y mark := by
    dsimp [C]
    nlinarith [hratio]
  have hdelta_eq : delta = 5 * y mark / (12 * C) := by
    dsimp [delta, lambda]
    field_simp [ne_of_gt hCpos]
    ring
  have hdelta : (1 : ℝ) / 10 ≤ delta := by
    rw [hdelta_eq]
    apply (le_div_iff₀ (mul_pos (by norm_num) hCpos)).2
    nlinarith [hcross]
  have hheads : ∀ i, delta ≤ heads i := by
    intro i
    have hbalance_i := hbalanced (align i.succ)
    dsimp [delta, heads]
    nlinarith [mul_le_mul_of_nonneg_left hbalance_i hlambda_pos.le]
  have hsumAlignment :
      y mark + (∑ i : Fin 6, y (align i.succ)) = ∑ i : Fin 7, y i := by
    have hp := Equiv.sum_comp align y
    rw [Fin.sum_univ_succ] at hp
    simpa [halign_zero] using hp
  have hsumHeads : (∑ i : Fin 6, y (align i.succ)) + y mark / 2 = C := by
    dsimp [C]
    nlinarith [hsum, hsumAlignment]
  have hsimplex : (∑ i : Fin 6, heads i) + delta = (5 : ℝ) / 6 := by
    have hscale :
        (∑ i : Fin 6, lambda * y (align i.succ)) +
          lambda * y mark / 2 = lambda * C := by
      calc
        (∑ i : Fin 6, lambda * y (align i.succ)) + lambda * y mark / 2 =
            lambda * (∑ i : Fin 6, y (align i.succ)) + lambda * (y mark / 2) := by
              rw [← Finset.mul_sum]
              ring
        _ = lambda * ((∑ i : Fin 6, y (align i.succ)) + y mark / 2) := by ring
        _ = lambda * C := by rw [hsumHeads]
    dsimp [heads, delta, lambda]
    rw [show
      (∑ i : Fin 6, lambda * y (align i.succ)) + lambda * y mark / 2 =
        lambda * C from hscale]
    dsimp [lambda]
    field_simp [ne_of_gt hCpos]
  obtain ⟨W, hW⟩ := weakSeven_tenth_band hdelta hheads hsimplex
  have hweak_strict : ∀ i : Fin 7,
      y (align i) < weakSevenRates heads delta i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp only [weakSevenRates_zero]
      dsimp [delta]
      simp [align, halign_zero]
      nlinarith [mul_lt_mul_of_pos_right hlambda_gt_one (hypos mark)]
    · intro j
      simpa [weakSevenRates, heads] using
        (mul_lt_mul_of_pos_right hlambda_gt_one (hypos (align j.succ)))
  have hordinary : ValidRates (fun i => y (align i)) W :=
    WeakValidRates.toValidRates_of_strictly_smaller hW hweak_strict
  exact SchedulableRates.relabel align ⟨W, hordinary⟩

end RealPinwheel
