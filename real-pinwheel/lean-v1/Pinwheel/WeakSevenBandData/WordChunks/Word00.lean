import Pinwheel.WeakPeriodicPath

/-! Literal R190/T244 words and kernel-checked debt paths. -/

set_option maxHeartbeats 15000000
set_option maxRecDepth 50000

namespace RealPinwheel
namespace WeakSevenBandData

def ws7Word0 : List (Fin 7) := [1, 0, 4, 6, 1, 3, 0, 2, 5, 1, 0, 4, 6, 1, 3, 0, 2, 5]

def ws7WordP0 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ0 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 9
  | 2 => 9
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ0 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5]
  | 1 => [8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8]
  | 2 => [1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1]
  | 3 => [3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3]
  | 4 => [6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6]
  | 5 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0]
  | 6 => [5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5]
  | _ => []

theorem ws7Word0Weak :
    WeakValidRates (fun i => (ws7WordP0 i : ℝ) / (ws7WordQ0 i : ℝ))
      (periodic ws7Word0.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word0)) := by
  apply weakPeriodic_of_paths ws7Word0 (by decide) ws7WordP0 ws7WordQ0
    (by intro i; fin_cases i <;> norm_num [ws7WordQ0]) ws7WordZ0
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word1 : List (Fin 7) := [6, 5, 0, 1, 2, 4, 0, 3, 6, 1, 5, 0, 2, 4, 1, 3, 0, 6, 5, 2, 1, 0, 4, 3]

def ws7WordP1 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ1 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 24
  | 1 => 6
  | 2 => 8
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | _ => 1

def ws7WordZ1 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [13, 18, 23, 4, 9, 14, 19, 0, 5, 10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13]
  | 1 => [3, 4, 5, 6, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3]
  | 2 => [4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4]
  | 3 => [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0]
  | 4 => [2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2]
  | 5 => [6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6]
  | 6 => [7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7]
  | _ => []

theorem ws7Word1Weak :
    WeakValidRates (fun i => (ws7WordP1 i : ℝ) / (ws7WordQ1 i : ℝ))
      (periodic ws7Word1.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word1)) := by
  apply weakPeriodic_of_paths ws7Word1 (by decide) ws7WordP1 ws7WordQ1
    (by intro i; fin_cases i <;> norm_num [ws7WordQ1]) ws7WordZ1
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word2 : List (Fin 7) := [2, 0, 3, 1, 4, 5, 0, 6, 1, 2, 3, 0, 4, 1, 5, 6, 0, 2, 1, 3, 4, 0, 5, 1, 6]

def ws7WordP2 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

def ws7WordQ2 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 5
  | 2 => 25
  | 3 => 25
  | 4 => 25
  | 5 => 25
  | 6 => 25
  | _ => 1

def ws7WordZ2 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3]
  | 1 => [1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1]
  | 2 => [22, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22]
  | 3 => [17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17]
  | 4 => [12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 0, 3, 6, 9, 12]
  | 5 => [7, 10, 13, 16, 19, 22, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7]
  | 6 => [2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2]
  | _ => []

theorem ws7Word2Weak :
    WeakValidRates (fun i => (ws7WordP2 i : ℝ) / (ws7WordQ2 i : ℝ))
      (periodic ws7Word2.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word2)) := by
  apply weakPeriodic_of_paths ws7Word2 (by decide) ws7WordP2 ws7WordQ2
    (by intro i; fin_cases i <;> norm_num [ws7WordQ2]) ws7WordZ2
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word3 : List (Fin 7) := [1, 2, 0, 3, 4, 1, 5, 0, 6, 2, 1, 0, 3, 4, 5, 0, 1, 6, 2, 0, 3, 1, 4, 5, 0, 6]

def ws7WordP3 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 5
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

def ws7WordQ3 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 13
  | 1 => 26
  | 2 => 26
  | 3 => 26
  | 4 => 26
  | 5 => 26
  | 6 => 26
  | _ => 1

def ws7WordZ3 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [5, 8, 11, 1, 4, 7, 10, 13, 3, 6, 9, 12, 2, 5, 8, 11, 1, 4, 7, 10, 0, 3, 6, 9, 12, 2, 5]
  | 1 => [23, 2, 7, 12, 17, 22, 1, 6, 11, 16, 21, 0, 5, 10, 15, 20, 25, 4, 9, 14, 19, 24, 3, 8, 13, 18, 23]
  | 2 => [22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22]
  | 3 => [15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15]
  | 4 => [11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11]
  | 5 => [7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7]
  | 6 => [0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 0]
  | _ => []

theorem ws7Word3Weak :
    WeakValidRates (fun i => (ws7WordP3 i : ℝ) / (ws7WordQ3 i : ℝ))
      (periodic ws7Word3.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word3)) := by
  apply weakPeriodic_of_paths ws7Word3 (by decide) ws7WordP3 ws7WordQ3
    (by intro i; fin_cases i <;> norm_num [ws7WordQ3]) ws7WordZ3
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word4 : List (Fin 7) := [0, 6, 3, 1, 0, 2, 4, 5, 1, 3, 0, 6, 2, 0, 1, 4, 3, 5, 0, 2, 1, 6, 3, 0, 4, 1, 2, 5]

def ws7WordP4 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 5
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | 5 => 2
  | 6 => 2
  | _ => 0

def ws7WordQ4 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 28
  | 2 => 7
  | 3 => 7
  | 4 => 28
  | 5 => 19
  | 6 => 19
  | _ => 1

def ws7WordZ4 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 1, 2, 3, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4]
  | 1 => [11, 16, 21, 26, 3, 8, 13, 18, 23, 0, 5, 10, 15, 20, 25, 2, 7, 12, 17, 22, 27, 4, 9, 14, 19, 24, 1, 6, 11]
  | 2 => [1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1]
  | 3 => [5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5]
  | 4 => [9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 0, 3, 6, 9]
  | 5 => [2, 4, 6, 8, 10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2]
  | 6 => [14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14]
  | _ => []

theorem ws7Word4Weak :
    WeakValidRates (fun i => (ws7WordP4 i : ℝ) / (ws7WordQ4 i : ℝ))
      (periodic ws7Word4.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word4)) := by
  apply weakPeriodic_of_paths ws7Word4 (by decide) ws7WordP4 ws7WordQ4
    (by intro i; fin_cases i <;> norm_num [ws7WordQ4]) ws7WordZ4
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word5 : List (Fin 7) := [2, 0, 3, 1, 5, 0, 6, 2, 1, 4, 0, 3, 1, 5, 2, 0, 6, 1, 4, 0, 2, 3, 1, 5, 0, 6, 1, 4]

def ws7WordP5 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 3
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

def ws7WordQ5 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 14
  | 1 => 14
  | 2 => 7
  | 3 => 28
  | 4 => 28
  | 5 => 28
  | 6 => 28
  | _ => 1

def ws7WordZ5 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [10, 13, 2, 5, 8, 11, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 0, 3, 6, 9, 12, 1, 4, 7, 10]
  | 1 => [3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 0, 3]
  | 2 => [7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7]
  | 3 => [20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20]
  | 4 => [0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 0]
  | 5 => [14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14]
  | 6 => [7, 10, 13, 16, 19, 22, 25, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7]
  | _ => []

theorem ws7Word5Weak :
    WeakValidRates (fun i => (ws7WordP5 i : ℝ) / (ws7WordQ5 i : ℝ))
      (periodic ws7Word5.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word5)) := by
  apply weakPeriodic_of_paths ws7Word5 (by decide) ws7WordP5 ws7WordQ5
    (by intro i; fin_cases i <;> norm_num [ws7WordQ5]) ws7WordZ5
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word6 : List (Fin 7) := [2, 0, 4, 6, 1, 0, 3, 2, 5, 0, 1, 4, 3, 6, 0, 2, 1, 5, 3, 0, 4, 2, 1, 6, 0, 3, 5, 1]

def ws7WordP6 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 4
  | 1 => 3
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | 5 => 3
  | 6 => 2
  | _ => 0

def ws7WordQ6 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 19
  | 1 => 17
  | 2 => 7
  | 3 => 8
  | 4 => 28
  | 5 => 28
  | 6 => 19
  | _ => 1

def ws7WordZ6 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [15, 19, 4, 8, 12, 16, 1, 5, 9, 13, 0, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 18, 3, 7, 11, 15]
  | 1 => [1, 4, 7, 10, 13, 0, 3, 6, 9, 12, 15, 1, 4, 7, 10, 13, 16, 2, 5, 8, 11, 14, 17, 3, 6, 9, 12, 15, 1]
  | 2 => [6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6]
  | 3 => [2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2]
  | 4 => [21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 0, 3, 6, 9, 12, 15, 18, 21]
  | 5 => [3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 0, 3]
  | 6 => [10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10]
  | _ => []

theorem ws7Word6Weak :
    WeakValidRates (fun i => (ws7WordP6 i : ℝ) / (ws7WordQ6 i : ℝ))
      (periodic ws7Word6.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word6)) := by
  apply weakPeriodic_of_paths ws7Word6 (by decide) ws7WordP6 ws7WordQ6
    (by intro i; fin_cases i <;> norm_num [ws7WordQ6]) ws7WordZ6
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word7 : List (Fin 7) := [3, 0, 6, 4, 1, 2, 0, 3, 5, 1, 0, 2, 6, 4, 3, 0, 1, 5, 2, 0, 6, 1, 4, 3, 0, 2, 5, 1]

def ws7WordP7 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | 5 => 3
  | 6 => 2
  | _ => 0

def ws7WordQ7 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 14
  | 1 => 6
  | 2 => 7
  | 3 => 8
  | 4 => 28
  | 5 => 28
  | 6 => 19
  | _ => 1

def ws7WordZ7 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 0, 3, 6, 9, 12, 1, 4, 7, 10]
  | 1 => [0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0]
  | 2 => [2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2]
  | 3 => [5, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5]
  | 4 => [16, 19, 22, 25, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16]
  | 5 => [3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 0, 3]
  | 6 => [14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14]
  | _ => []

theorem ws7Word7Weak :
    WeakValidRates (fun i => (ws7WordP7 i : ℝ) / (ws7WordQ7 i : ℝ))
      (periodic ws7Word7.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word7)) := by
  apply weakPeriodic_of_paths ws7Word7 (by decide) ws7WordP7 ws7WordQ7
    (by intro i; fin_cases i <;> norm_num [ws7WordQ7]) ws7WordZ7
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word8 : List (Fin 7) := [0, 3, 1, 2, 4, 0, 1, 5, 3, 6, 0, 2, 1, 4, 3, 0, 1, 5, 2, 6, 0, 1, 3, 4, 0, 2, 1, 5, 6]

def ws7WordP8 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 6
  | 1 => 1
  | 2 => 4
  | 3 => 2
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

def ws7WordQ8 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 29
  | 1 => 5
  | 2 => 29
  | 3 => 15
  | 4 => 29
  | 5 => 29
  | 6 => 29
  | _ => 1

def ws7WordZ8 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [24, 1, 7, 13, 19, 25, 2, 8, 14, 20, 26, 3, 9, 15, 21, 27, 4, 10, 16, 22, 28, 5, 11, 17, 23, 0, 6, 12, 18, 24]
  | 1 => [2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2]
  | 2 => [13, 17, 21, 25, 0, 4, 8, 12, 16, 20, 24, 28, 3, 7, 11, 15, 19, 23, 27, 2, 6, 10, 14, 18, 22, 26, 1, 5, 9, 13]
  | 3 => [13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13]
  | 4 => [16, 19, 22, 25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13, 16]
  | 5 => [5, 8, 11, 14, 17, 20, 23, 26, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 2, 5]
  | 6 => [0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26, 0]
  | _ => []

theorem ws7Word8Weak :
    WeakValidRates (fun i => (ws7WordP8 i : ℝ) / (ws7WordQ8 i : ℝ))
      (periodic ws7Word8.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word8)) := by
  apply weakPeriodic_of_paths ws7Word8 (by decide) ws7WordP8 ws7WordQ8
    (by intro i; fin_cases i <;> norm_num [ws7WordQ8]) ws7WordZ8
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word9 : List (Fin 7) := [1, 4, 3, 2, 0, 5, 1, 6, 2, 0, 3, 4, 1, 0, 2, 5, 6, 3, 1, 0, 4, 2, 0, 1, 5, 3, 6, 2, 0]

def ws7WordP9 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 5
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

def ws7WordQ9 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 29
  | 2 => 6
  | 3 => 22
  | 4 => 29
  | 5 => 29
  | 6 => 29
  | _ => 1

def ws7WordZ9 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 0, 1, 2, 3, 4, 5, 1]
  | 1 => [25, 1, 6, 11, 16, 21, 26, 2, 7, 12, 17, 22, 27, 3, 8, 13, 18, 23, 28, 4, 9, 14, 19, 24, 0, 5, 10, 15, 20, 25]
  | 2 => [2, 3, 4, 5, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 6, 1, 2]
  | 3 => [12, 15, 18, 0, 3, 6, 9, 12, 15, 18, 21, 2, 5, 8, 11, 14, 17, 20, 1, 4, 7, 10, 13, 16, 19, 22, 3, 6, 9, 12]
  | 4 => [24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26, 0, 3, 6, 9, 12, 15, 18, 21, 24]
  | 5 => [12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26, 0, 3, 6, 9, 12]
  | 6 => [7, 10, 13, 16, 19, 22, 25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7]
  | _ => []

theorem ws7Word9Weak :
    WeakValidRates (fun i => (ws7WordP9 i : ℝ) / (ws7WordQ9 i : ℝ))
      (periodic ws7Word9.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word9)) := by
  apply weakPeriodic_of_paths ws7Word9 (by decide) ws7WordP9 ws7WordQ9
    (by intro i; fin_cases i <;> norm_num [ws7WordQ9]) ws7WordZ9
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word10 : List (Fin 7) := [1, 6, 4, 0, 2, 1, 5, 3, 0, 4, 6, 1, 2, 0, 3, 5, 4, 1, 0, 2, 6, 3, 0, 1, 4, 5, 2, 0, 3]

def ws7WordP10 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 6
  | 1 => 5
  | 2 => 4
  | 3 => 4
  | 4 => 4
  | 5 => 3
  | 6 => 3
  | _ => 0

def ws7WordQ10 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 29
  | 1 => 29
  | 2 => 29
  | 3 => 29
  | 4 => 29
  | 5 => 29
  | 6 => 29
  | _ => 1

def ws7WordZ10 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [7, 13, 19, 25, 2, 8, 14, 20, 26, 3, 9, 15, 21, 27, 4, 10, 16, 22, 28, 5, 11, 17, 23, 0, 6, 12, 18, 24, 1, 7]
  | 1 => [28, 4, 9, 14, 19, 24, 0, 5, 10, 15, 20, 25, 1, 6, 11, 16, 21, 26, 2, 7, 12, 17, 22, 27, 3, 8, 13, 18, 23, 28]
  | 2 => [9, 13, 17, 21, 25, 0, 4, 8, 12, 16, 20, 24, 28, 3, 7, 11, 15, 19, 23, 27, 2, 6, 10, 14, 18, 22, 26, 1, 5, 9]
  | 3 => [0, 4, 8, 12, 16, 20, 24, 28, 3, 7, 11, 15, 19, 23, 27, 2, 6, 10, 14, 18, 22, 26, 1, 5, 9, 13, 17, 21, 25, 0]
  | 4 => [19, 23, 27, 2, 6, 10, 14, 18, 22, 26, 1, 5, 9, 13, 17, 21, 25, 0, 4, 8, 12, 16, 20, 24, 28, 3, 7, 11, 15, 19]
  | 5 => [10, 13, 16, 19, 22, 25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10]
  | 6 => [25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 25]
  | _ => []

theorem ws7Word10Weak :
    WeakValidRates (fun i => (ws7WordP10 i : ℝ) / (ws7WordQ10 i : ℝ))
      (periodic ws7Word10.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word10)) := by
  apply weakPeriodic_of_paths ws7Word10 (by decide) ws7WordP10 ws7WordQ10
    (by intro i; fin_cases i <;> norm_num [ws7WordQ10]) ws7WordZ10
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word11 : List (Fin 7) := [3, 2, 0, 5, 1, 6, 2, 0, 3, 4, 1, 2, 0, 5, 6, 1, 3, 0, 2, 4, 1, 0, 5, 3, 6, 2, 0, 1, 4]

def ws7WordP11 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 6
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

def ws7WordQ11 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 29
  | 1 => 6
  | 2 => 13
  | 3 => 15
  | 4 => 29
  | 5 => 29
  | 6 => 29
  | _ => 1

def ws7WordZ11 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [13, 19, 25, 2, 8, 14, 20, 26, 3, 9, 15, 21, 27, 4, 10, 16, 22, 28, 5, 11, 17, 23, 0, 6, 12, 18, 24, 1, 7, 13]
  | 1 => [2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 6, 1, 2]
  | 2 => [8, 10, 0, 2, 4, 6, 8, 0, 2, 4, 6, 8, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8]
  | 3 => [11, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11]
  | 4 => [0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26, 0]
  | 5 => [18, 21, 24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26, 0, 3, 6, 9, 12, 15, 18]
  | 6 => [13, 16, 19, 22, 25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13]
  | _ => []

theorem ws7Word11Weak :
    WeakValidRates (fun i => (ws7WordP11 i : ℝ) / (ws7WordQ11 i : ℝ))
      (periodic ws7Word11.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word11)) := by
  apply weakPeriodic_of_paths ws7Word11 (by decide) ws7WordP11 ws7WordQ11
    (by intro i; fin_cases i <;> norm_num [ws7WordQ11]) ws7WordZ11
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word12 : List (Fin 7) := [1, 6, 3, 2, 0, 1, 4, 5, 3, 0, 2, 6, 1, 0, 3, 2, 4, 1, 5, 0, 6, 3, 2, 0, 1, 4, 3, 2, 5, 0]

def ws7WordP12 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ12 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 6
  | 2 => 6
  | 3 => 6
  | 4 => 10
  | 5 => 10
  | 6 => 10
  | _ => 1

def ws7WordZ12 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1]
  | 1 => [6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 6]
  | 2 => [2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2]
  | 3 => [3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3]
  | 4 => [4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4]
  | 5 => [2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2]
  | 6 => [9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  | _ => []

theorem ws7Word12Weak :
    WeakValidRates (fun i => (ws7WordP12 i : ℝ) / (ws7WordQ12 i : ℝ))
      (periodic ws7Word12.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word12)) := by
  apply weakPeriodic_of_paths ws7Word12 (by decide) ws7WordP12 ws7WordQ12
    (by intro i; fin_cases i <;> norm_num [ws7WordQ12]) ws7WordZ12
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word13 : List (Fin 7) := [1, 6, 5, 0, 3, 4, 1, 2, 0, 5, 6, 3, 1, 4, 0, 2, 5, 1, 0, 3, 4, 6, 2, 0, 1, 5, 3, 4, 0, 2]

def ws7WordP13 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ13 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 6
  | 2 => 15
  | 3 => 15
  | 4 => 15
  | 5 => 8
  | 6 => 10
  | _ => 1

def ws7WordZ13 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1]
  | 1 => [6, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 6]
  | 2 => [0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0]
  | 3 => [6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6]
  | 4 => [4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4]
  | 5 => [5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5]
  | 6 => [9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  | _ => []

theorem ws7Word13Weak :
    WeakValidRates (fun i => (ws7WordP13 i : ℝ) / (ws7WordQ13 i : ℝ))
      (periodic ws7Word13.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word13)) := by
  apply weakPeriodic_of_paths ws7Word13 (by decide) ws7WordP13 ws7WordQ13
    (by intro i; fin_cases i <;> norm_num [ws7WordQ13]) ws7WordZ13
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word14 : List (Fin 7) := [3, 0, 2, 4, 1, 0, 6, 5, 3, 2, 0, 1, 4, 6, 0, 5, 3, 2, 1, 0, 4, 6, 5, 0, 1, 3, 2, 4, 0, 6, 1, 5]

def ws7WordP14 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 2
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ14 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 32
  | 1 => 13
  | 2 => 8
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | _ => 1

def ws7WordZ14 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [24, 31, 6, 13, 20, 27, 2, 9, 16, 23, 30, 5, 12, 19, 26, 1, 8, 15, 22, 29, 4, 11, 18, 25, 0, 7, 14, 21, 28, 3, 10, 17, 24]
  | 1 => [2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2]
  | 2 => [6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6]
  | 3 => [7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7]
  | 4 => [4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4]
  | 5 => [1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1]
  | 6 => [2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2]
  | _ => []

theorem ws7Word14Weak :
    WeakValidRates (fun i => (ws7WordP14 i : ℝ) / (ws7WordQ14 i : ℝ))
      (periodic ws7Word14.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word14)) := by
  apply weakPeriodic_of_paths ws7Word14 (by decide) ws7WordP14 ws7WordQ14
    (by intro i; fin_cases i <;> norm_num [ws7WordQ14]) ws7WordZ14
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word15 : List (Fin 7) := [1, 3, 0, 5, 2, 4, 0, 1, 6, 3, 2, 0, 5, 4, 1, 6, 0, 2, 3, 5, 1, 0, 4, 6, 2, 0, 3, 1, 5, 4, 0, 2, 6]

def ws7WordP15 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 5
  | 2 => 3
  | 3 => 4
  | 4 => 3
  | 5 => 3
  | 6 => 2
  | _ => 0

def ws7WordQ15 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 33
  | 1 => 33
  | 2 => 20
  | 3 => 33
  | 4 => 25
  | 5 => 25
  | 6 => 17
  | _ => 1

def ws7WordZ15 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [17, 24, 31, 5, 12, 19, 26, 0, 7, 14, 21, 28, 2, 9, 16, 23, 30, 4, 11, 18, 25, 32, 6, 13, 20, 27, 1, 8, 15, 22, 29, 3, 10, 17]
  | 1 => [28, 0, 5, 10, 15, 20, 25, 30, 2, 7, 12, 17, 22, 27, 32, 4, 9, 14, 19, 24, 29, 1, 6, 11, 16, 21, 26, 31, 3, 8, 13, 18, 23, 28]
  | 2 => [6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 20, 3, 6]
  | 3 => [26, 30, 1, 5, 9, 13, 17, 21, 25, 29, 0, 4, 8, 12, 16, 20, 24, 28, 32, 3, 7, 11, 15, 19, 23, 27, 31, 2, 6, 10, 14, 18, 22, 26]
  | 4 => [9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9]
  | 5 => [14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14]
  | 6 => [1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1]
  | _ => []

theorem ws7Word15Weak :
    WeakValidRates (fun i => (ws7WordP15 i : ℝ) / (ws7WordQ15 i : ℝ))
      (periodic ws7Word15.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word15)) := by
  apply weakPeriodic_of_paths ws7Word15 (by decide) ws7WordP15 ws7WordQ15
    (by intro i; fin_cases i <;> norm_num [ws7WordQ15]) ws7WordZ15
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word16 : List (Fin 7) := [6, 0, 1, 2, 4, 5, 0, 3, 1, 6, 0, 2, 4, 1, 5, 0, 3, 6, 1, 2, 0, 4, 5, 3, 1, 0, 6, 2, 4, 0, 1, 5, 3]

def ws7WordP16 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 2
  | 2 => 4
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

def ws7WordQ16 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 33
  | 1 => 11
  | 2 => 33
  | 3 => 25
  | 4 => 25
  | 5 => 25
  | 6 => 25
  | _ => 1

def ws7WordZ16 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [22, 29, 3, 10, 17, 24, 31, 5, 12, 19, 26, 0, 7, 14, 21, 28, 2, 9, 16, 23, 30, 4, 11, 18, 25, 32, 6, 13, 20, 27, 1, 8, 15, 22]
  | 1 => [6, 8, 10, 1, 3, 5, 7, 9, 11, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11, 2, 4, 6]
  | 2 => [20, 24, 28, 32, 3, 7, 11, 15, 19, 23, 27, 31, 2, 6, 10, 14, 18, 22, 26, 30, 1, 5, 9, 13, 17, 21, 25, 29, 0, 4, 8, 12, 16, 20]
  | 3 => [2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2]
  | 4 => [12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12]
  | 5 => [6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 6]
  | 6 => [21, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21]
  | _ => []

theorem ws7Word16Weak :
    WeakValidRates (fun i => (ws7WordP16 i : ℝ) / (ws7WordQ16 i : ℝ))
      (periodic ws7Word16.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word16)) := by
  apply weakPeriodic_of_paths ws7Word16 (by decide) ws7WordP16 ws7WordQ16
    (by intro i; fin_cases i <;> norm_num [ws7WordQ16]) ws7WordZ16
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word17 : List (Fin 7) := [1, 5, 3, 4, 0, 2, 1, 6, 5, 0, 3, 1, 4, 2, 0, 6, 1, 5, 3, 0, 2, 4, 1, 6, 0, 5, 2, 3, 1, 0, 4, 6, 2, 0]

def ws7WordP17 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 4
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ17 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 34
  | 1 => 23
  | 2 => 7
  | 3 => 17
  | 4 => 26
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ17 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [0, 7, 14, 21, 28, 1, 8, 15, 22, 29, 2, 9, 16, 23, 30, 3, 10, 17, 24, 31, 4, 11, 18, 25, 32, 5, 12, 19, 26, 33, 6, 13, 20, 27, 0]
  | 1 => [22, 3, 7, 11, 15, 19, 23, 4, 8, 12, 16, 20, 1, 5, 9, 13, 17, 0, 4, 8, 12, 16, 20, 1, 5, 9, 13, 17, 21, 2, 6, 10, 14, 18, 22]
  | 2 => [1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1]
  | 3 => [13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13]
  | 4 => [12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 26, 3, 6, 9, 12]
  | 5 => [8, 9, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8]
  | 6 => [2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2]
  | _ => []

theorem ws7Word17Weak :
    WeakValidRates (fun i => (ws7WordP17 i : ℝ) / (ws7WordQ17 i : ℝ))
      (periodic ws7Word17.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word17)) := by
  apply weakPeriodic_of_paths ws7Word17 (by decide) ws7WordP17 ws7WordQ17
    (by intro i; fin_cases i <;> norm_num [ws7WordQ17]) ws7WordZ17
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word18 : List (Fin 7) := [5, 6, 0, 3, 2, 4, 1, 0, 5, 3, 6, 2, 0, 1, 4, 3, 0, 5, 2, 6, 1, 0, 4, 3, 2, 5, 0, 1, 6, 3, 4, 0, 2, 1]

def ws7WordP18 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 5
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | _ => 0

def ws7WordQ18 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 34
  | 1 => 34
  | 2 => 7
  | 3 => 7
  | 4 => 17
  | 5 => 17
  | 6 => 26
  | _ => 1

def ws7WordZ18 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [17, 24, 31, 4, 11, 18, 25, 32, 5, 12, 19, 26, 33, 6, 13, 20, 27, 0, 7, 14, 21, 28, 1, 8, 15, 22, 29, 2, 9, 16, 23, 30, 3, 10, 17]
  | 1 => [0, 5, 10, 15, 20, 25, 30, 1, 6, 11, 16, 21, 26, 31, 2, 7, 12, 17, 22, 27, 32, 3, 8, 13, 18, 23, 28, 33, 4, 9, 14, 19, 24, 29, 0]
  | 2 => [2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2]
  | 3 => [4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4]
  | 4 => [6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6]
  | 5 => [16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 16]
  | 6 => [18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 26, 3, 6, 9, 12, 15, 18]
  | _ => []

theorem ws7Word18Weak :
    WeakValidRates (fun i => (ws7WordP18 i : ℝ) / (ws7WordQ18 i : ℝ))
      (periodic ws7Word18.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word18)) := by
  apply weakPeriodic_of_paths ws7Word18 (by decide) ws7WordP18 ws7WordQ18
    (by intro i; fin_cases i <;> norm_num [ws7WordQ18]) ws7WordZ18
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word19 : List (Fin 7) := [6, 1, 0, 5, 3, 2, 4, 0, 1, 6, 2, 5, 0, 3, 1, 4, 6, 0, 2, 1, 5, 3, 0, 4, 1, 6, 2, 0, 5, 3, 1, 4, 0, 2]

def ws7WordP19 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | _ => 0

def ws7WordQ19 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 34
  | 1 => 6
  | 2 => 15
  | 3 => 17
  | 4 => 17
  | 5 => 17
  | 6 => 26
  | _ => 1

def ws7WordZ19 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [13, 20, 27, 0, 7, 14, 21, 28, 1, 8, 15, 22, 29, 2, 9, 16, 23, 30, 3, 10, 17, 24, 31, 4, 11, 18, 25, 32, 5, 12, 19, 26, 33, 6, 13]
  | 1 => [3, 4, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3]
  | 2 => [1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1]
  | 3 => [8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8]
  | 4 => [4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4]
  | 5 => [10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10]
  | 6 => [25, 2, 5, 8, 11, 14, 17, 20, 23, 26, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25]
  | _ => []

theorem ws7Word19Weak :
    WeakValidRates (fun i => (ws7WordP19 i : ℝ) / (ws7WordQ19 i : ℝ))
      (periodic ws7Word19.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word19)) := by
  apply weakPeriodic_of_paths ws7Word19 (by decide) ws7WordP19 ws7WordQ19
    (by intro i; fin_cases i <;> norm_num [ws7WordQ19]) ws7WordZ19
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word20 : List (Fin 7) := [0, 3, 6, 2, 0, 1, 5, 4, 0, 3, 2, 6, 1, 0, 5, 3, 4, 0, 2, 1, 6, 0, 3, 5, 4, 2, 0, 1, 3, 6, 0, 2, 5, 4, 1]

def ws7WordP20 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 8
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

def ws7WordQ20 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 35
  | 1 => 7
  | 2 => 7
  | 3 => 15
  | 4 => 35
  | 5 => 35
  | 6 => 35
  | _ => 1

def ws7WordZ20 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [34, 7, 15, 23, 31, 4, 12, 20, 28, 1, 9, 17, 25, 33, 6, 14, 22, 30, 3, 11, 19, 27, 0, 8, 16, 24, 32, 5, 13, 21, 29, 2, 10, 18, 26, 34]
  | 1 => [1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1]
  | 2 => [3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3]
  | 3 => [12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 12]
  | 4 => [5, 9, 13, 17, 21, 25, 29, 33, 2, 6, 10, 14, 18, 22, 26, 30, 34, 3, 7, 11, 15, 19, 23, 27, 31, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5]
  | 5 => [10, 14, 18, 22, 26, 30, 34, 3, 7, 11, 15, 19, 23, 27, 31, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 29, 33, 2, 6, 10]
  | 6 => [23, 27, 31, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 29, 33, 2, 6, 10, 14, 18, 22, 26, 30, 34, 3, 7, 11, 15, 19, 23]
  | _ => []

theorem ws7Word20Weak :
    WeakValidRates (fun i => (ws7WordP20 i : ℝ) / (ws7WordQ20 i : ℝ))
      (periodic ws7Word20.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word20)) := by
  apply weakPeriodic_of_paths ws7Word20 (by decide) ws7WordP20 ws7WordQ20
    (by intro i; fin_cases i <;> norm_num [ws7WordQ20]) ws7WordZ20
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word21 : List (Fin 7) := [1, 2, 5, 0, 3, 4, 1, 0, 2, 6, 5, 0, 1, 3, 4, 2, 0, 6, 1, 5, 0, 2, 3, 4, 1, 0, 6, 5, 2, 0, 1, 3, 4, 0, 6]

def ws7WordP21 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 8
  | 1 => 6
  | 2 => 1
  | 3 => 4
  | 4 => 4
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ21 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 35
  | 1 => 35
  | 2 => 7
  | 3 => 35
  | 4 => 35
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ21 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [9, 17, 25, 33, 6, 14, 22, 30, 3, 11, 19, 27, 0, 8, 16, 24, 32, 5, 13, 21, 29, 2, 10, 18, 26, 34, 7, 15, 23, 31, 4, 12, 20, 28, 1, 9]
  | 1 => [29, 0, 6, 12, 18, 24, 30, 1, 7, 13, 19, 25, 31, 2, 8, 14, 20, 26, 32, 3, 9, 15, 21, 27, 33, 4, 10, 16, 22, 28, 34, 5, 11, 17, 23, 29]
  | 2 => [6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6]
  | 3 => [15, 19, 23, 27, 31, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 29, 33, 2, 6, 10, 14, 18, 22, 26, 30, 34, 3, 7, 11, 15]
  | 4 => [11, 15, 19, 23, 27, 31, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 29, 33, 2, 6, 10, 14, 18, 22, 26, 30, 34, 3, 7, 11]
  | 5 => [7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]
  | 6 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0]
  | _ => []

theorem ws7Word21Weak :
    WeakValidRates (fun i => (ws7WordP21 i : ℝ) / (ws7WordQ21 i : ℝ))
      (periodic ws7Word21.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word21)) := by
  apply weakPeriodic_of_paths ws7Word21 (by decide) ws7WordP21 ws7WordQ21
    (by intro i; fin_cases i <;> norm_num [ws7WordQ21]) ws7WordZ21
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word22 : List (Fin 7) := [2, 4, 1, 5, 0, 3, 6, 2, 1, 0, 4, 3, 5, 0, 1, 2, 6, 3, 4, 0, 1, 5, 2, 0, 6, 3, 1, 4, 2, 0, 5, 1, 3, 6, 0]

def ws7WordP22 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 6
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 1
  | _ => 0

def ws7WordQ22 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 35
  | 2 => 7
  | 3 => 22
  | 4 => 35
  | 5 => 35
  | 6 => 9
  | _ => 1

def ws7WordZ22 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1]
  | 1 => [18, 24, 30, 1, 7, 13, 19, 25, 31, 2, 8, 14, 20, 26, 32, 3, 9, 15, 21, 27, 33, 4, 10, 16, 22, 28, 34, 5, 11, 17, 23, 29, 0, 6, 12, 18]
  | 2 => [6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6]
  | 3 => [7, 10, 13, 16, 19, 22, 3, 6, 9, 12, 15, 18, 0, 3, 6, 9, 12, 15, 0, 3, 6, 9, 12, 15, 18, 21, 2, 5, 8, 11, 14, 17, 20, 1, 4, 7]
  | 4 => [29, 33, 2, 6, 10, 14, 18, 22, 26, 30, 34, 3, 7, 11, 15, 19, 23, 27, 31, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 29]
  | 5 => [19, 23, 27, 31, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 29, 33, 2, 6, 10, 14, 18, 22, 26, 30, 34, 3, 7, 11, 15, 19]
  | 6 => [1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1]
  | _ => []

theorem ws7Word22Weak :
    WeakValidRates (fun i => (ws7WordP22 i : ℝ) / (ws7WordQ22 i : ℝ))
      (periodic ws7Word22.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word22)) := by
  apply weakPeriodic_of_paths ws7Word22 (by decide) ws7WordP22 ws7WordQ22
    (by intro i; fin_cases i <;> norm_num [ws7WordQ22]) ws7WordZ22
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word23 : List (Fin 7) := [3, 6, 0, 2, 4, 1, 5, 0, 3, 6, 2, 1, 0, 4, 5, 3, 0, 1, 2, 6, 4, 0, 3, 1, 5, 2, 0, 6, 1, 3, 4, 2, 0, 5, 1]

def ws7WordP23 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 6
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ23 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 35
  | 2 => 7
  | 3 => 7
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ23 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3]
  | 1 => [1, 7, 13, 19, 25, 31, 2, 8, 14, 20, 26, 32, 3, 9, 15, 21, 27, 33, 4, 10, 16, 22, 28, 34, 5, 11, 17, 23, 29, 0, 6, 12, 18, 24, 30, 1]
  | 2 => [3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3]
  | 3 => [6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6]
  | 4 => [5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5]
  | 5 => [2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2]
  | 6 => [7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7]
  | _ => []

theorem ws7Word23Weak :
    WeakValidRates (fun i => (ws7WordP23 i : ℝ) / (ws7WordQ23 i : ℝ))
      (periodic ws7Word23.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word23)) := by
  apply weakPeriodic_of_paths ws7Word23 (by decide) ws7WordP23 ws7WordQ23
    (by intro i; fin_cases i <;> norm_num [ws7WordQ23]) ws7WordZ23
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word24 : List (Fin 7) := [4, 6, 0, 2, 3, 1, 5, 0, 4, 6, 1, 2, 0, 3, 5, 0, 1, 4, 2, 6, 0, 3, 1, 5, 0, 2, 4, 6, 1, 0, 3, 2, 5, 0, 1]

def ws7WordP24 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 2
  | 1 => 6
  | 2 => 1
  | 3 => 4
  | 4 => 4
  | 5 => 4
  | 6 => 1
  | _ => 0

def ws7WordQ24 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 35
  | 2 => 7
  | 3 => 35
  | 4 => 35
  | 5 => 35
  | 6 => 9
  | _ => 1

def ws7WordZ24 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [2, 4, 6, 0, 2, 4, 6, 8, 1, 3, 5, 7, 9, 2, 4, 6, 0, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2]
  | 1 => [4, 10, 16, 22, 28, 34, 5, 11, 17, 23, 29, 0, 6, 12, 18, 24, 30, 1, 7, 13, 19, 25, 31, 2, 8, 14, 20, 26, 32, 3, 9, 15, 21, 27, 33, 4]
  | 2 => [3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3]
  | 3 => [17, 21, 25, 29, 33, 2, 6, 10, 14, 18, 22, 26, 30, 34, 3, 7, 11, 15, 19, 23, 27, 31, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17]
  | 4 => [34, 3, 7, 11, 15, 19, 23, 27, 31, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 29, 33, 2, 6, 10, 14, 18, 22, 26, 30, 34]
  | 5 => [10, 14, 18, 22, 26, 30, 34, 3, 7, 11, 15, 19, 23, 27, 31, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 29, 33, 2, 6, 10]
  | 6 => [7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7]
  | _ => []

theorem ws7Word24Weak :
    WeakValidRates (fun i => (ws7WordP24 i : ℝ) / (ws7WordQ24 i : ℝ))
      (periodic ws7Word24.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word24)) := by
  apply weakPeriodic_of_paths ws7Word24 (by decide) ws7WordP24 ws7WordQ24
    (by intro i; fin_cases i <;> norm_num [ws7WordQ24]) ws7WordZ24
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word25 : List (Fin 7) := [0, 1, 2, 3, 4, 0, 1, 5, 6, 2, 0, 3, 1, 4, 0, 2, 1, 5, 6, 0, 3, 4, 1, 2, 0, 5, 6, 1, 0, 3, 4, 2, 1, 0, 5, 6]

def ws7WordP25 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 6
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ25 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 23
  | 1 => 31
  | 2 => 15
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ25 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [14, 0, 5, 10, 15, 20, 2, 7, 12, 17, 22, 4, 9, 14, 19, 1, 6, 11, 16, 21, 3, 8, 13, 18, 23, 5, 10, 15, 20, 2, 7, 12, 17, 22, 4, 9, 14]
  | 1 => [21, 27, 2, 8, 14, 20, 26, 1, 7, 13, 19, 25, 31, 6, 12, 18, 24, 0, 6, 12, 18, 24, 30, 5, 11, 17, 23, 29, 4, 10, 16, 22, 28, 3, 9, 15, 21]
  | 2 => [10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10]
  | 3 => [6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6]
  | 4 => [5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5]
  | 5 => [1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1]
  | 6 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0]
  | _ => []

theorem ws7Word25Weak :
    WeakValidRates (fun i => (ws7WordP25 i : ℝ) / (ws7WordQ25 i : ℝ))
      (periodic ws7Word25.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word25)) := by
  apply weakPeriodic_of_paths ws7Word25 (by decide) ws7WordP25 ws7WordQ25
    (by intro i; fin_cases i <;> norm_num [ws7WordQ25]) ws7WordZ25
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word26 : List (Fin 7) := [3, 4, 2, 0, 6, 1, 5, 0, 3, 2, 1, 4, 0, 6, 5, 1, 0, 2, 3, 4, 1, 0, 6, 5, 2, 0, 1, 3, 4, 0, 1, 2, 6, 5, 0, 1]

def ws7WordP26 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 2
  | 1 => 5
  | 2 => 5
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ26 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 26
  | 2 => 36
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ26 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [3, 5, 7, 9, 2, 4, 6, 8, 1, 3, 5, 7, 9, 2, 4, 6, 8, 1, 3, 5, 7, 9, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3]
  | 1 => [0, 5, 10, 15, 20, 25, 4, 9, 14, 19, 24, 3, 8, 13, 18, 23, 2, 7, 12, 17, 22, 1, 6, 11, 16, 21, 26, 5, 10, 15, 20, 0, 5, 10, 15, 20, 0]
  | 2 => [22, 27, 32, 1, 6, 11, 16, 21, 26, 31, 0, 5, 10, 15, 20, 25, 30, 35, 4, 9, 14, 19, 24, 29, 34, 3, 8, 13, 18, 23, 28, 33, 2, 7, 12, 17, 22]
  | 3 => [9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  | 4 => [7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7]
  | 5 => [3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3]
  | 6 => [4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4]
  | _ => []

theorem ws7Word26Weak :
    WeakValidRates (fun i => (ws7WordP26 i : ℝ) / (ws7WordQ26 i : ℝ))
      (periodic ws7Word26.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word26)) := by
  apply weakPeriodic_of_paths ws7Word26 (by decide) ws7WordP26 ws7WordQ26
    (by intro i; fin_cases i <;> norm_num [ws7WordQ26]) ws7WordZ26
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word27 : List (Fin 7) := [5, 0, 3, 1, 2, 6, 0, 4, 1, 5, 0, 3, 2, 1, 6, 0, 4, 1, 5, 2, 0, 3, 6, 1, 0, 4, 2, 5, 1, 0, 3, 6, 0, 2, 1, 4]

def ws7WordP27 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 3
  | 2 => 5
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ27 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 23
  | 1 => 16
  | 2 => 36
  | 3 => 9
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ27 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [15, 20, 2, 7, 12, 17, 22, 4, 9, 14, 19, 1, 6, 11, 16, 21, 3, 8, 13, 18, 23, 5, 10, 15, 20, 2, 7, 12, 17, 22, 4, 9, 14, 0, 5, 10, 15]
  | 1 => [6, 9, 12, 15, 2, 5, 8, 11, 14, 1, 4, 7, 10, 13, 0, 3, 6, 9, 0, 3, 6, 9, 12, 15, 2, 5, 8, 11, 14, 1, 4, 7, 10, 13, 16, 3, 6]
  | 2 => [11, 16, 21, 26, 31, 0, 5, 10, 15, 20, 25, 30, 35, 4, 9, 14, 19, 24, 29, 34, 3, 8, 13, 18, 23, 28, 33, 2, 7, 12, 17, 22, 27, 32, 1, 6, 11]
  | 3 => [6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6]
  | 4 => [1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1]
  | 5 => [8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8]
  | 6 => [4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4]
  | _ => []

theorem ws7Word27Weak :
    WeakValidRates (fun i => (ws7WordP27 i : ℝ) / (ws7WordQ27 i : ℝ))
      (periodic ws7Word27.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word27)) := by
  apply weakPeriodic_of_paths ws7Word27 (by decide) ws7WordP27 ws7WordQ27
    (by intro i; fin_cases i <;> norm_num [ws7WordQ27]) ws7WordZ27
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word28 : List (Fin 7) := [5, 1, 2, 6, 0, 3, 4, 1, 0, 2, 5, 6, 3, 0, 1, 4, 2, 0, 5, 1, 3, 6, 0, 2, 4, 1, 0, 3, 5, 6, 2, 0, 1, 4, 3, 0]

def ws7WordP28 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 2
  | 1 => 1
  | 2 => 5
  | 3 => 5
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ28 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 6
  | 2 => 36
  | 3 => 36
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ28 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [0, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 7, 0]
  | 1 => [4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4]
  | 2 => [25, 30, 35, 4, 9, 14, 19, 24, 29, 34, 3, 8, 13, 18, 23, 28, 33, 2, 7, 12, 17, 22, 27, 32, 1, 6, 11, 16, 21, 26, 31, 0, 5, 10, 15, 20, 25]
  | 3 => [7, 12, 17, 22, 27, 32, 1, 6, 11, 16, 21, 26, 31, 0, 5, 10, 15, 20, 25, 30, 35, 4, 9, 14, 19, 24, 29, 34, 3, 8, 13, 18, 23, 28, 33, 2, 7]
  | 4 => [2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2]
  | 5 => [8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8]
  | 6 => [6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6]
  | _ => []

theorem ws7Word28Weak :
    WeakValidRates (fun i => (ws7WordP28 i : ℝ) / (ws7WordQ28 i : ℝ))
      (periodic ws7Word28.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word28)) := by
  apply weakPeriodic_of_paths ws7Word28 (by decide) ws7WordP28 ws7WordQ28
    (by intro i; fin_cases i <;> norm_num [ws7WordQ28]) ws7WordZ28
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word29 : List (Fin 7) := [0, 5, 6, 4, 2, 0, 3, 1, 5, 4, 0, 6, 2, 3, 1, 0, 5, 4, 0, 2, 3, 6, 1, 0, 5, 4, 2, 3, 0, 1, 6, 5, 4, 0, 2, 3, 1]

def ws7WordP29 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 5
  | 2 => 5
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 4
  | _ => 0

def ws7WordQ29 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 33
  | 1 => 37
  | 2 => 37
  | 3 => 15
  | 4 => 15
  | 5 => 15
  | 6 => 37
  | _ => 1

def ws7WordZ29 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [27, 1, 8, 15, 22, 29, 3, 10, 17, 24, 31, 5, 12, 19, 26, 33, 7, 14, 21, 0, 7, 14, 21, 28, 2, 9, 16, 23, 30, 4, 11, 18, 25, 32, 6, 13, 20, 27]
  | 1 => [0, 5, 10, 15, 20, 25, 30, 35, 3, 8, 13, 18, 23, 28, 33, 1, 6, 11, 16, 21, 26, 31, 36, 4, 9, 14, 19, 24, 29, 34, 2, 7, 12, 17, 22, 27, 32, 0]
  | 2 => [13, 18, 23, 28, 33, 1, 6, 11, 16, 21, 26, 31, 36, 4, 9, 14, 19, 24, 29, 34, 2, 7, 12, 17, 22, 27, 32, 0, 5, 10, 15, 20, 25, 30, 35, 3, 8, 13]
  | 3 => [3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3]
  | 4 => [9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9]
  | 5 => [11, 13, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11]
  | 6 => [26, 30, 34, 1, 5, 9, 13, 17, 21, 25, 29, 33, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 3, 7, 11, 15, 19, 23, 27, 31, 35, 2, 6, 10, 14, 18, 22, 26]
  | _ => []

theorem ws7Word29Weak :
    WeakValidRates (fun i => (ws7WordP29 i : ℝ) / (ws7WordQ29 i : ℝ))
      (periodic ws7Word29.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word29)) := by
  apply weakPeriodic_of_paths ws7Word29 (by decide) ws7WordP29 ws7WordQ29
    (by intro i; fin_cases i <;> norm_num [ws7WordQ29]) ws7WordZ29
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word30 : List (Fin 7) := [1, 2, 0, 4, 6, 1, 0, 3, 5, 2, 0, 4, 1, 6, 3, 0, 2, 5, 1, 4, 0, 3, 6, 2, 1, 0, 5, 4, 3, 0, 2, 1, 6, 4, 0, 5, 3]

def ws7WordP30 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 4
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | 6 => 4
  | _ => 0

def ws7WordQ30 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 14
  | 1 => 25
  | 2 => 15
  | 3 => 15
  | 4 => 23
  | 5 => 37
  | 6 => 37
  | _ => 1

def ws7WordZ30 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [8, 11, 14, 3, 6, 9, 12, 1, 4, 7, 10, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8]
  | 1 => [24, 3, 7, 11, 15, 19, 0, 4, 8, 12, 16, 20, 24, 3, 7, 11, 15, 19, 23, 2, 6, 10, 14, 18, 22, 1, 5, 9, 13, 17, 21, 25, 4, 8, 12, 16, 20, 24]
  | 2 => [12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12]
  | 3 => [1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1]
  | 4 => [9, 12, 15, 18, 0, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17, 20, 23, 3, 6, 9, 12, 15, 18, 0, 3, 6, 9]
  | 5 => [4, 8, 12, 16, 20, 24, 28, 32, 36, 3, 7, 11, 15, 19, 23, 27, 31, 35, 2, 6, 10, 14, 18, 22, 26, 30, 34, 1, 5, 9, 13, 17, 21, 25, 29, 33, 0, 4]
  | 6 => [19, 23, 27, 31, 35, 2, 6, 10, 14, 18, 22, 26, 30, 34, 1, 5, 9, 13, 17, 21, 25, 29, 33, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 3, 7, 11, 15, 19]
  | _ => []

theorem ws7Word30Weak :
    WeakValidRates (fun i => (ws7WordP30 i : ℝ) / (ws7WordQ30 i : ℝ))
      (periodic ws7Word30.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word30)) := by
  apply weakPeriodic_of_paths ws7Word30 (by decide) ws7WordP30 ws7WordQ30
    (by intro i; fin_cases i <;> norm_num [ws7WordQ30]) ws7WordZ30
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word31 : List (Fin 7) := [1, 6, 4, 0, 3, 5, 1, 2, 0, 6, 4, 1, 3, 0, 2, 5, 0, 1, 4, 6, 3, 0, 2, 1, 5, 4, 0, 3, 6, 2, 1, 0, 4, 5, 3, 0, 2]

def ws7WordP31 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 2
  | 2 => 5
  | 3 => 2
  | 4 => 2
  | 5 => 4
  | 6 => 3
  | _ => 0

def ws7WordQ31 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 33
  | 1 => 13
  | 2 => 37
  | 3 => 15
  | 4 => 15
  | 5 => 37
  | 6 => 28
  | _ => 1

def ws7WordZ31 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [8, 15, 22, 29, 3, 10, 17, 24, 31, 5, 12, 19, 26, 33, 7, 14, 21, 0, 7, 14, 21, 28, 2, 9, 16, 23, 30, 4, 11, 18, 25, 32, 6, 13, 20, 27, 1, 8]
  | 1 => [13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13]
  | 2 => [0, 5, 10, 15, 20, 25, 30, 35, 3, 8, 13, 18, 23, 28, 33, 1, 6, 11, 16, 21, 26, 31, 36, 4, 9, 14, 19, 24, 29, 34, 2, 7, 12, 17, 22, 27, 32, 0]
  | 3 => [4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4]
  | 4 => [8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8]
  | 5 => [13, 17, 21, 25, 29, 33, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 3, 7, 11, 15, 19, 23, 27, 31, 35, 2, 6, 10, 14, 18, 22, 26, 30, 34, 1, 5, 9, 13]
  | 6 => [25, 28, 3, 6, 9, 12, 15, 18, 21, 24, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25]
  | _ => []

theorem ws7Word31Weak :
    WeakValidRates (fun i => (ws7WordP31 i : ℝ) / (ws7WordQ31 i : ℝ))
      (periodic ws7Word31.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word31)) := by
  apply weakPeriodic_of_paths ws7Word31 (by decide) ws7WordP31 ws7WordQ31
    (by intro i; fin_cases i <;> norm_num [ws7WordQ31]) ws7WordZ31
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word32 : List (Fin 7) := [2, 3, 5, 1, 0, 6, 4, 2, 3, 0, 1, 5, 2, 0, 6, 4, 3, 1, 0, 2, 5, 1, 0, 6, 3, 4, 2, 0, 1, 5, 3, 2, 0, 6, 4, 1, 0]

def ws7WordP32 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 8
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

def ws7WordQ32 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 37
  | 1 => 13
  | 2 => 13
  | 3 => 15
  | 4 => 37
  | 5 => 37
  | 6 => 37
  | _ => 1

def ws7WordZ32 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 9, 17, 25, 33, 4, 12, 20, 28, 36, 7, 15, 23, 31, 2, 10, 18, 26, 34, 5, 13, 21, 29, 0, 8, 16, 24, 32, 3, 11, 19, 27, 35, 6, 14, 22, 30, 1]
  | 1 => [4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4]
  | 2 => [10, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10]
  | 3 => [12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12]
  | 4 => [10, 14, 18, 22, 26, 30, 34, 1, 5, 9, 13, 17, 21, 25, 29, 33, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 3, 7, 11, 15, 19, 23, 27, 31, 35, 2, 6, 10]
  | 5 => [28, 32, 36, 3, 7, 11, 15, 19, 23, 27, 31, 35, 2, 6, 10, 14, 18, 22, 26, 30, 34, 1, 5, 9, 13, 17, 21, 25, 29, 33, 0, 4, 8, 12, 16, 20, 24, 28]
  | 6 => [15, 19, 23, 27, 31, 35, 2, 6, 10, 14, 18, 22, 26, 30, 34, 1, 5, 9, 13, 17, 21, 25, 29, 33, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 3, 7, 11, 15]
  | _ => []

theorem ws7Word32Weak :
    WeakValidRates (fun i => (ws7WordP32 i : ℝ) / (ws7WordQ32 i : ℝ))
      (periodic ws7Word32.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word32)) := by
  apply weakPeriodic_of_paths ws7Word32 (by decide) ws7WordP32 ws7WordQ32
    (by intro i; fin_cases i <;> norm_num [ws7WordQ32]) ws7WordZ32
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word33 : List (Fin 7) := [5, 0, 1, 4, 6, 3, 0, 2, 1, 5, 4, 0, 3, 6, 2, 1, 0, 4, 5, 3, 0, 1, 2, 6, 4, 0, 3, 1, 5, 2, 0, 6, 4, 1, 3, 0, 2]

def ws7WordP33 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 6
  | 2 => 5
  | 3 => 2
  | 4 => 2
  | 5 => 4
  | 6 => 3
  | _ => 0

def ws7WordQ33 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 33
  | 1 => 37
  | 2 => 37
  | 3 => 15
  | 4 => 15
  | 5 => 37
  | 6 => 28
  | _ => 1

def ws7WordZ33 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [14, 21, 0, 7, 14, 21, 28, 2, 9, 16, 23, 30, 4, 11, 18, 25, 32, 6, 13, 20, 27, 1, 8, 15, 22, 29, 3, 10, 17, 24, 31, 5, 12, 19, 26, 33, 7, 14]
  | 1 => [20, 26, 32, 1, 7, 13, 19, 25, 31, 0, 6, 12, 18, 24, 30, 36, 5, 11, 17, 23, 29, 35, 4, 10, 16, 22, 28, 34, 3, 9, 15, 21, 27, 33, 2, 8, 14, 20]
  | 2 => [0, 5, 10, 15, 20, 25, 30, 35, 3, 8, 13, 18, 23, 28, 33, 1, 6, 11, 16, 21, 26, 31, 36, 4, 9, 14, 19, 24, 29, 34, 2, 7, 12, 17, 22, 27, 32, 0]
  | 3 => [5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5]
  | 4 => [9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9]
  | 5 => [35, 2, 6, 10, 14, 18, 22, 26, 30, 34, 1, 5, 9, 13, 17, 21, 25, 29, 33, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 3, 7, 11, 15, 19, 23, 27, 31, 35]
  | 6 => [15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 3, 6, 9, 12, 15, 18, 21, 24, 0, 3, 6, 9, 12, 15]
  | _ => []

theorem ws7Word33Weak :
    WeakValidRates (fun i => (ws7WordP33 i : ℝ) / (ws7WordQ33 i : ℝ))
      (periodic ws7Word33.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word33)) := by
  apply weakPeriodic_of_paths ws7Word33 (by decide) ws7WordP33 ws7WordQ33
    (by intro i; fin_cases i <;> norm_num [ws7WordQ33]) ws7WordZ33
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word34 : List (Fin 7) := [5, 2, 6, 3, 0, 1, 4, 2, 0, 3, 5, 1, 6, 0, 2, 4, 3, 1, 0, 5, 2, 6, 0, 1, 4, 3, 2, 0, 5, 1, 6, 0, 3, 2, 4, 1, 0]

def ws7WordP34 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 8
  | 1 => 6
  | 2 => 4
  | 3 => 1
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

def ws7WordQ34 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 37
  | 1 => 37
  | 2 => 25
  | 3 => 8
  | 4 => 37
  | 5 => 37
  | 6 => 37
  | _ => 1

def ws7WordZ34 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [3, 11, 19, 27, 35, 6, 14, 22, 30, 1, 9, 17, 25, 33, 4, 12, 20, 28, 36, 7, 15, 23, 31, 2, 10, 18, 26, 34, 5, 13, 21, 29, 0, 8, 16, 24, 32, 3]
  | 1 => [6, 12, 18, 24, 30, 36, 5, 11, 17, 23, 29, 35, 4, 10, 16, 22, 28, 34, 3, 9, 15, 21, 27, 33, 2, 8, 14, 20, 26, 32, 1, 7, 13, 19, 25, 31, 0, 6]
  | 2 => [16, 20, 0, 4, 8, 12, 16, 20, 0, 4, 8, 12, 16, 20, 24, 3, 7, 11, 15, 19, 23, 2, 6, 10, 14, 18, 22, 1, 5, 9, 13, 17, 21, 25, 4, 8, 12, 16]
  | 3 => [4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4]
  | 4 => [11, 15, 19, 23, 27, 31, 35, 2, 6, 10, 14, 18, 22, 26, 30, 34, 1, 5, 9, 13, 17, 21, 25, 29, 33, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 3, 7, 11]
  | 5 => [33, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 3, 7, 11, 15, 19, 23, 27, 31, 35, 2, 6, 10, 14, 18, 22, 26, 30, 34, 1, 5, 9, 13, 17, 21, 25, 29, 33]
  | 6 => [25, 29, 33, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 3, 7, 11, 15, 19, 23, 27, 31, 35, 2, 6, 10, 14, 18, 22, 26, 30, 34, 1, 5, 9, 13, 17, 21, 25]
  | _ => []

theorem ws7Word34Weak :
    WeakValidRates (fun i => (ws7WordP34 i : ℝ) / (ws7WordQ34 i : ℝ))
      (periodic ws7Word34.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word34)) := by
  apply weakPeriodic_of_paths ws7Word34 (by decide) ws7WordP34 ws7WordQ34
    (by intro i; fin_cases i <;> norm_num [ws7WordQ34]) ws7WordZ34
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word35 : List (Fin 7) := [0, 1, 2, 5, 3, 4, 0, 1, 6, 2, 0, 3, 1, 5, 4, 0, 6, 2, 1, 3, 0, 4, 5, 1, 2, 0, 6, 3, 4, 1, 0, 5, 2, 1, 0, 3, 6, 4]

def ws7WordP35 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 3
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | _ => 0

def ws7WordQ35 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 11
  | 2 => 38
  | 3 => 23
  | 4 => 8
  | 5 => 19
  | 6 => 29
  | _ => 1

def ws7WordZ35 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [3, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3]
  | 1 => [8, 10, 1, 3, 5, 7, 9, 11, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11, 2, 4, 6, 8, 0, 2, 4, 6, 8]
  | 2 => [27, 32, 37, 4, 9, 14, 19, 24, 29, 34, 1, 6, 11, 16, 21, 26, 31, 36, 3, 8, 13, 18, 23, 28, 33, 0, 5, 10, 15, 20, 25, 30, 35, 2, 7, 12, 17, 22, 27]
  | 3 => [9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 0, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17, 20, 23, 3, 6, 9]
  | 4 => [1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1]
  | 5 => [12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12]
  | 6 => [5, 8, 11, 14, 17, 20, 23, 26, 29, 3, 6, 9, 12, 15, 18, 21, 24, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 2, 5]
  | _ => []

theorem ws7Word35Weak :
    WeakValidRates (fun i => (ws7WordP35 i : ℝ) / (ws7WordQ35 i : ℝ))
      (periodic ws7Word35.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word35)) := by
  apply weakPeriodic_of_paths ws7Word35 (by decide) ws7WordP35 ws7WordQ35
    (by intro i; fin_cases i <;> norm_num [ws7WordQ35]) ws7WordZ35
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word36 : List (Fin 7) := [0, 5, 1, 3, 0, 2, 6, 4, 1, 0, 5, 3, 2, 0, 4, 1, 6, 2, 0, 3, 5, 1, 4, 0, 2, 6, 3, 1, 0, 5, 4, 2, 0, 1, 3, 6, 2, 4]

def ws7WordP36 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 3
  | 2 => 2
  | 3 => 5
  | 4 => 5
  | 5 => 2
  | 6 => 2
  | _ => 0

def ws7WordQ36 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 19
  | 2 => 13
  | 3 => 38
  | 4 => 38
  | 5 => 19
  | 6 => 19
  | _ => 1

def ws7WordZ36 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5]
  | 1 => [12, 15, 18, 2, 5, 8, 11, 14, 17, 1, 4, 7, 10, 13, 16, 19, 3, 6, 9, 12, 15, 18, 2, 5, 8, 11, 14, 17, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12]
  | 2 => [2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 0, 2]
  | 3 => [18, 23, 28, 33, 0, 5, 10, 15, 20, 25, 30, 35, 2, 7, 12, 17, 22, 27, 32, 37, 4, 9, 14, 19, 24, 29, 34, 1, 6, 11, 16, 21, 26, 31, 36, 3, 8, 13, 18]
  | 4 => [1, 6, 11, 16, 21, 26, 31, 36, 3, 8, 13, 18, 23, 28, 33, 0, 5, 10, 15, 20, 25, 30, 35, 2, 7, 12, 17, 22, 27, 32, 37, 4, 9, 14, 19, 24, 29, 34, 1]
  | 5 => [16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16]
  | 6 => [5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5]
  | _ => []

theorem ws7Word36Weak :
    WeakValidRates (fun i => (ws7WordP36 i : ℝ) / (ws7WordQ36 i : ℝ))
      (periodic ws7Word36.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word36)) := by
  apply weakPeriodic_of_paths ws7Word36 (by decide) ws7WordP36 ws7WordQ36
    (by intro i; fin_cases i <;> norm_num [ws7WordQ36]) ws7WordZ36
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word37 : List (Fin 7) := [1, 2, 4, 5, 0, 1, 3, 6, 2, 0, 1, 4, 5, 2, 0, 3, 1, 6, 2, 0, 4, 1, 5, 3, 0, 2, 6, 1, 3, 0, 4, 5, 2, 1, 0, 6, 3, 0]

def ws7WordP37 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 2
  | 2 => 4
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

def ws7WordQ37 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 34
  | 1 => 11
  | 2 => 27
  | 3 => 8
  | 4 => 19
  | 5 => 19
  | 6 => 19
  | _ => 1

def ws7WordZ37 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [0, 7, 14, 21, 28, 1, 8, 15, 22, 29, 2, 9, 16, 23, 30, 3, 10, 17, 24, 31, 4, 11, 18, 25, 32, 5, 12, 19, 26, 33, 6, 13, 20, 27, 34, 7, 14, 21, 0]
  | 1 => [10, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11, 2, 4, 6, 8, 10]
  | 2 => [22, 26, 3, 7, 11, 15, 19, 23, 27, 4, 8, 12, 16, 20, 0, 4, 8, 12, 16, 0, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 25, 2, 6, 10, 14, 18, 22]
  | 3 => [1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1]
  | 4 => [15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15]
  | 5 => [12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12]
  | 6 => [4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4]
  | _ => []

theorem ws7Word37Weak :
    WeakValidRates (fun i => (ws7WordP37 i : ℝ) / (ws7WordQ37 i : ℝ))
      (periodic ws7Word37.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word37)) := by
  apply weakPeriodic_of_paths ws7Word37 (by decide) ws7WordP37 ws7WordQ37
    (by intro i; fin_cases i <;> norm_num [ws7WordQ37]) ws7WordZ37
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word38 : List (Fin 7) := [2, 4, 0, 3, 1, 6, 5, 0, 2, 4, 1, 3, 0, 5, 6, 2, 0, 1, 4, 3, 5, 0, 1, 2, 6, 4, 0, 3, 5, 1, 0, 2, 4, 6, 3, 0, 1, 5]

def ws7WordP38 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 4
  | 1 => 2
  | 2 => 5
  | 3 => 3
  | 4 => 1
  | 5 => 1
  | 6 => 2
  | _ => 0

def ws7WordQ38 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 19
  | 1 => 13
  | 2 => 38
  | 3 => 23
  | 4 => 8
  | 5 => 8
  | 6 => 19
  | _ => 1

def ws7WordZ38 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [9, 13, 17, 2, 6, 10, 14, 18, 3, 7, 11, 15, 19, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 18, 3, 7, 11, 15, 0, 4, 8, 12, 16, 1, 5, 9]
  | 1 => [4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4]
  | 2 => [34, 1, 6, 11, 16, 21, 26, 31, 36, 3, 8, 13, 18, 23, 28, 33, 0, 5, 10, 15, 20, 25, 30, 35, 2, 7, 12, 17, 22, 27, 32, 37, 4, 9, 14, 19, 24, 29, 34]
  | 3 => [10, 13, 16, 19, 0, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17, 20, 23, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10]
  | 4 => [5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5]
  | 5 => [1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1]
  | 6 => [8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8]
  | _ => []

theorem ws7Word38Weak :
    WeakValidRates (fun i => (ws7WordP38 i : ℝ) / (ws7WordQ38 i : ℝ))
      (periodic ws7Word38.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word38)) := by
  apply weakPeriodic_of_paths ws7Word38 (by decide) ws7WordP38 ws7WordQ38
    (by intro i; fin_cases i <;> norm_num [ws7WordQ38]) ws7WordZ38
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word39 : List (Fin 7) := [5, 1, 3, 0, 4, 2, 6, 0, 1, 3, 5, 2, 0, 4, 1, 3, 6, 0, 2, 5, 1, 3, 0, 4, 2, 6, 0, 1, 3, 5, 2, 0, 4, 1, 3, 6, 0, 2]

def ws7WordP39 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 4
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

def ws7WordQ39 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 19
  | 1 => 19
  | 2 => 19
  | 3 => 19
  | 4 => 19
  | 5 => 19
  | 6 => 19
  | _ => 1

def ws7WordZ39 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [6, 10, 14, 18, 3, 7, 11, 15, 0, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 18, 3, 7, 11, 15, 0, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6]
  | 1 => [13, 16, 0, 3, 6, 9, 12, 15, 18, 2, 5, 8, 11, 14, 17, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12, 15, 18, 2, 5, 8, 11, 14, 17, 1, 4, 7, 10, 13]
  | 2 => [2, 5, 8, 11, 14, 17, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12, 15, 18, 2, 5, 8, 11, 14, 17, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12, 15, 18, 2]
  | 3 => [10, 13, 16, 0, 3, 6, 9, 12, 15, 18, 2, 5, 8, 11, 14, 17, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12, 15, 18, 2, 5, 8, 11, 14, 17, 1, 4, 7, 10]
  | 4 => [10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10]
  | 5 => [17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17]
  | 6 => [5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5]
  | _ => []

theorem ws7Word39Weak :
    WeakValidRates (fun i => (ws7WordP39 i : ℝ) / (ws7WordQ39 i : ℝ))
      (periodic ws7Word39.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word39)) := by
  apply weakPeriodic_of_paths ws7Word39 (by decide) ws7WordP39 ws7WordQ39
    (by intro i; fin_cases i <;> norm_num [ws7WordQ39]) ws7WordZ39
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word40 : List (Fin 7) := [0, 2, 6, 5, 1, 0, 4, 3, 2, 6, 0, 1, 5, 4, 3, 0, 2, 1, 6, 5, 0, 4, 3, 1, 2, 0, 6, 5, 4, 0, 1, 3, 2, 6, 0, 5, 1, 4, 3]

def ws7WordP40 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 8
  | 1 => 2
  | 2 => 5
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ40 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 39
  | 1 => 13
  | 2 => 39
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | _ => 1

def ws7WordZ40 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [33, 2, 10, 18, 26, 34, 3, 11, 19, 27, 35, 4, 12, 20, 28, 36, 5, 13, 21, 29, 37, 6, 14, 22, 30, 38, 7, 15, 23, 31, 0, 8, 16, 24, 32, 1, 9, 17, 25, 33]
  | 1 => [4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4]
  | 2 => [33, 38, 4, 9, 14, 19, 24, 29, 34, 0, 5, 10, 15, 20, 25, 30, 35, 1, 6, 11, 16, 21, 26, 31, 36, 2, 7, 12, 17, 22, 27, 32, 37, 3, 8, 13, 18, 23, 28, 33]
  | 3 => [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0]
  | 4 => [2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2]
  | 5 => [3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3]
  | 6 => [5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5]
  | _ => []

theorem ws7Word40Weak :
    WeakValidRates (fun i => (ws7WordP40 i : ℝ) / (ws7WordQ40 i : ℝ))
      (periodic ws7Word40.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word40)) := by
  apply weakPeriodic_of_paths ws7Word40 (by decide) ws7WordP40 ws7WordQ40
    (by intro i; fin_cases i <;> norm_num [ws7WordQ40]) ws7WordZ40
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word41 : List (Fin 7) := [5, 1, 2, 0, 3, 4, 6, 1, 0, 2, 5, 3, 0, 4, 1, 2, 6, 3, 0, 5, 1, 4, 2, 0, 3, 6, 1, 0, 2, 5, 4, 3, 0, 1, 2, 6, 4, 3, 0]

def ws7WordP41 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 4
  | 6 => 4
  | _ => 0

def ws7WordQ41 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 13
  | 2 => 13
  | 3 => 13
  | 4 => 8
  | 5 => 39
  | 6 => 39
  | _ => 1

def ws7WordZ41 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1]
  | 1 => [11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11]
  | 2 => [8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8]
  | 3 => [3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3]
  | 4 => [2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 0, 1, 2]
  | 5 => [37, 2, 6, 10, 14, 18, 22, 26, 30, 34, 38, 3, 7, 11, 15, 19, 23, 27, 31, 35, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 1, 5, 9, 13, 17, 21, 25, 29, 33, 37]
  | 6 => [13, 17, 21, 25, 29, 33, 37, 2, 6, 10, 14, 18, 22, 26, 30, 34, 38, 3, 7, 11, 15, 19, 23, 27, 31, 35, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 1, 5, 9, 13]
  | _ => []

theorem ws7Word41Weak :
    WeakValidRates (fun i => (ws7WordP41 i : ℝ) / (ws7WordQ41 i : ℝ))
      (periodic ws7Word41.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word41)) := by
  apply weakPeriodic_of_paths ws7Word41 (by decide) ws7WordP41 ws7WordQ41
    (by intro i; fin_cases i <;> norm_num [ws7WordQ41]) ws7WordZ41
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word42 : List (Fin 7) := [5, 3, 1, 4, 0, 2, 6, 0, 1, 3, 5, 2, 4, 0, 1, 3, 6, 2, 0, 1, 5, 3, 4, 0, 2, 1, 6, 0, 3, 5, 2, 1, 4, 0, 3, 1, 6, 2, 0]

def ws7WordP42 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 3
  | 2 => 2
  | 3 => 1
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

def ws7WordQ42 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 17
  | 2 => 13
  | 3 => 7
  | 4 => 39
  | 5 => 39
  | 6 => 39
  | _ => 1

def ws7WordZ42 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 2, 3, 4, 5, 1, 2, 3, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1]
  | 1 => [9, 12, 15, 1, 4, 7, 10, 13, 16, 2, 5, 8, 11, 14, 17, 3, 6, 9, 12, 15, 1, 4, 7, 10, 13, 16, 2, 5, 8, 11, 14, 17, 3, 6, 9, 12, 0, 3, 6, 9]
  | 2 => [3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 12, 1, 3]
  | 3 => [4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4]
  | 4 => [26, 30, 34, 38, 3, 7, 11, 15, 19, 23, 27, 31, 35, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 1, 5, 9, 13, 17, 21, 25, 29, 33, 37, 2, 6, 10, 14, 18, 22, 26]
  | 5 => [36, 1, 5, 9, 13, 17, 21, 25, 29, 33, 37, 2, 6, 10, 14, 18, 22, 26, 30, 34, 38, 3, 7, 11, 15, 19, 23, 27, 31, 35, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36]
  | 6 => [11, 15, 19, 23, 27, 31, 35, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 1, 5, 9, 13, 17, 21, 25, 29, 33, 37, 2, 6, 10, 14, 18, 22, 26, 30, 34, 38, 3, 7, 11]
  | _ => []

theorem ws7Word42Weak :
    WeakValidRates (fun i => (ws7WordP42 i : ℝ) / (ws7WordQ42 i : ℝ))
      (periodic ws7Word42.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word42)) := by
  apply weakPeriodic_of_paths ws7Word42 (by decide) ws7WordP42 ws7WordQ42
    (by intro i; fin_cases i <;> norm_num [ws7WordQ42]) ws7WordZ42
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word43 : List (Fin 7) := [5, 4, 0, 3, 6, 2, 1, 0, 4, 3, 5, 2, 0, 1, 6, 3, 4, 0, 2, 1, 5, 3, 0, 6, 2, 4, 1, 0, 3, 5, 2, 0, 1, 6, 4, 3, 0, 2, 1]

def ws7WordP43 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 8
  | 1 => 2
  | 2 => 2
  | 3 => 3
  | 4 => 2
  | 5 => 4
  | 6 => 4
  | _ => 0

def ws7WordQ43 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 39
  | 1 => 13
  | 2 => 13
  | 3 => 20
  | 4 => 17
  | 5 => 39
  | 6 => 39
  | _ => 1

def ws7WordZ43 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [17, 25, 33, 2, 10, 18, 26, 34, 3, 11, 19, 27, 35, 4, 12, 20, 28, 36, 5, 13, 21, 29, 37, 6, 14, 22, 30, 38, 7, 15, 23, 31, 0, 8, 16, 24, 32, 1, 9, 17]
  | 1 => [0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0]
  | 2 => [3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 12, 1, 3]
  | 3 => [11, 14, 17, 20, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12, 15, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11]
  | 4 => [10, 12, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10]
  | 5 => [36, 1, 5, 9, 13, 17, 21, 25, 29, 33, 37, 2, 6, 10, 14, 18, 22, 26, 30, 34, 38, 3, 7, 11, 15, 19, 23, 27, 31, 35, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36]
  | 6 => [21, 25, 29, 33, 37, 2, 6, 10, 14, 18, 22, 26, 30, 34, 38, 3, 7, 11, 15, 19, 23, 27, 31, 35, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 1, 5, 9, 13, 17, 21]
  | _ => []

theorem ws7Word43Weak :
    WeakValidRates (fun i => (ws7WordP43 i : ℝ) / (ws7WordQ43 i : ℝ))
      (periodic ws7Word43.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word43)) := by
  apply weakPeriodic_of_paths ws7Word43 (by decide) ws7WordP43 ws7WordQ43
    (by intro i; fin_cases i <;> norm_num [ws7WordQ43]) ws7WordZ43
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word44 : List (Fin 7) := [6, 1, 4, 2, 0, 5, 3, 1, 0, 2, 4, 6, 0, 1, 3, 5, 2, 0, 4, 1, 6, 3, 2, 0, 5, 1, 4, 0, 2, 3, 1, 6, 0, 4, 5, 2, 1, 3, 0]

def ws7WordP44 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 4
  | 2 => 2
  | 3 => 5
  | 4 => 5
  | 5 => 4
  | 6 => 1
  | _ => 0

def ws7WordQ44 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 23
  | 2 => 13
  | 3 => 39
  | 4 => 39
  | 5 => 39
  | 6 => 10
  | _ => 1

def ws7WordZ44 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1]
  | 1 => [10, 14, 0, 4, 8, 12, 16, 20, 1, 5, 9, 13, 17, 21, 2, 6, 10, 14, 18, 22, 3, 7, 11, 15, 19, 23, 4, 8, 12, 16, 20, 1, 5, 9, 13, 17, 21, 2, 6, 10]
  | 2 => [7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7]
  | 3 => [7, 12, 17, 22, 27, 32, 37, 3, 8, 13, 18, 23, 28, 33, 38, 4, 9, 14, 19, 24, 29, 34, 0, 5, 10, 15, 20, 25, 30, 35, 1, 6, 11, 16, 21, 26, 31, 36, 2, 7]
  | 4 => [25, 30, 35, 1, 6, 11, 16, 21, 26, 31, 36, 2, 7, 12, 17, 22, 27, 32, 37, 3, 8, 13, 18, 23, 28, 33, 38, 4, 9, 14, 19, 24, 29, 34, 0, 5, 10, 15, 20, 25]
  | 5 => [17, 21, 25, 29, 33, 37, 2, 6, 10, 14, 18, 22, 26, 30, 34, 38, 3, 7, 11, 15, 19, 23, 27, 31, 35, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 1, 5, 9, 13, 17]
  | 6 => [8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8]
  | _ => []

theorem ws7Word44Weak :
    WeakValidRates (fun i => (ws7WordP44 i : ℝ) / (ws7WordQ44 i : ℝ))
      (periodic ws7Word44.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word44)) := by
  apply weakPeriodic_of_paths ws7Word44 (by decide) ws7WordP44 ws7WordQ44
    (by intro i; fin_cases i <;> norm_num [ws7WordQ44]) ws7WordZ44
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word45 : List (Fin 7) := [1, 2, 3, 0, 6, 4, 5, 1, 0, 2, 3, 6, 0, 4, 1, 5, 0, 2, 3, 6, 1, 0, 4, 5, 2, 0, 1, 3, 6, 4, 0, 5, 2, 1, 0, 3, 6, 4, 5, 0]

def ws7WordP45 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 4
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ45 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 40
  | 1 => 27
  | 2 => 8
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | _ => 1

def ws7WordZ45 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [7, 16, 25, 34, 3, 12, 21, 30, 39, 8, 17, 26, 35, 4, 13, 22, 31, 0, 9, 18, 27, 36, 5, 14, 23, 32, 1, 10, 19, 28, 37, 6, 15, 24, 33, 2, 11, 20, 29, 38, 7]
  | 1 => [25, 2, 6, 10, 14, 18, 22, 26, 3, 7, 11, 15, 19, 23, 27, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 0, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 25]
  | 2 => [7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]
  | 3 => [5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5]
  | 4 => [2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2]
  | 5 => [1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1]
  | 6 => [4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4]
  | _ => []

theorem ws7Word45Weak :
    WeakValidRates (fun i => (ws7WordP45 i : ℝ) / (ws7WordQ45 i : ℝ))
      (periodic ws7Word45.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word45)) := by
  apply weakPeriodic_of_paths ws7Word45 (by decide) ws7WordP45 ws7WordQ45
    (by intro i; fin_cases i <;> norm_num [ws7WordQ45]) ws7WordZ45
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word46 : List (Fin 7) := [2, 6, 5, 0, 1, 3, 4, 2, 0, 6, 5, 1, 3, 0, 2, 4, 6, 1, 0, 5, 3, 2, 0, 4, 1, 6, 5, 2, 0, 3, 1, 4, 6, 0, 2, 5, 3, 1, 0, 4]

def ws7WordP46 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 3
  | 2 => 3
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ46 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 20
  | 2 => 20
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | _ => 1

def ws7WordZ46 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2]
  | 1 => [7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 20, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7]
  | 2 => [17, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 20, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17]
  | 3 => [3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3]
  | 4 => [1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1]
  | 5 => [5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5]
  | 6 => [7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]
  | _ => []

theorem ws7Word46Weak :
    WeakValidRates (fun i => (ws7WordP46 i : ℝ) / (ws7WordQ46 i : ℝ))
      (periodic ws7Word46.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word46)) := by
  apply weakPeriodic_of_paths ws7Word46 (by decide) ws7WordP46 ws7WordQ46
    (by intro i; fin_cases i <;> norm_num [ws7WordQ46]) ws7WordZ46
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word47 : List (Fin 7) := [3, 0, 4, 1, 6, 5, 2, 0, 3, 1, 4, 0, 2, 5, 3, 6, 1, 0, 4, 2, 3, 0, 5, 1, 6, 4, 2, 0, 3, 1, 5, 0, 2, 4, 3, 6, 1, 0, 5, 2]

def ws7WordP47 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 3
  | 2 => 3
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ47 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 20
  | 2 => 20
  | 3 => 7
  | 4 => 8
  | 5 => 8
  | 6 => 10
  | _ => 1

def ws7WordZ47 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3]
  | 1 => [10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10]
  | 2 => [1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 0, 3, 6, 9, 12, 15, 18, 1]
  | 3 => [5, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5]
  | 4 => [6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6]
  | 5 => [2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2]
  | 6 => [5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5]
  | _ => []

theorem ws7Word47Weak :
    WeakValidRates (fun i => (ws7WordP47 i : ℝ) / (ws7WordQ47 i : ℝ))
      (periodic ws7Word47.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word47)) := by
  apply weakPeriodic_of_paths ws7Word47 (by decide) ws7WordP47 ws7WordQ47
    (by intro i; fin_cases i <;> norm_num [ws7WordQ47]) ws7WordZ47
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word48 : List (Fin 7) := [4, 0, 5, 2, 1, 6, 0, 3, 1, 0, 4, 2, 5, 0, 1, 6, 3, 0, 1, 2, 4, 0, 5, 3, 1, 6, 0, 2, 1, 0, 4, 3, 5, 0, 1, 6, 2, 0, 1, 3]

def ws7WordP48 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ48 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 4
  | 1 => 5
  | 2 => 8
  | 3 => 8
  | 4 => 10
  | 5 => 10
  | 6 => 10
  | _ => 1

def ws7WordZ48 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [2, 3, 0, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2]
  | 1 => [1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1]
  | 2 => [4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4]
  | 3 => [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0]
  | 4 => [9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  | 5 => [7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7]
  | 6 => [4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4]
  | _ => []

theorem ws7Word48Weak :
    WeakValidRates (fun i => (ws7WordP48 i : ℝ) / (ws7WordQ48 i : ℝ))
      (periodic ws7Word48.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word48)) := by
  apply weakPeriodic_of_paths ws7Word48 (by decide) ws7WordP48 ws7WordQ48
    (by intro i; fin_cases i <;> norm_num [ws7WordQ48]) ws7WordZ48
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word49 : List (Fin 7) := [5, 2, 0, 3, 1, 6, 4, 0, 2, 1, 5, 3, 0, 1, 4, 2, 6, 0, 3, 1, 5, 2, 0, 4, 1, 6, 3, 0, 2, 1, 5, 4, 0, 1, 3, 2, 6, 0, 4, 1]

def ws7WordP49 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ49 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 5
  | 2 => 20
  | 3 => 8
  | 4 => 8
  | 5 => 10
  | 6 => 10
  | _ => 1

def ws7WordZ49 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2]
  | 1 => [1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1]
  | 2 => [14, 17, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14]
  | 3 => [5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5]
  | 4 => [1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1]
  | 5 => [9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  | 6 => [4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4]
  | _ => []

theorem ws7Word49Weak :
    WeakValidRates (fun i => (ws7WordP49 i : ℝ) / (ws7WordQ49 i : ℝ))
      (periodic ws7Word49.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word49)) := by
  apply weakPeriodic_of_paths ws7Word49 (by decide) ws7WordP49 ws7WordQ49
    (by intro i; fin_cases i <;> norm_num [ws7WordQ49]) ws7WordZ49
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word50 : List (Fin 7) := [5, 3, 2, 1, 0, 4, 6, 0, 5, 3, 1, 2, 0, 4, 6, 5, 1, 0, 3, 2, 4, 0, 6, 1, 5, 3, 0, 2, 4, 1, 0, 6, 5, 3, 2, 0, 1, 4, 6, 0]

def ws7WordP50 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ50 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 20
  | 2 => 8
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | _ => 1

def ws7WordZ50 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 3, 5, 7, 9, 2, 4, 6, 0, 2, 4, 6, 8, 1, 3, 5, 7, 9, 2, 4, 6, 8, 1, 3, 5, 7, 9, 2, 4, 6, 8, 1, 3, 5, 7, 9, 2, 4, 6, 8, 1]
  | 1 => [10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 20, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10]
  | 2 => [5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5]
  | 3 => [6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6]
  | 4 => [3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3]
  | 5 => [8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8]
  | 6 => [1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1]
  | _ => []

theorem ws7Word50Weak :
    WeakValidRates (fun i => (ws7WordP50 i : ℝ) / (ws7WordQ50 i : ℝ))
      (periodic ws7Word50.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word50)) := by
  apply weakPeriodic_of_paths ws7Word50 (by decide) ws7WordP50 ws7WordQ50
    (by intro i; fin_cases i <;> norm_num [ws7WordQ50]) ws7WordZ50
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word51 : List (Fin 7) := [6, 1, 0, 3, 2, 5, 4, 1, 0, 2, 3, 6, 0, 1, 5, 2, 4, 3, 0, 1, 6, 2, 0, 3, 1, 5, 4, 2, 0, 1, 3, 6, 0, 2, 5, 1, 4, 3, 0, 2]

def ws7WordP51 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 5
  | 2 => 5
  | 3 => 3
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ51 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 29
  | 2 => 29
  | 3 => 20
  | 4 => 10
  | 5 => 10
  | 6 => 10
  | _ => 1

def ws7WordZ51 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2]
  | 1 => [21, 26, 2, 7, 12, 17, 22, 27, 3, 8, 13, 18, 23, 28, 4, 9, 14, 19, 24, 29, 5, 10, 15, 20, 25, 1, 6, 11, 16, 21, 0, 5, 10, 15, 20, 25, 1, 6, 11, 16, 21]
  | 2 => [5, 10, 15, 20, 25, 1, 6, 11, 16, 21, 0, 5, 10, 15, 20, 25, 1, 6, 11, 16, 21, 26, 2, 7, 12, 17, 22, 27, 3, 8, 13, 18, 23, 28, 4, 9, 14, 19, 24, 29, 5]
  | 3 => [8, 11, 14, 17, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8]
  | 4 => [3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3]
  | 5 => [5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5]
  | 6 => [9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  | _ => []

theorem ws7Word51Weak :
    WeakValidRates (fun i => (ws7WordP51 i : ℝ) / (ws7WordQ51 i : ℝ))
      (periodic ws7Word51.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word51)) := by
  apply weakPeriodic_of_paths ws7Word51 (by decide) ws7WordP51 ws7WordQ51
    (by intro i; fin_cases i <;> norm_num [ws7WordQ51]) ws7WordZ51
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word52 : List (Fin 7) := [4, 1, 3, 0, 2, 5, 6, 1, 0, 4, 3, 2, 0, 5, 1, 6, 4, 0, 3, 2, 5, 1, 0, 6, 4, 2, 0, 3, 1, 5, 6, 0, 2, 4, 3, 1, 0, 5, 6, 2, 0]

def ws7WordP52 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 6
  | 2 => 1
  | 3 => 4
  | 4 => 3
  | 5 => 3
  | 6 => 2
  | _ => 0

def ws7WordQ52 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 23
  | 1 => 41
  | 2 => 7
  | 3 => 33
  | 4 => 25
  | 5 => 25
  | 6 => 17
  | _ => 1

def ws7WordZ52 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [2, 7, 12, 17, 0, 5, 10, 15, 20, 2, 7, 12, 17, 0, 5, 10, 15, 20, 2, 7, 12, 17, 22, 4, 9, 14, 19, 1, 6, 11, 16, 21, 3, 8, 13, 18, 23, 5, 10, 15, 20, 2]
  | 1 => [34, 40, 5, 11, 17, 23, 29, 35, 0, 6, 12, 18, 24, 30, 36, 1, 7, 13, 19, 25, 31, 37, 2, 8, 14, 20, 26, 32, 38, 3, 9, 15, 21, 27, 33, 39, 4, 10, 16, 22, 28, 34]
  | 2 => [1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1]
  | 3 => [24, 28, 32, 3, 7, 11, 15, 19, 23, 27, 31, 2, 6, 10, 14, 18, 22, 26, 30, 1, 5, 9, 13, 17, 21, 25, 29, 33, 4, 8, 12, 16, 20, 24, 28, 0, 4, 8, 12, 16, 20, 24]
  | 4 => [23, 1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23]
  | 5 => [10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10]
  | 6 => [4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4]
  | _ => []

theorem ws7Word52Weak :
    WeakValidRates (fun i => (ws7WordP52 i : ℝ) / (ws7WordQ52 i : ℝ))
      (periodic ws7Word52.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word52)) := by
  apply weakPeriodic_of_paths ws7Word52 (by decide) ws7WordP52 ws7WordQ52
    (by intro i; fin_cases i <;> norm_num [ws7WordQ52]) ws7WordZ52
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word53 : List (Fin 7) := [4, 2, 5, 0, 3, 1, 6, 4, 0, 2, 5, 1, 3, 0, 6, 2, 4, 0, 1, 5, 3, 6, 0, 2, 4, 1, 0, 5, 3, 6, 2, 0, 1, 4, 5, 0, 2, 3, 6, 1, 0]

def ws7WordP53 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 6
  | 2 => 1
  | 3 => 5
  | 4 => 3
  | 5 => 3
  | 6 => 2
  | _ => 0

def ws7WordQ53 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 41
  | 1 => 41
  | 2 => 7
  | 3 => 41
  | 4 => 25
  | 5 => 25
  | 6 => 17
  | _ => 1

def ws7WordZ53 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [5, 14, 23, 32, 0, 9, 18, 27, 36, 4, 13, 22, 31, 40, 8, 17, 26, 35, 3, 12, 21, 30, 39, 7, 16, 25, 34, 2, 11, 20, 29, 38, 6, 15, 24, 33, 1, 10, 19, 28, 37, 5]
  | 1 => [10, 16, 22, 28, 34, 40, 5, 11, 17, 23, 29, 35, 0, 6, 12, 18, 24, 30, 36, 1, 7, 13, 19, 25, 31, 37, 2, 8, 14, 20, 26, 32, 38, 3, 9, 15, 21, 27, 33, 39, 4, 10]
  | 2 => [4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4]
  | 3 => [19, 24, 29, 34, 39, 3, 8, 13, 18, 23, 28, 33, 38, 2, 7, 12, 17, 22, 27, 32, 37, 1, 6, 11, 16, 21, 26, 31, 36, 0, 5, 10, 15, 20, 25, 30, 35, 40, 4, 9, 14, 19]
  | 4 => [24, 2, 5, 8, 11, 14, 17, 20, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21, 24]
  | 5 => [18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 0, 3, 6, 9, 12, 15, 18]
  | 6 => [5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5]
  | _ => []

theorem ws7Word53Weak :
    WeakValidRates (fun i => (ws7WordP53 i : ℝ) / (ws7WordQ53 i : ℝ))
      (periodic ws7Word53.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word53)) := by
  apply weakPeriodic_of_paths ws7Word53 (by decide) ws7WordP53 ws7WordQ53
    (by intro i; fin_cases i <;> norm_num [ws7WordQ53]) ws7WordZ53
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word54 : List (Fin 7) := [0, 6, 2, 1, 4, 0, 3, 5, 2, 6, 0, 1, 3, 4, 0, 5, 2, 6, 1, 0, 3, 4, 2, 5, 0, 1, 6, 3, 0, 2, 4, 5, 1, 0, 3, 6, 2, 0, 4, 1, 5, 3]

def ws7WordP54 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 5
  | 5 => 2
  | 6 => 2
  | _ => 0

def ws7WordQ54 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 14
  | 1 => 7
  | 2 => 7
  | 3 => 7
  | 4 => 42
  | 5 => 17
  | 6 => 17
  | _ => 1

def ws7WordZ54 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 0, 3, 6, 9, 12]
  | 1 => [3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3]
  | 2 => [5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5]
  | 3 => [1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1]
  | 4 => [17, 22, 27, 32, 37, 0, 5, 10, 15, 20, 25, 30, 35, 40, 3, 8, 13, 18, 23, 28, 33, 38, 1, 6, 11, 16, 21, 26, 31, 36, 41, 4, 9, 14, 19, 24, 29, 34, 39, 2, 7, 12, 17]
  | 5 => [3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3]
  | 6 => [14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14]
  | _ => []

theorem ws7Word54Weak :
    WeakValidRates (fun i => (ws7WordP54 i : ℝ) / (ws7WordQ54 i : ℝ))
      (periodic ws7Word54.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word54)) := by
  apply weakPeriodic_of_paths ws7Word54 (by decide) ws7WordP54 ws7WordQ54
    (by intro i; fin_cases i <;> norm_num [ws7WordQ54]) ws7WordZ54
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word55 : List (Fin 7) := [1, 2, 0, 6, 5, 1, 4, 0, 3, 2, 6, 1, 0, 5, 4, 2, 3, 0, 1, 6, 5, 0, 2, 4, 1, 3, 0, 6, 5, 2, 1, 0, 4, 3, 0, 1, 2, 6, 5, 0, 4, 3]

def ws7WordP55 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 1
  | 2 => 1
  | 3 => 5
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ55 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 24
  | 1 => 6
  | 2 => 7
  | 3 => 42
  | 4 => 17
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ55 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 24, 5, 10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 0, 5, 10, 15, 20, 1, 6, 11]
  | 1 => [6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6]
  | 2 => [5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5]
  | 3 => [0, 5, 10, 15, 20, 25, 30, 35, 40, 3, 8, 13, 18, 23, 28, 33, 38, 1, 6, 11, 16, 21, 26, 31, 36, 41, 4, 9, 14, 19, 24, 29, 34, 39, 2, 7, 12, 17, 22, 27, 32, 37, 0]
  | 4 => [3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3]
  | 5 => [4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4]
  | 6 => [5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5]
  | _ => []

theorem ws7Word55Weak :
    WeakValidRates (fun i => (ws7WordP55 i : ℝ) / (ws7WordQ55 i : ℝ))
      (periodic ws7Word55.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word55)) := by
  apply weakPeriodic_of_paths ws7Word55 (by decide) ws7WordP55 ws7WordQ55
    (by intro i; fin_cases i <;> norm_num [ws7WordQ55]) ws7WordZ55
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word56 : List (Fin 7) := [3, 5, 1, 0, 6, 4, 0, 2, 1, 3, 5, 0, 6, 4, 1, 0, 2, 3, 5, 0, 1, 6, 4, 0, 2, 3, 1, 5, 0, 6, 4, 0, 1, 2, 3, 5, 0, 6, 1, 4, 0, 2]

def ws7WordP56 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 1
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | 5 => 5
  | 6 => 5
  | _ => 0

def ws7WordQ56 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 13
  | 1 => 6
  | 2 => 42
  | 3 => 42
  | 4 => 42
  | 5 => 42
  | 6 => 42
  | _ => 1

def ws7WordZ56 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [4, 7, 10, 13, 3, 6, 9, 0, 3, 6, 9, 12, 2, 5, 8, 11, 1, 4, 7, 10, 0, 3, 6, 9, 0, 3, 6, 9, 12, 2, 5, 8, 0, 3, 6, 9, 12, 2, 5, 8, 11, 1, 4]
  | 1 => [3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3]
  | 2 => [2, 7, 12, 17, 22, 27, 32, 37, 0, 5, 10, 15, 20, 25, 30, 35, 40, 3, 8, 13, 18, 23, 28, 33, 38, 1, 6, 11, 16, 21, 26, 31, 36, 41, 4, 9, 14, 19, 24, 29, 34, 39, 2]
  | 3 => [38, 1, 6, 11, 16, 21, 26, 31, 36, 41, 4, 9, 14, 19, 24, 29, 34, 39, 2, 7, 12, 17, 22, 27, 32, 37, 0, 5, 10, 15, 20, 25, 30, 35, 40, 3, 8, 13, 18, 23, 28, 33, 38]
  | 4 => [14, 19, 24, 29, 34, 39, 2, 7, 12, 17, 22, 27, 32, 37, 0, 5, 10, 15, 20, 25, 30, 35, 40, 3, 8, 13, 18, 23, 28, 33, 38, 1, 6, 11, 16, 21, 26, 31, 36, 41, 4, 9, 14]
  | 5 => [32, 37, 0, 5, 10, 15, 20, 25, 30, 35, 40, 3, 8, 13, 18, 23, 28, 33, 38, 1, 6, 11, 16, 21, 26, 31, 36, 41, 4, 9, 14, 19, 24, 29, 34, 39, 2, 7, 12, 17, 22, 27, 32]
  | 6 => [20, 25, 30, 35, 40, 3, 8, 13, 18, 23, 28, 33, 38, 1, 6, 11, 16, 21, 26, 31, 36, 41, 4, 9, 14, 19, 24, 29, 34, 39, 2, 7, 12, 17, 22, 27, 32, 37, 0, 5, 10, 15, 20]
  | _ => []

theorem ws7Word56Weak :
    WeakValidRates (fun i => (ws7WordP56 i : ℝ) / (ws7WordQ56 i : ℝ))
      (periodic ws7Word56.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word56)) := by
  apply weakPeriodic_of_paths ws7Word56 (by decide) ws7WordP56 ws7WordQ56
    (by intro i; fin_cases i <;> norm_num [ws7WordQ56]) ws7WordZ56
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word57 : List (Fin 7) := [5, 3, 4, 0, 1, 6, 2, 0, 5, 3, 4, 1, 0, 6, 2, 3, 5, 0, 1, 4, 2, 6, 0, 3, 1, 5, 0, 4, 2, 3, 6, 0, 1, 5, 2, 4, 0, 3, 6, 1, 0, 2]

def ws7WordP57 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 5
  | 5 => 5
  | 6 => 5
  | _ => 0

def ws7WordQ57 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 14
  | 1 => 7
  | 2 => 7
  | 3 => 7
  | 4 => 42
  | 5 => 42
  | 6 => 42
  | _ => 1

def ws7WordZ57 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [4, 7, 10, 13, 2, 5, 8, 11, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 12, 1, 4]
  | 1 => [3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3]
  | 2 => [0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0]
  | 3 => [5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5]
  | 4 => [30, 35, 40, 3, 8, 13, 18, 23, 28, 33, 38, 1, 6, 11, 16, 21, 26, 31, 36, 41, 4, 9, 14, 19, 24, 29, 34, 39, 2, 7, 12, 17, 22, 27, 32, 37, 0, 5, 10, 15, 20, 25, 30]
  | 5 => [41, 4, 9, 14, 19, 24, 29, 34, 39, 2, 7, 12, 17, 22, 27, 32, 37, 0, 5, 10, 15, 20, 25, 30, 35, 40, 3, 8, 13, 18, 23, 28, 33, 38, 1, 6, 11, 16, 21, 26, 31, 36, 41]
  | 6 => [16, 21, 26, 31, 36, 41, 4, 9, 14, 19, 24, 29, 34, 39, 2, 7, 12, 17, 22, 27, 32, 37, 0, 5, 10, 15, 20, 25, 30, 35, 40, 3, 8, 13, 18, 23, 28, 33, 38, 1, 6, 11, 16]
  | _ => []

theorem ws7Word57Weak :
    WeakValidRates (fun i => (ws7WordP57 i : ℝ) / (ws7WordQ57 i : ℝ))
      (periodic ws7Word57.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word57)) := by
  apply weakPeriodic_of_paths ws7Word57 (by decide) ws7WordP57 ws7WordQ57
    (by intro i; fin_cases i <;> norm_num [ws7WordQ57]) ws7WordZ57
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word58 : List (Fin 7) := [6, 0, 5, 1, 4, 2, 0, 3, 6, 1, 0, 5, 4, 2, 1, 0, 3, 6, 5, 1, 0, 4, 2, 3, 1, 0, 6, 5, 4, 0, 1, 2, 3, 6, 0, 1, 5, 4, 2, 0, 1, 3]

def ws7WordP58 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 4
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

def ws7WordQ58 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 14
  | 1 => 21
  | 2 => 17
  | 3 => 17
  | 4 => 17
  | 5 => 17
  | 6 => 17
  | _ => 1

def ws7WordZ58 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9]
  | 1 => [5, 9, 13, 17, 0, 4, 8, 12, 16, 20, 3, 7, 11, 15, 19, 2, 6, 10, 14, 18, 1, 5, 9, 13, 17, 0, 4, 8, 12, 16, 20, 3, 7, 11, 15, 19, 2, 6, 10, 14, 18, 1, 5]
  | 2 => [6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6]
  | 3 => [2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2]
  | 4 => [9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9]
  | 5 => [12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12]
  | 6 => [16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16]
  | _ => []

theorem ws7Word58Weak :
    WeakValidRates (fun i => (ws7WordP58 i : ℝ) / (ws7WordQ58 i : ℝ))
      (periodic ws7Word58.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word58)) := by
  apply weakPeriodic_of_paths ws7Word58 (by decide) ws7WordP58 ws7WordQ58
    (by intro i; fin_cases i <;> norm_num [ws7WordQ58]) ws7WordZ58
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word59 : List (Fin 7) := [0, 2, 5, 6, 0, 4, 1, 3, 2, 0, 5, 6, 1, 0, 4, 2, 3, 0, 1, 5, 6, 0, 2, 4, 3, 1, 0, 5, 6, 2, 0, 1, 4, 3, 0, 5, 2, 1, 6, 0, 4, 3, 1]

def ws7WordP59 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 10
  | 1 => 4
  | 2 => 6
  | 3 => 5
  | 4 => 3
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ59 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 43
  | 1 => 25
  | 2 => 43
  | 3 => 43
  | 4 => 26
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ59 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [38, 5, 15, 25, 35, 2, 12, 22, 32, 42, 9, 19, 29, 39, 6, 16, 26, 36, 3, 13, 23, 33, 0, 10, 20, 30, 40, 7, 17, 27, 37, 4, 14, 24, 34, 1, 11, 21, 31, 41, 8, 18, 28, 38]
  | 1 => [0, 4, 8, 12, 16, 20, 24, 3, 7, 11, 15, 19, 23, 2, 6, 10, 14, 18, 22, 1, 5, 9, 13, 17, 21, 25, 4, 8, 12, 16, 20, 24, 3, 7, 11, 15, 19, 23, 2, 6, 10, 14, 18, 0]
  | 2 => [36, 42, 5, 11, 17, 23, 29, 35, 41, 4, 10, 16, 22, 28, 34, 40, 3, 9, 15, 21, 27, 33, 39, 2, 8, 14, 20, 26, 32, 38, 1, 7, 13, 19, 25, 31, 37, 0, 6, 12, 18, 24, 30, 36]
  | 3 => [5, 10, 15, 20, 25, 30, 35, 40, 2, 7, 12, 17, 22, 27, 32, 37, 42, 4, 9, 14, 19, 24, 29, 34, 39, 1, 6, 11, 16, 21, 26, 31, 36, 41, 3, 8, 13, 18, 23, 28, 33, 38, 0, 5]
  | 4 => [7, 10, 13, 16, 19, 22, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 26, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7]
  | 5 => [7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]
  | 6 => [5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5]
  | _ => []

theorem ws7Word59Weak :
    WeakValidRates (fun i => (ws7WordP59 i : ℝ) / (ws7WordQ59 i : ℝ))
      (periodic ws7Word59.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word59)) := by
  apply weakPeriodic_of_paths ws7Word59 (by decide) ws7WordP59 ws7WordQ59
    (by intro i; fin_cases i <;> norm_num [ws7WordQ59]) ws7WordZ59
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word60 : List (Fin 7) := [5, 2, 4, 0, 3, 1, 6, 2, 0, 5, 4, 1, 3, 0, 2, 6, 5, 1, 0, 4, 3, 2, 6, 0, 1, 5, 3, 4, 0, 2, 1, 6, 3, 0, 5, 1, 4, 2, 0, 3, 6, 1, 0]

def ws7WordP60 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 4
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 4
  | 6 => 4
  | _ => 0

def ws7WordQ60 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 34
  | 1 => 25
  | 2 => 15
  | 3 => 23
  | 4 => 43
  | 5 => 35
  | 6 => 35
  | _ => 1

def ws7WordZ60 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 8, 15, 22, 0, 7, 14, 21, 28, 1, 8, 15, 22, 29, 2, 9, 16, 23, 30, 3, 10, 17, 24, 31, 4, 11, 18, 25, 32, 5, 12, 19, 26, 33, 6, 13, 20, 27, 34, 7, 14, 21, 28, 1]
  | 1 => [4, 8, 12, 16, 20, 24, 3, 7, 11, 15, 19, 23, 2, 6, 10, 14, 18, 22, 1, 5, 9, 13, 17, 21, 25, 4, 8, 12, 16, 20, 24, 3, 7, 11, 15, 19, 0, 4, 8, 12, 16, 20, 0, 4]
  | 2 => [12, 14, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12]
  | 3 => [9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17, 20, 23, 3, 6, 9, 12, 15, 18, 0, 3, 6, 9, 12, 15, 0, 3, 6, 9, 12, 15, 18, 0, 3, 6, 9]
  | 4 => [32, 37, 42, 4, 9, 14, 19, 24, 29, 34, 39, 1, 6, 11, 16, 21, 26, 31, 36, 41, 3, 8, 13, 18, 23, 28, 33, 38, 0, 5, 10, 15, 20, 25, 30, 35, 40, 2, 7, 12, 17, 22, 27, 32]
  | 5 => [34, 3, 7, 11, 15, 19, 23, 27, 31, 35, 4, 8, 12, 16, 20, 24, 28, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 29, 33, 2, 6, 10, 14, 18, 22, 26, 30, 34]
  | 6 => [10, 14, 18, 22, 26, 30, 34, 3, 7, 11, 15, 19, 23, 27, 31, 35, 4, 8, 12, 16, 20, 24, 28, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 29, 33, 2, 6, 10]
  | _ => []

theorem ws7Word60Weak :
    WeakValidRates (fun i => (ws7WordP60 i : ℝ) / (ws7WordQ60 i : ℝ))
      (periodic ws7Word60.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word60)) := by
  apply weakPeriodic_of_paths ws7Word60 (by decide) ws7WordP60 ws7WordQ60
    (by intro i; fin_cases i <;> norm_num [ws7WordQ60]) ws7WordZ60
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word61 : List (Fin 7) := [5, 3, 1, 4, 0, 2, 6, 3, 1, 0, 5, 4, 2, 0, 1, 3, 6, 5, 0, 2, 4, 1, 3, 0, 6, 5, 2, 1, 0, 4, 3, 6, 1, 0, 2, 5, 3, 4, 0, 1, 6, 2, 0]

def ws7WordP61 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 5
  | 2 => 6
  | 3 => 3
  | 4 => 5
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ61 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 24
  | 1 => 31
  | 2 => 43
  | 3 => 22
  | 4 => 43
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ61 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 0, 5, 10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 24, 5, 10, 15, 20, 1]
  | 1 => [19, 24, 29, 3, 8, 13, 18, 23, 28, 2, 7, 12, 17, 22, 27, 1, 6, 11, 16, 21, 26, 31, 5, 10, 15, 20, 25, 30, 4, 9, 14, 19, 24, 0, 5, 10, 15, 20, 25, 30, 4, 9, 14, 19]
  | 2 => [10, 16, 22, 28, 34, 40, 3, 9, 15, 21, 27, 33, 39, 2, 8, 14, 20, 26, 32, 38, 1, 7, 13, 19, 25, 31, 37, 0, 6, 12, 18, 24, 30, 36, 42, 5, 11, 17, 23, 29, 35, 41, 4, 10]
  | 3 => [18, 21, 2, 5, 8, 11, 14, 17, 0, 3, 6, 9, 12, 15, 18, 21, 2, 5, 8, 11, 14, 17, 20, 1, 4, 7, 10, 13, 16, 19, 22, 3, 6, 9, 12, 15, 18, 0, 3, 6, 9, 12, 15, 18]
  | 4 => [26, 31, 36, 41, 3, 8, 13, 18, 23, 28, 33, 38, 0, 5, 10, 15, 20, 25, 30, 35, 40, 2, 7, 12, 17, 22, 27, 32, 37, 42, 4, 9, 14, 19, 24, 29, 34, 39, 1, 6, 11, 16, 21, 26]
  | 5 => [8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8]
  | 6 => [2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2]
  | _ => []

theorem ws7Word61Weak :
    WeakValidRates (fun i => (ws7WordP61 i : ℝ) / (ws7WordQ61 i : ℝ))
      (periodic ws7Word61.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word61)) := by
  apply weakPeriodic_of_paths ws7Word61 (by decide) ws7WordP61 ws7WordQ61
    (by intro i; fin_cases i <;> norm_num [ws7WordQ61]) ws7WordZ61
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word62 : List (Fin 7) := [1, 0, 4, 5, 0, 1, 3, 2, 6, 0, 1, 4, 5, 0, 2, 3, 1, 6, 0, 4, 5, 2, 1, 0, 3, 6, 0, 1, 4, 2, 5, 0, 3, 1, 6, 0, 2, 4, 1, 5, 0, 3, 6, 2]

def ws7WordP62 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 3
  | 3 => 5
  | 4 => 5
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ62 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 11
  | 2 => 22
  | 3 => 44
  | 4 => 44
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ62 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [7, 9, 2, 4, 6, 0, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 7, 9, 2, 4, 6, 0, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 7]
  | 1 => [11, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11]
  | 2 => [0, 3, 6, 9, 12, 15, 18, 21, 2, 5, 8, 11, 14, 17, 20, 1, 4, 7, 10, 13, 16, 19, 0, 3, 6, 9, 12, 15, 18, 21, 2, 5, 8, 11, 14, 17, 20, 1, 4, 7, 10, 13, 16, 19, 0]
  | 3 => [11, 16, 21, 26, 31, 36, 41, 2, 7, 12, 17, 22, 27, 32, 37, 42, 3, 8, 13, 18, 23, 28, 33, 38, 43, 4, 9, 14, 19, 24, 29, 34, 39, 0, 5, 10, 15, 20, 25, 30, 35, 40, 1, 6, 11]
  | 4 => [32, 37, 42, 3, 8, 13, 18, 23, 28, 33, 38, 43, 4, 9, 14, 19, 24, 29, 34, 39, 0, 5, 10, 15, 20, 25, 30, 35, 40, 1, 6, 11, 16, 21, 26, 31, 36, 41, 2, 7, 12, 17, 22, 27, 32]
  | 5 => [5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5]
  | 6 => [1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1]
  | _ => []

theorem ws7Word62Weak :
    WeakValidRates (fun i => (ws7WordP62 i : ℝ) / (ws7WordQ62 i : ℝ))
      (periodic ws7Word62.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word62)) := by
  apply weakPeriodic_of_paths ws7Word62 (by decide) ws7WordP62 ws7WordQ62
    (by intro i; fin_cases i <;> norm_num [ws7WordQ62]) ws7WordZ62
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word63 : List (Fin 7) := [3, 4, 1, 0, 5, 6, 2, 1, 0, 3, 4, 0, 1, 5, 2, 6, 0, 3, 1, 4, 0, 2, 5, 1, 6, 0, 3, 4, 1, 2, 0, 5, 6, 0, 1, 3, 4, 2, 0, 5, 1, 6, 0, 2]

def ws7WordP63 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 2
  | 1 => 3
  | 2 => 2
  | 3 => 5
  | 4 => 5
  | 5 => 5
  | 6 => 1
  | _ => 0

def ws7WordQ63 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 17
  | 2 => 15
  | 3 => 44
  | 4 => 44
  | 5 => 44
  | 6 => 9
  | _ => 1

def ws7WordZ63 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [2, 4, 6, 8, 1, 3, 5, 7, 9, 2, 4, 6, 0, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 7, 9, 2, 4, 6, 0, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2]
  | 1 => [11, 14, 17, 3, 6, 9, 12, 15, 1, 4, 7, 10, 13, 0, 3, 6, 9, 12, 15, 1, 4, 7, 10, 13, 0, 3, 6, 9, 12, 0, 3, 6, 9, 12, 15, 1, 4, 7, 10, 13, 16, 2, 5, 8, 11]
  | 2 => [0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 0]
  | 3 => [42, 3, 8, 13, 18, 23, 28, 33, 38, 43, 4, 9, 14, 19, 24, 29, 34, 39, 0, 5, 10, 15, 20, 25, 30, 35, 40, 1, 6, 11, 16, 21, 26, 31, 36, 41, 2, 7, 12, 17, 22, 27, 32, 37, 42]
  | 4 => [36, 41, 2, 7, 12, 17, 22, 27, 32, 37, 42, 3, 8, 13, 18, 23, 28, 33, 38, 43, 4, 9, 14, 19, 24, 29, 34, 39, 0, 5, 10, 15, 20, 25, 30, 35, 40, 1, 6, 11, 16, 21, 26, 31, 36]
  | 5 => [20, 25, 30, 35, 40, 1, 6, 11, 16, 21, 26, 31, 36, 41, 2, 7, 12, 17, 22, 27, 32, 37, 42, 3, 8, 13, 18, 23, 28, 33, 38, 43, 4, 9, 14, 19, 24, 29, 34, 39, 0, 5, 10, 15, 20]
  | 6 => [2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2]
  | _ => []

theorem ws7Word63Weak :
    WeakValidRates (fun i => (ws7WordP63 i : ℝ) / (ws7WordQ63 i : ℝ))
      (periodic ws7Word63.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word63)) := by
  apply weakPeriodic_of_paths ws7Word63 (by decide) ws7WordP63 ws7WordQ63
    (by intro i; fin_cases i <;> norm_num [ws7WordQ63]) ws7WordZ63
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word64 : List (Fin 7) := [3, 6, 2, 0, 1, 5, 4, 3, 0, 2, 1, 6, 5, 0, 3, 4, 1, 2, 0, 6, 1, 5, 3, 0, 2, 4, 1, 6, 0, 3, 5, 2, 1, 0, 4, 6, 3, 0, 1, 2, 5, 4, 0, 1]

def ws7WordP64 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | 4 => 1
  | 5 => 1
  | 6 => 2
  | _ => 0

def ws7WordQ64 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 44
  | 1 => 17
  | 2 => 22
  | 3 => 22
  | 4 => 9
  | 5 => 9
  | 6 => 19
  | _ => 1

def ws7WordZ64 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [10, 19, 28, 37, 2, 11, 20, 29, 38, 3, 12, 21, 30, 39, 4, 13, 22, 31, 40, 5, 14, 23, 32, 41, 6, 15, 24, 33, 42, 7, 16, 25, 34, 43, 8, 17, 26, 35, 0, 9, 18, 27, 36, 1, 10]
  | 1 => [1, 4, 7, 10, 13, 0, 3, 6, 9, 12, 15, 1, 4, 7, 10, 13, 16, 2, 5, 8, 11, 0, 3, 6, 9, 12, 15, 1, 4, 7, 10, 13, 16, 2, 5, 8, 11, 14, 17, 3, 6, 9, 12, 15, 1]
  | 2 => [14, 17, 20, 1, 4, 7, 10, 13, 16, 19, 0, 3, 6, 9, 12, 15, 18, 21, 2, 5, 8, 11, 14, 17, 20, 1, 4, 7, 10, 13, 16, 19, 0, 3, 6, 9, 12, 15, 18, 21, 2, 5, 8, 11, 14]
  | 3 => [21, 2, 5, 8, 11, 14, 17, 20, 1, 4, 7, 10, 13, 16, 19, 0, 3, 6, 9, 12, 15, 18, 21, 2, 5, 8, 11, 14, 17, 20, 1, 4, 7, 10, 13, 16, 19, 0, 3, 6, 9, 12, 15, 18, 21]
  | 4 => [2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2]
  | 5 => [4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4]
  | 6 => [16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16]
  | _ => []

theorem ws7Word64Weak :
    WeakValidRates (fun i => (ws7WordP64 i : ℝ) / (ws7WordQ64 i : ℝ))
      (periodic ws7Word64.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word64)) := by
  apply weakPeriodic_of_paths ws7Word64 (by decide) ws7WordP64 ws7WordQ64
    (by intro i; fin_cases i <;> norm_num [ws7WordQ64]) ws7WordZ64
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word65 : List (Fin 7) := [4, 0, 2, 1, 6, 3, 0, 5, 2, 4, 1, 0, 3, 6, 2, 1, 0, 5, 4, 2, 3, 0, 1, 6, 5, 0, 2, 4, 1, 3, 0, 6, 2, 5, 1, 0, 4, 3, 2, 6, 0, 1, 5, 3]

def ws7WordP65 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 3
  | 2 => 1
  | 3 => 1
  | 4 => 5
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ65 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 44
  | 1 => 19
  | 2 => 7
  | 3 => 8
  | 4 => 44
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ65 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [30, 39, 4, 13, 22, 31, 40, 5, 14, 23, 32, 41, 6, 15, 24, 33, 42, 7, 16, 25, 34, 43, 8, 17, 26, 35, 0, 9, 18, 27, 36, 1, 10, 19, 28, 37, 2, 11, 20, 29, 38, 3, 12, 21, 30]
  | 1 => [8, 11, 14, 17, 1, 4, 7, 10, 13, 16, 19, 3, 6, 9, 12, 15, 0, 3, 6, 9, 12, 15, 18, 2, 5, 8, 11, 14, 17, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12, 15, 18, 2, 5, 8]
  | 2 => [5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5]
  | 3 => [0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 0]
  | 4 => [39, 0, 5, 10, 15, 20, 25, 30, 35, 40, 1, 6, 11, 16, 21, 26, 31, 36, 41, 2, 7, 12, 17, 22, 27, 32, 37, 42, 3, 8, 13, 18, 23, 28, 33, 38, 43, 4, 9, 14, 19, 24, 29, 34, 39]
  | 5 => [1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1]
  | 6 => [4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4]
  | _ => []

theorem ws7Word65Weak :
    WeakValidRates (fun i => (ws7WordP65 i : ℝ) / (ws7WordQ65 i : ℝ))
      (periodic ws7Word65.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word65)) := by
  apply weakPeriodic_of_paths ws7Word65 (by decide) ws7WordP65 ws7WordQ65
    (by intro i; fin_cases i <;> norm_num [ws7WordQ65]) ws7WordZ65
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word66 : List (Fin 7) := [6, 4, 0, 3, 1, 5, 2, 0, 6, 4, 1, 3, 0, 2, 5, 4, 1, 6, 0, 3, 2, 0, 1, 5, 4, 3, 6, 0, 2, 1, 4, 0, 5, 3, 6, 2, 1, 0, 4, 3, 5, 0, 1, 2]

def ws7WordP66 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 3
  | 4 => 1
  | 5 => 5
  | 6 => 1
  | _ => 0

def ws7WordQ66 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 13
  | 2 => 22
  | 3 => 23
  | 4 => 8
  | 5 => 44
  | 6 => 9
  | _ => 1

def ws7WordZ66 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2]
  | 1 => [3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3]
  | 2 => [3, 6, 9, 12, 15, 18, 21, 2, 5, 8, 11, 14, 17, 20, 1, 4, 7, 10, 13, 16, 19, 0, 3, 6, 9, 12, 15, 18, 21, 2, 5, 8, 11, 14, 17, 20, 1, 4, 7, 10, 13, 16, 19, 22, 3]
  | 3 => [12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17, 20, 23, 3, 6, 9, 12, 15, 18, 0, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12]
  | 4 => [5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5]
  | 5 => [15, 20, 25, 30, 35, 40, 1, 6, 11, 16, 21, 26, 31, 36, 41, 2, 7, 12, 17, 22, 27, 32, 37, 42, 3, 8, 13, 18, 23, 28, 33, 38, 43, 4, 9, 14, 19, 24, 29, 34, 39, 0, 5, 10, 15]
  | 6 => [9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  | _ => []

theorem ws7Word66Weak :
    WeakValidRates (fun i => (ws7WordP66 i : ℝ) / (ws7WordQ66 i : ℝ))
      (periodic ws7Word66.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word66)) := by
  apply weakPeriodic_of_paths ws7Word66 (by decide) ws7WordP66 ws7WordQ66
    (by intro i; fin_cases i <;> norm_num [ws7WordQ66]) ws7WordZ66
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word67 : List (Fin 7) := [1, 5, 2, 0, 3, 6, 4, 1, 5, 0, 2, 3, 4, 1, 0, 6, 5, 2, 0, 3, 1, 4, 6, 5, 0, 2, 1, 3, 4, 0, 5, 6, 2, 1, 0, 3, 4, 5, 0, 1, 2, 6, 3, 4, 0]

def ws7WordP67 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 7
  | 2 => 2
  | 3 => 3
  | 4 => 1
  | 5 => 1
  | 6 => 3
  | _ => 0

def ws7WordQ67 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 45
  | 2 => 15
  | 3 => 23
  | 4 => 8
  | 5 => 8
  | 6 => 28
  | _ => 1

def ws7WordZ67 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1]
  | 1 => [38, 0, 7, 14, 21, 28, 35, 42, 4, 11, 18, 25, 32, 39, 1, 8, 15, 22, 29, 36, 43, 5, 12, 19, 26, 33, 40, 2, 9, 16, 23, 30, 37, 44, 6, 13, 20, 27, 34, 41, 3, 10, 17, 24, 31, 38]
  | 2 => [9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9]
  | 3 => [7, 10, 13, 16, 19, 0, 3, 6, 9, 12, 15, 18, 0, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17, 20, 23, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7]
  | 4 => [1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1]
  | 5 => [7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7]
  | 6 => [11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 24, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11]
  | _ => []

theorem ws7Word67Weak :
    WeakValidRates (fun i => (ws7WordP67 i : ℝ) / (ws7WordQ67 i : ℝ))
      (periodic ws7Word67.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word67)) := by
  apply weakPeriodic_of_paths ws7Word67 (by decide) ws7WordP67 ws7WordQ67
    (by intro i; fin_cases i <;> norm_num [ws7WordQ67]) ws7WordZ67
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word68 : List (Fin 7) := [6, 3, 4, 0, 2, 1, 5, 3, 0, 6, 4, 1, 2, 0, 5, 3, 1, 0, 6, 4, 2, 0, 1, 3, 5, 0, 2, 6, 1, 4, 0, 3, 5, 1, 2, 0, 6, 4, 3, 1, 0, 5, 2, 0, 1]

def ws7WordP68 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 8
  | 2 => 5
  | 3 => 3
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ68 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 14
  | 1 => 45
  | 2 => 38
  | 3 => 23
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ68 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 12, 1, 4, 7, 10, 0, 3, 6, 9, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 0, 3]
  | 1 => [0, 8, 16, 24, 32, 40, 3, 11, 19, 27, 35, 43, 6, 14, 22, 30, 38, 1, 9, 17, 25, 33, 41, 4, 12, 20, 28, 36, 44, 7, 15, 23, 31, 39, 2, 10, 18, 26, 34, 42, 5, 13, 21, 29, 37, 0]
  | 2 => [14, 19, 24, 29, 34, 1, 6, 11, 16, 21, 26, 31, 36, 3, 8, 13, 18, 23, 28, 33, 38, 5, 10, 15, 20, 25, 30, 0, 5, 10, 15, 20, 25, 30, 35, 2, 7, 12, 17, 22, 27, 32, 37, 4, 9, 14]
  | 3 => [19, 22, 2, 5, 8, 11, 14, 17, 0, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17, 20, 23, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19]
  | 4 => [7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7]
  | 5 => [3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3]
  | 6 => [8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8]
  | _ => []

theorem ws7Word68Weak :
    WeakValidRates (fun i => (ws7WordP68 i : ℝ) / (ws7WordQ68 i : ℝ))
      (periodic ws7Word68.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word68)) := by
  apply weakPeriodic_of_paths ws7Word68 (by decide) ws7WordP68 ws7WordQ68
    (by intro i; fin_cases i <;> norm_num [ws7WordQ68]) ws7WordZ68
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word69 : List (Fin 7) := [0, 2, 4, 1, 3, 0, 6, 1, 2, 5, 0, 4, 1, 3, 0, 2, 6, 1, 5, 0, 4, 2, 3, 1, 0, 6, 5, 2, 1, 0, 4, 3, 0, 1, 2, 6, 5, 0, 1, 4, 2, 3, 0, 1, 6, 5]

def ws7WordP69 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 6
  | 2 => 3
  | 3 => 5
  | 4 => 5
  | 5 => 3
  | 6 => 3
  | _ => 0

def ws7WordQ69 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 14
  | 1 => 31
  | 2 => 20
  | 3 => 46
  | 4 => 46
  | 5 => 28
  | 6 => 28
  | _ => 1

def ws7WordZ69 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [11, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11]
  | 1 => [13, 19, 25, 31, 6, 12, 18, 24, 0, 6, 12, 18, 24, 0, 6, 12, 18, 24, 0, 6, 12, 18, 24, 30, 5, 11, 17, 23, 29, 4, 10, 16, 22, 28, 3, 9, 15, 21, 27, 2, 8, 14, 20, 26, 1, 7, 13]
  | 2 => [15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 20, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12, 15]
  | 3 => [24, 29, 34, 39, 44, 3, 8, 13, 18, 23, 28, 33, 38, 43, 2, 7, 12, 17, 22, 27, 32, 37, 42, 1, 6, 11, 16, 21, 26, 31, 36, 41, 0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 4, 9, 14, 19, 24]
  | 4 => [33, 38, 43, 2, 7, 12, 17, 22, 27, 32, 37, 42, 1, 6, 11, 16, 21, 26, 31, 36, 41, 0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 4, 9, 14, 19, 24, 29, 34, 39, 44, 3, 8, 13, 18, 23, 28, 33]
  | 5 => [1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1]
  | 6 => [5, 8, 11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5]
  | _ => []

theorem ws7Word69Weak :
    WeakValidRates (fun i => (ws7WordP69 i : ℝ) / (ws7WordQ69 i : ℝ))
      (periodic ws7Word69.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word69)) := by
  apply weakPeriodic_of_paths ws7Word69 (by decide) ws7WordP69 ws7WordQ69
    (by intro i; fin_cases i <;> norm_num [ws7WordQ69]) ws7WordZ69
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word70 : List (Fin 7) := [3, 0, 1, 2, 5, 0, 1, 4, 3, 6, 0, 2, 1, 5, 3, 0, 4, 1, 6, 2, 0, 3, 1, 5, 0, 4, 2, 1, 6, 0, 3, 5, 1, 0, 2, 4, 6, 1, 0, 3, 5, 2, 1, 0, 4, 6]

def ws7WordP70 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 8
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 3
  | 6 => 3
  | _ => 0

def ws7WordQ70 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 14
  | 1 => 41
  | 2 => 23
  | 3 => 17
  | 4 => 46
  | 5 => 28
  | 6 => 28
  | _ => 1

def ws7WordZ70 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [8, 11, 0, 3, 6, 9, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8]
  | 1 => [25, 33, 41, 8, 16, 24, 32, 0, 8, 16, 24, 32, 40, 7, 15, 23, 31, 39, 6, 14, 22, 30, 38, 5, 13, 21, 29, 37, 4, 12, 20, 28, 36, 3, 11, 19, 27, 35, 2, 10, 18, 26, 34, 1, 9, 17, 25]
  | 2 => [12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17, 20, 23, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17, 20, 0, 3, 6, 9, 12]
  | 3 => [14, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14]
  | 4 => [8, 13, 18, 23, 28, 33, 38, 43, 2, 7, 12, 17, 22, 27, 32, 37, 42, 1, 6, 11, 16, 21, 26, 31, 36, 41, 0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 4, 9, 14, 19, 24, 29, 34, 39, 44, 3, 8]
  | 5 => [15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 3, 6, 9, 12, 15, 18, 21, 24, 0, 3, 6, 9, 12, 15, 18, 21, 24, 0, 3, 6, 9, 12, 15]
  | 6 => [0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 3, 6, 9, 12, 15, 18, 21, 24, 0, 3, 6, 9, 12, 15, 18, 21, 24, 0]
  | _ => []

theorem ws7Word70Weak :
    WeakValidRates (fun i => (ws7WordP70 i : ℝ) / (ws7WordQ70 i : ℝ))
      (periodic ws7Word70.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word70)) := by
  apply weakPeriodic_of_paths ws7Word70 (by decide) ws7WordP70 ws7WordQ70
    (by intro i; fin_cases i <;> norm_num [ws7WordQ70]) ws7WordZ70
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word71 : List (Fin 7) := [3, 4, 1, 0, 5, 2, 6, 1, 0, 3, 4, 2, 0, 1, 5, 3, 6, 0, 2, 1, 4, 3, 0, 5, 1, 2, 6, 0, 4, 3, 1, 0, 2, 5, 6, 0, 1, 4, 3, 2, 0, 5, 1, 6, 0, 2]

def ws7WordP71 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 4
  | 2 => 4
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 2
  | _ => 0

def ws7WordQ71 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 14
  | 1 => 23
  | 2 => 27
  | 3 => 25
  | 4 => 28
  | 5 => 28
  | 6 => 19
  | _ => 1

def ws7WordZ71 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 12, 1, 4, 7, 10, 0, 3, 6, 9, 12, 1, 4, 7, 10, 0, 3]
  | 1 => [15, 19, 23, 4, 8, 12, 16, 20, 1, 5, 9, 13, 17, 21, 2, 6, 10, 14, 18, 22, 3, 7, 11, 15, 19, 0, 4, 8, 12, 16, 20, 1, 5, 9, 13, 17, 21, 2, 6, 10, 14, 18, 22, 3, 7, 11, 15]
  | 2 => [1, 5, 9, 13, 17, 21, 0, 4, 8, 12, 16, 20, 0, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 25, 2, 6, 10, 14, 18, 22, 26, 3, 7, 11, 15, 19, 23, 27, 4, 8, 12, 16, 20, 24, 1]
  | 3 => [23, 1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 0, 3, 6, 9, 12, 15, 0, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23]
  | 4 => [24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 3, 6, 9, 12, 15, 18, 21, 24, 0, 3, 6, 9, 12, 15, 18, 21, 24, 0, 3, 6, 9, 12, 15, 18, 21, 24]
  | 5 => [12, 15, 18, 21, 24, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 3, 6, 9, 12, 15, 18, 21, 24, 0, 3, 6, 9, 12]
  | 6 => [4, 6, 8, 10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 0, 2, 4]
  | _ => []

theorem ws7Word71Weak :
    WeakValidRates (fun i => (ws7WordP71 i : ℝ) / (ws7WordQ71 i : ℝ))
      (periodic ws7Word71.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word71)) := by
  apply weakPeriodic_of_paths ws7Word71 (by decide) ws7WordP71 ws7WordQ71
    (by intro i; fin_cases i <;> norm_num [ws7WordQ71]) ws7WordZ71
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word72 : List (Fin 7) := [5, 3, 1, 0, 2, 6, 4, 0, 1, 3, 5, 2, 0, 4, 1, 6, 0, 3, 2, 5, 1, 0, 4, 6, 3, 2, 0, 1, 5, 4, 0, 2, 3, 6, 1, 0, 4, 5, 2, 0, 3, 1, 6, 2, 0, 4]

def ws7WordP72 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 4
  | 2 => 4
  | 3 => 3
  | 4 => 1
  | 5 => 5
  | 6 => 4
  | _ => 0

def ws7WordQ72 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 23
  | 1 => 27
  | 2 => 27
  | 3 => 23
  | 4 => 8
  | 5 => 46
  | 6 => 37
  | _ => 1

def ws7WordZ72 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [7, 12, 17, 22, 4, 9, 14, 19, 1, 6, 11, 16, 21, 3, 8, 13, 18, 0, 5, 10, 15, 20, 2, 7, 12, 17, 22, 4, 9, 14, 19, 1, 6, 11, 16, 21, 3, 8, 13, 18, 0, 5, 10, 15, 20, 2, 7]
  | 1 => [19, 23, 27, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 0, 4, 8, 12, 16, 20, 0, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 25, 2, 6, 10, 14, 18, 22, 26, 3, 7, 11, 15, 19]
  | 2 => [8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 25, 2, 6, 10, 14, 18, 22, 26, 3, 7, 11, 15, 19, 23, 27, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 25, 2, 6, 10, 14, 18, 0, 4, 8]
  | 3 => [17, 20, 0, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17, 20, 0, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17]
  | 4 => [1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1]
  | 5 => [41, 0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 4, 9, 14, 19, 24, 29, 34, 39, 44, 3, 8, 13, 18, 23, 28, 33, 38, 43, 2, 7, 12, 17, 22, 27, 32, 37, 42, 1, 6, 11, 16, 21, 26, 31, 36, 41]
  | 6 => [14, 18, 22, 26, 30, 34, 1, 5, 9, 13, 17, 21, 25, 29, 33, 37, 4, 8, 12, 16, 20, 24, 28, 32, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 3, 7, 11, 15, 19, 23, 27, 31, 35, 2, 6, 10, 14]
  | _ => []

theorem ws7Word72Weak :
    WeakValidRates (fun i => (ws7WordP72 i : ℝ) / (ws7WordQ72 i : ℝ))
      (periodic ws7Word72.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word72)) := by
  apply weakPeriodic_of_paths ws7Word72 (by decide) ws7WordP72 ws7WordQ72
    (by intro i; fin_cases i <;> norm_num [ws7WordQ72]) ws7WordZ72
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word73 : List (Fin 7) := [0, 3, 6, 2, 0, 1, 5, 4, 3, 0, 2, 1, 6, 5, 0, 4, 3, 1, 2, 0, 6, 5, 4, 1, 0, 3, 2, 5, 0, 1, 6, 4, 3, 0, 2, 1, 5, 4, 0, 6, 3, 1, 2, 0, 5, 4, 1]

def ws7WordP73 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 4
  | 1 => 8
  | 2 => 6
  | 3 => 1
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | _ => 0

def ws7WordQ73 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 19
  | 1 => 47
  | 2 => 47
  | 3 => 8
  | 4 => 8
  | 5 => 25
  | 6 => 19
  | _ => 1

def ws7WordZ73 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [16, 1, 5, 9, 13, 0, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 18, 3, 7, 11, 15, 19, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 18, 3, 7, 11, 15, 19, 4, 8, 12, 16]
  | 1 => [0, 8, 16, 24, 32, 40, 1, 9, 17, 25, 33, 41, 2, 10, 18, 26, 34, 42, 3, 11, 19, 27, 35, 43, 4, 12, 20, 28, 36, 44, 5, 13, 21, 29, 37, 45, 6, 14, 22, 30, 38, 46, 7, 15, 23, 31, 39, 0]
  | 2 => [28, 34, 40, 46, 5, 11, 17, 23, 29, 35, 41, 0, 6, 12, 18, 24, 30, 36, 42, 1, 7, 13, 19, 25, 31, 37, 43, 2, 8, 14, 20, 26, 32, 38, 44, 3, 9, 15, 21, 27, 33, 39, 45, 4, 10, 16, 22, 28]
  | 3 => [6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6]
  | 4 => [1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1]
  | 5 => [7, 10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7]
  | 6 => [14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14]
  | _ => []

theorem ws7Word73Weak :
    WeakValidRates (fun i => (ws7WordP73 i : ℝ) / (ws7WordQ73 i : ℝ))
      (periodic ws7Word73.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word73)) := by
  apply weakPeriodic_of_paths ws7Word73 (by decide) ws7WordP73 ws7WordQ73
    (by intro i; fin_cases i <;> norm_num [ws7WordQ73]) ws7WordZ73
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word74 : List (Fin 7) := [1, 2, 0, 3, 5, 4, 1, 0, 2, 6, 3, 0, 4, 1, 5, 2, 0, 6, 3, 1, 4, 0, 2, 5, 3, 0, 1, 6, 2, 4, 0, 3, 5, 1, 2, 0, 4, 6, 3, 0, 1, 2, 5, 4, 0, 3, 6]

def ws7WordP74 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 10
  | 1 => 4
  | 2 => 5
  | 3 => 1
  | 4 => 1
  | 5 => 5
  | 6 => 2
  | _ => 0

def ws7WordQ74 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 47
  | 1 => 27
  | 2 => 34
  | 3 => 7
  | 4 => 8
  | 5 => 47
  | 6 => 19
  | _ => 1

def ws7WordZ74 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [23, 33, 43, 6, 16, 26, 36, 46, 9, 19, 29, 39, 2, 12, 22, 32, 42, 5, 15, 25, 35, 45, 8, 18, 28, 38, 1, 11, 21, 31, 41, 4, 14, 24, 34, 44, 7, 17, 27, 37, 0, 10, 20, 30, 40, 3, 13, 23]
  | 1 => [27, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 25, 2, 6, 10, 14, 18, 22, 0, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 25, 2, 6, 10, 14, 18, 22, 26, 3, 7, 11, 15, 19, 23, 27]
  | 2 => [26, 31, 2, 7, 12, 17, 22, 27, 32, 3, 8, 13, 18, 23, 28, 33, 4, 9, 14, 19, 24, 29, 34, 5, 10, 15, 20, 25, 30, 1, 6, 11, 16, 21, 26, 0, 5, 10, 15, 20, 25, 30, 1, 6, 11, 16, 21, 26]
  | 3 => [1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1]
  | 4 => [3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3]
  | 5 => [23, 28, 33, 38, 43, 1, 6, 11, 16, 21, 26, 31, 36, 41, 46, 4, 9, 14, 19, 24, 29, 34, 39, 44, 2, 7, 12, 17, 22, 27, 32, 37, 42, 0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 3, 8, 13, 18, 23]
  | 6 => [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1]
  | _ => []

theorem ws7Word74Weak :
    WeakValidRates (fun i => (ws7WordP74 i : ℝ) / (ws7WordQ74 i : ℝ))
      (periodic ws7Word74.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word74)) := by
  apply weakPeriodic_of_paths ws7Word74 (by decide) ws7WordP74 ws7WordQ74
    (by intro i; fin_cases i <;> norm_num [ws7WordQ74]) ws7WordZ74
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word75 : List (Fin 7) := [1, 2, 6, 0, 5, 3, 1, 4, 2, 0, 6, 3, 1, 0, 5, 2, 4, 0, 1, 3, 6, 2, 0, 5, 1, 3, 4, 0, 2, 6, 1, 0, 3, 5, 2, 4, 1, 0, 3, 6, 0, 2, 1, 5, 4, 3, 0]

def ws7WordP75 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 8
  | 2 => 4
  | 3 => 1
  | 4 => 5
  | 5 => 2
  | 6 => 2
  | _ => 0

def ws7WordQ75 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 47
  | 2 => 27
  | 3 => 7
  | 4 => 47
  | 5 => 19
  | 6 => 19
  | _ => 1

def ws7WordZ75 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 1, 2, 3, 0, 1, 2, 3, 4, 5, 1]
  | 1 => [39, 0, 8, 16, 24, 32, 40, 1, 9, 17, 25, 33, 41, 2, 10, 18, 26, 34, 42, 3, 11, 19, 27, 35, 43, 4, 12, 20, 28, 36, 44, 5, 13, 21, 29, 37, 45, 6, 14, 22, 30, 38, 46, 7, 15, 23, 31, 39]
  | 2 => [21, 25, 2, 6, 10, 14, 18, 22, 26, 3, 7, 11, 15, 19, 23, 27, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 25, 2, 6, 10, 14, 18, 22, 0, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21]
  | 3 => [1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 0, 1]
  | 4 => [10, 15, 20, 25, 30, 35, 40, 45, 3, 8, 13, 18, 23, 28, 33, 38, 43, 1, 6, 11, 16, 21, 26, 31, 36, 41, 46, 4, 9, 14, 19, 24, 29, 34, 39, 44, 2, 7, 12, 17, 22, 27, 32, 37, 42, 0, 5, 10]
  | 5 => [8, 10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8]
  | 6 => [15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15]
  | _ => []

theorem ws7Word75Weak :
    WeakValidRates (fun i => (ws7WordP75 i : ℝ) / (ws7WordQ75 i : ℝ))
      (periodic ws7Word75.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word75)) := by
  apply weakPeriodic_of_paths ws7Word75 (by decide) ws7WordP75 ws7WordQ75
    (by intro i; fin_cases i <;> norm_num [ws7WordQ75]) ws7WordZ75
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word76 : List (Fin 7) := [1, 6, 2, 0, 5, 4, 1, 3, 0, 2, 6, 5, 0, 1, 4, 3, 2, 0, 6, 1, 5, 4, 0, 3, 2, 5, 1, 0, 6, 4, 2, 3, 0, 1, 5, 2, 0, 4, 6, 3, 1, 0, 2, 5, 4, 0, 3]

def ws7WordP76 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 4
  | 1 => 4
  | 2 => 1
  | 3 => 6
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | _ => 0

def ws7WordQ76 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 19
  | 1 => 27
  | 2 => 7
  | 3 => 47
  | 4 => 8
  | 5 => 17
  | 6 => 29
  | _ => 1

def ws7WordZ76 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 0, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 18, 3, 7, 11, 15, 19, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 0, 4]
  | 1 => [27, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 25, 2, 6, 10, 14, 18, 22, 0, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 25, 2, 6, 10, 14, 18, 22, 26, 3, 7, 11, 15, 19, 23, 27]
  | 2 => [4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4]
  | 3 => [0, 6, 12, 18, 24, 30, 36, 42, 1, 7, 13, 19, 25, 31, 37, 43, 2, 8, 14, 20, 26, 32, 38, 44, 3, 9, 15, 21, 27, 33, 39, 45, 4, 10, 16, 22, 28, 34, 40, 46, 5, 11, 17, 23, 29, 35, 41, 0]
  | 4 => [2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2]
  | 5 => [8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8]
  | 6 => [26, 29, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26]
  | _ => []

theorem ws7Word76Weak :
    WeakValidRates (fun i => (ws7WordP76 i : ℝ) / (ws7WordQ76 i : ℝ))
      (periodic ws7Word76.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word76)) := by
  apply weakPeriodic_of_paths ws7Word76 (by decide) ws7WordP76 ws7WordQ76
    (by intro i; fin_cases i <;> norm_num [ws7WordQ76]) ws7WordZ76
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word77 : List (Fin 7) := [3, 0, 2, 5, 1, 3, 0, 4, 2, 6, 1, 0, 3, 5, 2, 1, 0, 4, 3, 6, 0, 2, 1, 5, 3, 0, 4, 1, 2, 6, 0, 5, 3, 1, 0, 2, 4, 6, 0, 1, 3, 5, 2, 0, 1, 4, 6]

def ws7WordP77 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 1
  | 2 => 5
  | 3 => 2
  | 4 => 5
  | 5 => 2
  | 6 => 3
  | _ => 0

def ws7WordQ77 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 24
  | 1 => 6
  | 2 => 34
  | 3 => 15
  | 4 => 47
  | 5 => 19
  | 6 => 29
  | _ => 1

def ws7WordZ77 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 24, 5, 10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 0, 5, 10, 15, 0, 5, 10, 15, 20, 1, 6, 11, 16]
  | 1 => [2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 0, 1, 2]
  | 2 => [24, 29, 34, 5, 10, 15, 20, 25, 30, 1, 6, 11, 16, 21, 26, 0, 5, 10, 15, 20, 25, 30, 1, 6, 11, 16, 21, 26, 31, 2, 7, 12, 17, 22, 27, 32, 3, 8, 13, 18, 23, 28, 33, 4, 9, 14, 19, 24]
  | 3 => [14, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14]
  | 4 => [7, 12, 17, 22, 27, 32, 37, 42, 0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 3, 8, 13, 18, 23, 28, 33, 38, 43, 1, 6, 11, 16, 21, 26, 31, 36, 41, 46, 4, 9, 14, 19, 24, 29, 34, 39, 44, 2, 7]
  | 5 => [11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11]
  | 6 => [0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26, 29, 3, 6, 9, 12, 15, 18, 21, 24, 0, 3, 6, 9, 12, 15, 18, 21, 24, 0]
  | _ => []

theorem ws7Word77Weak :
    WeakValidRates (fun i => (ws7WordP77 i : ℝ) / (ws7WordQ77 i : ℝ))
      (periodic ws7Word77.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word77)) := by
  apply weakPeriodic_of_paths ws7Word77 (by decide) ws7WordP77 ws7WordQ77
    (by intro i; fin_cases i <;> norm_num [ws7WordQ77]) ws7WordZ77
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word78 : List (Fin 7) := [3, 1, 0, 2, 5, 1, 6, 0, 3, 4, 1, 2, 0, 5, 1, 6, 3, 0, 4, 2, 1, 0, 5, 3, 1, 6, 0, 2, 4, 1, 3, 0, 5, 1, 2, 6, 0, 4, 1, 3, 0, 5, 2, 1, 6, 0, 4]

def ws7WordP78 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 1
  | 2 => 6
  | 3 => 1
  | 4 => 5
  | 5 => 5
  | 6 => 2
  | _ => 0

def ws7WordQ78 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 33
  | 1 => 5
  | 2 => 47
  | 3 => 8
  | 4 => 47
  | 5 => 47
  | 6 => 19
  | _ => 1

def ws7WordZ78 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [11, 18, 25, 0, 7, 14, 21, 28, 2, 9, 16, 23, 30, 4, 11, 18, 25, 32, 6, 13, 20, 27, 1, 8, 15, 22, 29, 3, 10, 17, 24, 31, 5, 12, 19, 26, 33, 7, 14, 21, 28, 2, 9, 16, 23, 30, 4, 11]
  | 1 => [3, 4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3]
  | 2 => [25, 31, 37, 43, 2, 8, 14, 20, 26, 32, 38, 44, 3, 9, 15, 21, 27, 33, 39, 45, 4, 10, 16, 22, 28, 34, 40, 46, 5, 11, 17, 23, 29, 35, 41, 0, 6, 12, 18, 24, 30, 36, 42, 1, 7, 13, 19, 25]
  | 3 => [8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8]
  | 4 => [0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 3, 8, 13, 18, 23, 28, 33, 38, 43, 1, 6, 11, 16, 21, 26, 31, 36, 41, 46, 4, 9, 14, 19, 24, 29, 34, 39, 44, 2, 7, 12, 17, 22, 27, 32, 37, 42, 0]
  | 5 => [26, 31, 36, 41, 46, 4, 9, 14, 19, 24, 29, 34, 39, 44, 2, 7, 12, 17, 22, 27, 32, 37, 42, 0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 3, 8, 13, 18, 23, 28, 33, 38, 43, 1, 6, 11, 16, 21, 26]
  | 6 => [5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5]
  | _ => []

theorem ws7Word78Weak :
    WeakValidRates (fun i => (ws7WordP78 i : ℝ) / (ws7WordQ78 i : ℝ))
      (periodic ws7Word78.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word78)) := by
  apply weakPeriodic_of_paths ws7Word78 (by decide) ws7WordP78 ws7WordQ78
    (by intro i; fin_cases i <;> norm_num [ws7WordQ78]) ws7WordZ78
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word79 : List (Fin 7) := [4, 6, 3, 0, 1, 5, 2, 0, 4, 3, 6, 1, 0, 2, 5, 4, 0, 3, 1, 6, 2, 0, 5, 4, 1, 3, 0, 2, 6, 5, 0, 1, 4, 3, 2, 0, 5, 1, 6, 4, 0, 2, 3, 5, 1, 0, 2]

def ws7WordP79 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 4
  | 1 => 4
  | 2 => 6
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | _ => 0

def ws7WordQ79 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 19
  | 1 => 27
  | 2 => 41
  | 3 => 8
  | 4 => 8
  | 5 => 17
  | 6 => 19
  | _ => 1

def ws7WordZ79 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [7, 11, 15, 19, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 0, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 0, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 18, 3, 7]
  | 1 => [9, 13, 17, 21, 25, 2, 6, 10, 14, 18, 22, 26, 3, 7, 11, 15, 19, 23, 27, 4, 8, 12, 16, 20, 24, 1, 5, 9, 13, 17, 21, 25, 2, 6, 10, 14, 18, 22, 0, 4, 8, 12, 16, 20, 24, 1, 5, 9]
  | 2 => [0, 6, 12, 18, 24, 30, 36, 1, 7, 13, 19, 25, 31, 37, 2, 8, 14, 20, 26, 32, 38, 3, 9, 15, 21, 27, 33, 39, 4, 10, 16, 22, 28, 34, 40, 5, 11, 17, 23, 29, 35, 41, 6, 12, 18, 24, 30, 0]
  | 3 => [5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5]
  | 4 => [7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]
  | 5 => [6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6]
  | 6 => [17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17, 0, 2, 4, 6, 8, 10, 12, 14, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 1, 3, 5, 7, 9, 11, 13, 15, 17]
  | _ => []

theorem ws7Word79Weak :
    WeakValidRates (fun i => (ws7WordP79 i : ℝ) / (ws7WordQ79 i : ℝ))
      (periodic ws7Word79.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word79)) := by
  apply weakPeriodic_of_paths ws7Word79 (by decide) ws7WordP79 ws7WordQ79
    (by intro i; fin_cases i <;> norm_num [ws7WordQ79]) ws7WordZ79
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word80 : List (Fin 7) := [1, 4, 5, 0, 3, 2, 6, 1, 0, 4, 5, 2, 3, 0, 1, 6, 4, 0, 5, 2, 3, 1, 0, 6, 4, 2, 5, 0, 1, 3, 6, 2, 0, 4, 5, 1, 3, 0, 2, 6, 4, 0, 1, 5, 3, 2, 0, 6]

def ws7WordP80 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 7
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ80 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 24
  | 1 => 48
  | 2 => 7
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | _ => 1

def ws7WordZ80 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 0, 5, 10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 0, 5, 10, 15, 20, 1, 6]
  | 1 => [41, 0, 7, 14, 21, 28, 35, 42, 1, 8, 15, 22, 29, 36, 43, 2, 9, 16, 23, 30, 37, 44, 3, 10, 17, 24, 31, 38, 45, 4, 11, 18, 25, 32, 39, 46, 5, 12, 19, 26, 33, 40, 47, 6, 13, 20, 27, 34, 41]
  | 2 => [2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2]
  | 3 => [3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3]
  | 4 => [7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]
  | 5 => [5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5]
  | 6 => [1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1]
  | _ => []

theorem ws7Word80Weak :
    WeakValidRates (fun i => (ws7WordP80 i : ℝ) / (ws7WordQ80 i : ℝ))
      (periodic ws7Word80.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word80)) := by
  apply weakPeriodic_of_paths ws7Word80 (by decide) ws7WordP80 ws7WordQ80
    (by intro i; fin_cases i <;> norm_num [ws7WordQ80]) ws7WordZ80
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word81 : List (Fin 7) := [2, 5, 1, 4, 0, 3, 1, 6, 2, 0, 4, 5, 1, 0, 3, 2, 6, 1, 4, 0, 5, 2, 3, 1, 0, 4, 6, 0, 1, 2, 5, 3, 0, 1, 4, 2, 6, 0, 3, 1, 5, 2, 4, 0, 1, 6, 3, 0]

def ws7WordP81 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 8
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

def ws7WordQ81 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 43
  | 2 => 7
  | 3 => 25
  | 4 => 25
  | 5 => 48
  | 6 => 48
  | _ => 1

def ws7WordZ81 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0]
  | 1 => [27, 35, 43, 8, 16, 24, 32, 0, 8, 16, 24, 32, 40, 5, 13, 21, 29, 37, 2, 10, 18, 26, 34, 42, 7, 15, 23, 31, 39, 4, 12, 20, 28, 36, 1, 9, 17, 25, 33, 41, 6, 14, 22, 30, 38, 3, 11, 19, 27]
  | 2 => [6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6]
  | 3 => [3, 6, 9, 12, 15, 18, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 0, 3]
  | 4 => [16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16]
  | 5 => [39, 44, 1, 6, 11, 16, 21, 26, 31, 36, 41, 46, 3, 8, 13, 18, 23, 28, 33, 38, 43, 0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 2, 7, 12, 17, 22, 27, 32, 37, 42, 47, 4, 9, 14, 19, 24, 29, 34, 39]
  | 6 => [11, 16, 21, 26, 31, 36, 41, 46, 3, 8, 13, 18, 23, 28, 33, 38, 43, 0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 2, 7, 12, 17, 22, 27, 32, 37, 42, 47, 4, 9, 14, 19, 24, 29, 34, 39, 44, 1, 6, 11]
  | _ => []

theorem ws7Word81Weak :
    WeakValidRates (fun i => (ws7WordP81 i : ℝ) / (ws7WordQ81 i : ℝ))
      (periodic ws7Word81.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word81)) := by
  apply weakPeriodic_of_paths ws7Word81 (by decide) ws7WordP81 ws7WordQ81
    (by intro i; fin_cases i <;> norm_num [ws7WordQ81]) ws7WordZ81
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word82 : List (Fin 7) := [3, 5, 2, 1, 0, 4, 6, 2, 3, 0, 1, 5, 2, 0, 4, 1, 6, 3, 0, 2, 5, 1, 4, 0, 3, 2, 6, 1, 0, 4, 5, 2, 3, 0, 1, 6, 2, 0, 4, 1, 5, 3, 0, 2, 6, 1, 4, 0]

def ws7WordP82 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 5
  | 6 => 3
  | _ => 0

def ws7WordQ82 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 24
  | 1 => 6
  | 2 => 13
  | 3 => 8
  | 4 => 8
  | 5 => 48
  | 6 => 29
  | _ => 1

def ws7WordZ82 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 0, 5, 10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 0, 5, 10, 15, 20, 1, 6, 11, 16, 21, 2]
  | 1 => [2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2]
  | 2 => [9, 11, 13, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9]
  | 3 => [7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7]
  | 4 => [2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2]
  | 5 => [39, 44, 1, 6, 11, 16, 21, 26, 31, 36, 41, 46, 3, 8, 13, 18, 23, 28, 33, 38, 43, 0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 2, 7, 12, 17, 22, 27, 32, 37, 42, 47, 4, 9, 14, 19, 24, 29, 34, 39]
  | 6 => [9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 2, 5, 8, 11, 14, 17, 20, 23, 26, 29, 3, 6, 9, 12, 15, 18, 21, 24, 27, 1, 4, 7, 10, 13, 16, 19, 22, 25, 0, 3, 6, 9]
  | _ => []

theorem ws7Word82Weak :
    WeakValidRates (fun i => (ws7WordP82 i : ℝ) / (ws7WordQ82 i : ℝ))
      (periodic ws7Word82.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word82)) := by
  apply weakPeriodic_of_paths ws7Word82 (by decide) ws7WordP82 ws7WordQ82
    (by intro i; fin_cases i <;> norm_num [ws7WordQ82]) ws7WordZ82
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word83 : List (Fin 7) := [4, 0, 3, 2, 5, 0, 1, 6, 4, 3, 0, 2, 5, 1, 0, 6, 4, 3, 2, 0, 1, 5, 6, 0, 4, 3, 2, 1, 0, 5, 6, 0, 4, 3, 1, 2, 0, 5, 6, 4, 0, 1, 3, 2, 0, 5, 6, 1]

def ws7WordP83 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 7
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ83 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 31
  | 1 => 48
  | 2 => 8
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | _ => 1

def ws7WordZ83 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [21, 28, 4, 11, 18, 25, 1, 8, 15, 22, 29, 5, 12, 19, 26, 2, 9, 16, 23, 30, 6, 13, 20, 27, 3, 10, 17, 24, 31, 7, 14, 21, 0, 7, 14, 21, 28, 4, 11, 18, 25, 1, 8, 15, 22, 0, 7, 14, 21]
  | 1 => [0, 7, 14, 21, 28, 35, 42, 1, 8, 15, 22, 29, 36, 43, 2, 9, 16, 23, 30, 37, 44, 3, 10, 17, 24, 31, 38, 45, 4, 11, 18, 25, 32, 39, 46, 5, 12, 19, 26, 33, 40, 47, 6, 13, 20, 27, 34, 41, 0]
  | 2 => [5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5]
  | 3 => [6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6]
  | 4 => [8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8]
  | 5 => [3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3]
  | 6 => [1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1]
  | _ => []

theorem ws7Word83Weak :
    WeakValidRates (fun i => (ws7WordP83 i : ℝ) / (ws7WordQ83 i : ℝ))
      (periodic ws7Word83.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word83)) := by
  apply weakPeriodic_of_paths ws7Word83 (by decide) ws7WordP83 ws7WordQ83
    (by intro i; fin_cases i <;> norm_num [ws7WordQ83]) ws7WordZ83
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word84 : List (Fin 7) := [6, 3, 1, 0, 2, 5, 4, 1, 0, 3, 6, 2, 1, 0, 5, 4, 3, 1, 0, 6, 2, 1, 0, 4, 5, 3, 1, 0, 2, 6, 4, 1, 0, 3, 5, 2, 1, 0, 4, 6, 3, 1, 0, 5, 2, 1, 0, 4]

def ws7WordP84 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 5
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 5
  | 6 => 5
  | _ => 0

def ws7WordQ84 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 24
  | 1 => 24
  | 2 => 8
  | 3 => 8
  | 4 => 8
  | 5 => 48
  | 6 => 48
  | _ => 1

def ws7WordZ84 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [5, 10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 0, 5, 10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 0, 5]
  | 1 => [10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 0, 5, 10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 0, 5, 10]
  | 2 => [4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4]
  | 3 => [7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]
  | 4 => [1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1]
  | 5 => [21, 26, 31, 36, 41, 46, 3, 8, 13, 18, 23, 28, 33, 38, 43, 0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 2, 7, 12, 17, 22, 27, 32, 37, 42, 47, 4, 9, 14, 19, 24, 29, 34, 39, 44, 1, 6, 11, 16, 21]
  | 6 => [44, 1, 6, 11, 16, 21, 26, 31, 36, 41, 46, 3, 8, 13, 18, 23, 28, 33, 38, 43, 0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 2, 7, 12, 17, 22, 27, 32, 37, 42, 47, 4, 9, 14, 19, 24, 29, 34, 39, 44]
  | _ => []

theorem ws7Word84Weak :
    WeakValidRates (fun i => (ws7WordP84 i : ℝ) / (ws7WordQ84 i : ℝ))
      (periodic ws7Word84.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word84)) := by
  apply weakPeriodic_of_paths ws7Word84 (by decide) ws7WordP84 ws7WordQ84
    (by intro i; fin_cases i <;> norm_num [ws7WordQ84]) ws7WordZ84
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word85 : List (Fin 7) := [0, 1, 5, 6, 0, 4, 2, 1, 3, 0, 5, 6, 2, 0, 4, 1, 3, 0, 5, 6, 2, 1, 0, 4, 3, 5, 0, 2, 6, 1, 4, 0, 3, 5, 2, 0, 1, 6, 4, 2, 0, 3, 5, 1, 0, 6, 4, 2, 3]

def ws7WordP85 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 11
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

def ws7WordQ85 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 49
  | 1 => 7
  | 2 => 15
  | 3 => 41
  | 4 => 17
  | 5 => 17
  | 6 => 17
  | _ => 1

def ws7WordZ85 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [47, 9, 20, 31, 42, 4, 15, 26, 37, 48, 10, 21, 32, 43, 5, 16, 27, 38, 0, 11, 22, 33, 44, 6, 17, 28, 39, 1, 12, 23, 34, 45, 7, 18, 29, 40, 2, 13, 24, 35, 46, 8, 19, 30, 41, 3, 14, 25, 36, 47]
  | 1 => [6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6]
  | 2 => [3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3]
  | 3 => [0, 5, 10, 15, 20, 25, 30, 35, 40, 4, 9, 14, 19, 24, 29, 34, 39, 3, 8, 13, 18, 23, 28, 33, 38, 2, 7, 12, 17, 22, 27, 32, 37, 1, 6, 11, 16, 21, 26, 31, 36, 41, 5, 10, 15, 20, 25, 30, 35, 0]
  | 4 => [4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4]
  | 5 => [13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13]
  | 6 => [7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7]
  | _ => []

theorem ws7Word85Weak :
    WeakValidRates (fun i => (ws7WordP85 i : ℝ) / (ws7WordQ85 i : ℝ))
      (periodic ws7Word85.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word85)) := by
  apply weakPeriodic_of_paths ws7Word85 (by decide) ws7WordP85 ws7WordQ85
    (by intro i; fin_cases i <;> norm_num [ws7WordQ85]) ws7WordZ85
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word86 : List (Fin 7) := [4, 2, 0, 5, 1, 3, 6, 0, 4, 1, 2, 5, 0, 3, 1, 6, 4, 0, 2, 5, 1, 3, 0, 6, 4, 1, 2, 0, 5, 3, 1, 6, 0, 4, 2, 5, 1, 0, 3, 6, 4, 0, 1, 2, 5, 3, 0, 1, 6]

def ws7WordP86 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 10
  | 1 => 2
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | 5 => 5
  | 6 => 5
  | _ => 0

def ws7WordQ86 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 49
  | 1 => 11
  | 2 => 41
  | 3 => 41
  | 4 => 41
  | 5 => 41
  | 6 => 41
  | _ => 1

def ws7WordZ86 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [21, 31, 41, 2, 12, 22, 32, 42, 3, 13, 23, 33, 43, 4, 14, 24, 34, 44, 5, 15, 25, 35, 45, 6, 16, 26, 36, 46, 7, 17, 27, 37, 47, 8, 18, 28, 38, 48, 9, 19, 29, 39, 0, 10, 20, 30, 40, 1, 11, 21]
  | 1 => [3, 5, 7, 9, 11, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11, 2, 4, 6, 8, 10, 1, 3]
  | 2 => [30, 35, 0, 5, 10, 15, 20, 25, 30, 35, 40, 4, 9, 14, 19, 24, 29, 34, 39, 3, 8, 13, 18, 23, 28, 33, 38, 2, 7, 12, 17, 22, 27, 32, 37, 1, 6, 11, 16, 21, 26, 31, 36, 41, 5, 10, 15, 20, 25, 30]
  | 3 => [15, 20, 25, 30, 35, 40, 4, 9, 14, 19, 24, 29, 34, 39, 3, 8, 13, 18, 23, 28, 33, 38, 2, 7, 12, 17, 22, 27, 32, 37, 1, 6, 11, 16, 21, 26, 31, 36, 41, 5, 10, 15, 20, 25, 30, 35, 0, 5, 10, 15]
  | 4 => [40, 4, 9, 14, 19, 24, 29, 34, 39, 3, 8, 13, 18, 23, 28, 33, 38, 2, 7, 12, 17, 22, 27, 32, 37, 1, 6, 11, 16, 21, 26, 31, 36, 41, 5, 10, 15, 20, 25, 30, 35, 0, 5, 10, 15, 20, 25, 30, 35, 40]
  | 5 => [24, 29, 34, 39, 3, 8, 13, 18, 23, 28, 33, 38, 2, 7, 12, 17, 22, 27, 32, 37, 1, 6, 11, 16, 21, 26, 31, 36, 41, 5, 10, 15, 20, 25, 30, 35, 0, 5, 10, 15, 20, 25, 30, 35, 40, 4, 9, 14, 19, 24]
  | 6 => [5, 10, 15, 20, 25, 30, 35, 0, 5, 10, 15, 20, 25, 30, 35, 40, 4, 9, 14, 19, 24, 29, 34, 39, 3, 8, 13, 18, 23, 28, 33, 38, 2, 7, 12, 17, 22, 27, 32, 37, 1, 6, 11, 16, 21, 26, 31, 36, 41, 5]
  | _ => []

theorem ws7Word86Weak :
    WeakValidRates (fun i => (ws7WordP86 i : ℝ) / (ws7WordQ86 i : ℝ))
      (periodic ws7Word86.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word86)) := by
  apply weakPeriodic_of_paths ws7Word86 (by decide) ws7WordP86 ws7WordQ86
    (by intro i; fin_cases i <;> norm_num [ws7WordQ86]) ws7WordZ86
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word87 : List (Fin 7) := [0, 3, 1, 6, 2, 0, 5, 4, 1, 3, 0, 2, 6, 1, 0, 5, 4, 3, 0, 2, 1, 6, 5, 0, 4, 3, 1, 2, 0, 6, 5, 0, 1, 4, 3, 2, 0, 6, 5, 1, 4, 0, 3, 2, 6, 1, 0, 5, 4, 2]

def ws7WordP87 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 3
  | 1 => 3
  | 2 => 4
  | 3 => 3
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | _ => 0

def ws7WordQ87 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 14
  | 1 => 19
  | 2 => 31
  | 3 => 25
  | 4 => 17
  | 5 => 26
  | 6 => 26
  | _ => 1

def ws7WordZ87 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 12, 1, 4, 7, 10, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 0, 3, 6, 9, 12, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14, 3, 6, 9, 12]
  | 1 => [13, 16, 19, 3, 6, 9, 12, 15, 18, 2, 5, 8, 11, 14, 0, 3, 6, 9, 12, 15, 18, 2, 5, 8, 11, 14, 17, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12, 15, 18, 2, 5, 8, 11, 14, 17, 1, 4, 7, 10, 13]
  | 2 => [0, 4, 8, 12, 16, 0, 4, 8, 12, 16, 20, 24, 0, 4, 8, 12, 16, 20, 24, 28, 1, 5, 9, 13, 17, 21, 25, 29, 2, 6, 10, 14, 18, 22, 26, 30, 3, 7, 11, 15, 19, 23, 27, 31, 4, 8, 12, 16, 20, 24, 0]
  | 3 => [22, 25, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22]
  | 4 => [2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14, 0, 2]
  | 5 => [7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 26, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7]
  | 6 => [15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 26, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 0, 3, 6, 9, 12, 15, 18, 0, 3, 6, 9, 12, 15]
  | _ => []

theorem ws7Word87Weak :
    WeakValidRates (fun i => (ws7WordP87 i : ℝ) / (ws7WordQ87 i : ℝ))
      (periodic ws7Word87.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word87)) := by
  apply weakPeriodic_of_paths ws7Word87 (by decide) ws7WordP87 ws7WordQ87
    (by intro i; fin_cases i <;> norm_num [ws7WordQ87]) ws7WordZ87
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word88 : List (Fin 7) := [3, 6, 2, 0, 1, 4, 5, 3, 0, 2, 1, 6, 3, 0, 4, 2, 5, 1, 0, 3, 6, 2, 4, 1, 0, 3, 5, 2, 0, 1, 6, 4, 3, 0, 2, 1, 5, 3, 0, 4, 2, 6, 1, 0, 3, 5, 2, 4, 1, 0]

def ws7WordP88 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 1
  | 1 => 4
  | 2 => 4
  | 3 => 3
  | 4 => 3
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ88 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 25
  | 2 => 25
  | 3 => 19
  | 4 => 25
  | 5 => 10
  | 6 => 10
  | _ => 1

def ws7WordZ88 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1]
  | 1 => [6, 10, 14, 18, 22, 1, 5, 9, 13, 17, 21, 0, 4, 8, 12, 16, 20, 24, 3, 7, 11, 15, 19, 23, 2, 6, 10, 14, 18, 22, 1, 5, 9, 13, 17, 21, 0, 4, 8, 12, 16, 20, 24, 3, 7, 11, 15, 19, 23, 2, 6]
  | 2 => [13, 17, 21, 0, 4, 8, 12, 16, 20, 24, 3, 7, 11, 15, 19, 23, 2, 6, 10, 14, 18, 22, 1, 5, 9, 13, 17, 21, 0, 4, 8, 12, 16, 20, 24, 3, 7, 11, 15, 19, 23, 2, 6, 10, 14, 18, 22, 1, 5, 9, 13]
  | 3 => [17, 1, 4, 7, 10, 13, 16, 19, 3, 6, 9, 12, 15, 0, 3, 6, 9, 12, 15, 18, 2, 5, 8, 11, 14, 17, 1, 4, 7, 10, 13, 16, 19, 3, 6, 9, 12, 15, 0, 3, 6, 9, 12, 15, 18, 2, 5, 8, 11, 14, 17]
  | 4 => [7, 10, 13, 16, 19, 22, 0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 1, 4, 7]
  | 5 => [4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4]
  | 6 => [9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  | _ => []

theorem ws7Word88Weak :
    WeakValidRates (fun i => (ws7WordP88 i : ℝ) / (ws7WordQ88 i : ℝ))
      (periodic ws7Word88.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word88)) := by
  apply weakPeriodic_of_paths ws7Word88 (by decide) ws7WordP88 ws7WordQ88
    (by intro i; fin_cases i <;> norm_num [ws7WordQ88]) ws7WordZ88
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word89 : List (Fin 7) := [1, 0, 6, 2, 4, 0, 1, 5, 3, 0, 6, 2, 1, 4, 0, 5, 3, 1, 2, 0, 6, 4, 5, 1, 0, 3, 2, 6, 0, 1, 4, 5, 2, 0, 3, 1, 6, 4, 0, 2, 5, 1, 3, 0, 6, 1, 4, 2, 0, 5, 3]

def ws7WordP89 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 4
  | 1 => 4
  | 2 => 5
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | 6 => 1
  | _ => 0

def ws7WordQ89 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 19
  | 1 => 23
  | 2 => 37
  | 3 => 17
  | 4 => 26
  | 5 => 35
  | 6 => 9
  | _ => 1

def ws7WordZ89 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [12, 16, 1, 5, 9, 13, 0, 4, 8, 12, 0, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 18, 3, 7, 11, 15, 0, 4, 8, 12, 16, 1, 5, 9, 13, 17, 2, 6, 10, 14, 18, 3, 7, 11, 15, 19, 4, 8, 12]
  | 1 => [20, 1, 5, 9, 13, 17, 21, 2, 6, 10, 14, 18, 22, 3, 7, 11, 15, 19, 0, 4, 8, 12, 16, 20, 1, 5, 9, 13, 17, 21, 2, 6, 10, 14, 18, 22, 3, 7, 11, 15, 19, 23, 4, 8, 12, 16, 0, 4, 8, 12, 16, 20]
  | 2 => [18, 23, 28, 33, 1, 6, 11, 16, 21, 26, 31, 36, 4, 9, 14, 19, 24, 29, 34, 2, 7, 12, 17, 22, 27, 32, 37, 5, 10, 15, 20, 25, 30, 0, 5, 10, 15, 20, 25, 30, 0, 5, 10, 15, 20, 25, 30, 35, 3, 8, 13, 18]
  | 3 => [0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0]
  | 4 => [13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 26, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13]
  | 5 => [7, 11, 15, 19, 23, 27, 31, 35, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 29, 33, 2, 6, 10, 14, 18, 22, 26, 30, 34, 3, 7]
  | 6 => [6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6]
  | _ => []

theorem ws7Word89Weak :
    WeakValidRates (fun i => (ws7WordP89 i : ℝ) / (ws7WordQ89 i : ℝ))
      (periodic ws7Word89.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word89)) := by
  apply weakPeriodic_of_paths ws7Word89 (by decide) ws7WordP89 ws7WordQ89
    (by intro i; fin_cases i <;> norm_num [ws7WordQ89]) ws7WordZ89
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word90 : List (Fin 7) := [1, 4, 3, 0, 2, 6, 1, 5, 0, 4, 2, 3, 1, 0, 6, 5, 2, 0, 4, 1, 3, 0, 2, 6, 5, 1, 0, 4, 3, 2, 6, 0, 1, 5, 4, 2, 0, 3, 1, 6, 5, 0, 2, 4, 1, 3, 0, 6, 2, 5, 0]

def ws7WordP90 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 5
  | 1 => 8
  | 2 => 5
  | 3 => 2
  | 4 => 5
  | 5 => 5
  | 6 => 3
  | _ => 0

def ws7WordQ90 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 24
  | 1 => 51
  | 2 => 32
  | 3 => 17
  | 4 => 43
  | 5 => 43
  | 6 => 26
  | _ => 1

def ws7WordZ90 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 6, 11, 16, 0, 5, 10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 0, 5, 10, 15, 0, 5, 10, 15, 20, 1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 24, 5, 10, 15, 20, 1]
  | 1 => [49, 6, 14, 22, 30, 38, 46, 3, 11, 19, 27, 35, 43, 0, 8, 16, 24, 32, 40, 48, 5, 13, 21, 29, 37, 45, 2, 10, 18, 26, 34, 42, 50, 7, 15, 23, 31, 39, 47, 4, 12, 20, 28, 36, 44, 1, 9, 17, 25, 33, 41, 49]
  | 2 => [12, 17, 22, 27, 32, 5, 10, 15, 20, 25, 30, 3, 8, 13, 18, 23, 28, 1, 6, 11, 16, 21, 26, 0, 5, 10, 15, 20, 25, 30, 3, 8, 13, 18, 23, 28, 1, 6, 11, 16, 21, 26, 31, 4, 9, 14, 19, 24, 29, 2, 7, 12]
  | 3 => [11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11]
  | 4 => [37, 42, 4, 9, 14, 19, 24, 29, 34, 39, 1, 6, 11, 16, 21, 26, 31, 36, 41, 3, 8, 13, 18, 23, 28, 33, 38, 43, 5, 10, 15, 20, 25, 30, 35, 0, 5, 10, 15, 20, 25, 30, 35, 40, 2, 7, 12, 17, 22, 27, 32, 37]
  | 5 => [7, 12, 17, 22, 27, 32, 37, 42, 4, 9, 14, 19, 24, 29, 34, 39, 1, 6, 11, 16, 21, 26, 31, 36, 41, 3, 8, 13, 18, 23, 28, 33, 38, 43, 5, 10, 15, 20, 25, 30, 35, 0, 5, 10, 15, 20, 25, 30, 35, 40, 2, 7]
  | 6 => [9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 26, 3, 6, 9, 12, 15, 18, 21, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 0, 3, 6, 9]
  | _ => []

theorem ws7Word90Weak :
    WeakValidRates (fun i => (ws7WordP90 i : ℝ) / (ws7WordQ90 i : ℝ))
      (periodic ws7Word90.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word90)) := by
  apply weakPeriodic_of_paths ws7Word90 (by decide) ws7WordP90 ws7WordQ90
    (by intro i; fin_cases i <;> norm_num [ws7WordQ90]) ws7WordZ90
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word91 : List (Fin 7) := [2, 3, 1, 0, 6, 5, 2, 0, 4, 1, 3, 0, 6, 2, 5, 1, 0, 4, 3, 0, 2, 1, 6, 5, 0, 4, 3, 1, 2, 0, 6, 5, 0, 4, 1, 3, 2, 0, 6, 5, 1, 0, 4, 2, 3, 0, 1, 6, 5, 0, 4]

def ws7WordP91 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 1
  | _ => 0

def ws7WordQ91 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 13
  | 2 => 15
  | 3 => 17
  | 4 => 17
  | 5 => 17
  | 6 => 9
  | _ => 1

def ws7WordZ91 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 0, 2, 4, 6, 8, 1, 3, 5, 0, 2, 4, 6, 8, 1, 3, 5, 7, 9, 2, 4, 6, 0, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 0, 2, 4, 6, 0, 2]
  | 1 => [8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 0, 2, 4, 6, 8]
  | 2 => [15, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15]
  | 3 => [14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14]
  | 4 => [0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0]
  | 5 => [5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 17, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15, 0, 2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5]
  | 6 => [3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3]
  | _ => []

theorem ws7Word91Weak :
    WeakValidRates (fun i => (ws7WordP91 i : ℝ) / (ws7WordQ91 i : ℝ))
      (periodic ws7Word91.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word91)) := by
  apply weakPeriodic_of_paths ws7Word91 (by decide) ws7WordP91 ws7WordQ91
    (by intro i; fin_cases i <;> norm_num [ws7WordQ91]) ws7WordZ91
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word92 : List (Fin 7) := [1, 2, 0, 4, 5, 3, 0, 1, 6, 2, 0, 4, 3, 5, 1, 0, 2, 6, 0, 3, 4, 1, 5, 0, 2, 6, 1, 3, 0, 4, 5, 2, 0, 1, 6, 3, 0, 4, 2, 5, 1, 0, 3, 6, 0, 2, 4, 1, 5, 0, 3, 6]

def ws7WordP92 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 2
  | 1 => 3
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

def ws7WordQ92 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 20
  | 2 => 15
  | 3 => 15
  | 4 => 26
  | 5 => 26
  | 6 => 26
  | _ => 1

def ws7WordZ92 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [5, 7, 9, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 0, 2, 4, 6, 8, 1, 3, 5, 7, 9, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 0, 2, 4, 6, 8, 1, 3, 5]
  | 1 => [15, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 20, 3, 6, 9, 12, 15, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 20, 3, 6, 9, 12, 15]
  | 2 => [12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12]
  | 3 => [4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4]
  | 4 => [16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16]
  | 5 => [11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11]
  | 6 => [0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 0]
  | _ => []

theorem ws7Word92Weak :
    WeakValidRates (fun i => (ws7WordP92 i : ℝ) / (ws7WordQ92 i : ℝ))
      (periodic ws7Word92.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word92)) := by
  apply weakPeriodic_of_paths ws7Word92 (by decide) ws7WordP92 ws7WordQ92
    (by intro i; fin_cases i <;> norm_num [ws7WordQ92]) ws7WordZ92
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word93 : List (Fin 7) := [2, 0, 3, 5, 1, 6, 0, 2, 4, 1, 3, 0, 5, 2, 6, 0, 1, 4, 3, 0, 2, 5, 1, 6, 0, 3, 4, 2, 0, 1, 5, 6, 3, 0, 2, 4, 1, 5, 0, 3, 2, 6, 1, 0, 4, 5, 3, 2, 0, 1, 6, 4]

def ws7WordP93 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 5
  | 2 => 3
  | 3 => 3
  | 4 => 5
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ93 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 34
  | 1 => 33
  | 2 => 20
  | 3 => 23
  | 4 => 44
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ93 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [25, 32, 5, 12, 19, 26, 33, 6, 13, 20, 27, 34, 7, 14, 21, 28, 1, 8, 15, 22, 0, 7, 14, 21, 28, 1, 8, 15, 22, 0, 7, 14, 21, 28, 1, 8, 15, 22, 29, 2, 9, 16, 23, 30, 3, 10, 17, 24, 31, 4, 11, 18, 25]
  | 1 => [13, 18, 23, 28, 33, 5, 10, 15, 20, 25, 0, 5, 10, 15, 20, 25, 30, 2, 7, 12, 17, 22, 27, 0, 5, 10, 15, 20, 25, 30, 2, 7, 12, 17, 22, 27, 32, 4, 9, 14, 19, 24, 29, 1, 6, 11, 16, 21, 26, 31, 3, 8, 13]
  | 2 => [14, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 20, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14]
  | 3 => [15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 22, 2, 5, 8, 11, 14, 17, 20, 23, 3, 6, 9, 12, 15, 18, 21, 1, 4, 7, 10, 13, 16, 19, 0, 3, 6, 9, 12, 15, 18, 0, 3, 6, 9, 12, 15, 18, 0, 3, 6, 9, 12, 15]
  | 4 => [0, 5, 10, 15, 20, 25, 30, 35, 40, 1, 6, 11, 16, 21, 26, 31, 36, 41, 2, 7, 12, 17, 22, 27, 32, 37, 42, 3, 8, 13, 18, 23, 28, 33, 38, 43, 4, 9, 14, 19, 24, 29, 34, 39, 44, 5, 10, 15, 20, 25, 30, 35, 0]
  | 5 => [6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6]
  | 6 => [2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2]
  | _ => []

theorem ws7Word93Weak :
    WeakValidRates (fun i => (ws7WordP93 i : ℝ) / (ws7WordQ93 i : ℝ))
      (periodic ws7Word93.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word93)) := by
  apply weakPeriodic_of_paths ws7Word93 (by decide) ws7WordP93 ws7WordQ93
    (by intro i; fin_cases i <;> norm_num [ws7WordQ93]) ws7WordZ93
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word94 : List (Fin 7) := [2, 0, 6, 4, 3, 0, 1, 5, 2, 0, 6, 3, 4, 1, 0, 2, 5, 0, 3, 1, 6, 4, 0, 2, 5, 1, 3, 0, 6, 4, 2, 0, 1, 5, 3, 0, 6, 2, 4, 1, 0, 3, 5, 0, 2, 1, 6, 4, 0, 3, 5, 1]

def ws7WordP94 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 3
  | 6 => 1
  | _ => 0

def ws7WordQ94 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 9
  | 1 => 13
  | 2 => 15
  | 3 => 15
  | 4 => 26
  | 5 => 26
  | 6 => 9
  | _ => 1

def ws7WordZ94 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [7, 9, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 0, 2, 4, 6, 8, 1, 3, 5, 7, 9, 2, 4, 6, 8, 1, 3, 5, 7, 0, 2, 4, 6, 8, 1, 3, 5, 0, 2, 4, 6, 8, 1, 3, 5, 7]
  | 1 => [0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 13, 2, 4, 6, 8, 10, 12, 1, 3, 5, 7, 9, 11, 0]
  | 2 => [14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14]
  | 3 => [6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6]
  | 4 => [14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14]
  | 5 => [3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 0, 3]
  | 6 => [6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6]
  | _ => []

theorem ws7Word94Weak :
    WeakValidRates (fun i => (ws7WordP94 i : ℝ) / (ws7WordQ94 i : ℝ))
      (periodic ws7Word94.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word94)) := by
  apply weakPeriodic_of_paths ws7Word94 (by decide) ws7WordP94 ws7WordQ94
    (by intro i; fin_cases i <;> norm_num [ws7WordQ94]) ws7WordZ94
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word95 : List (Fin 7) := [6, 3, 0, 2, 5, 1, 4, 0, 3, 6, 2, 1, 0, 5, 3, 4, 0, 1, 2, 6, 0, 5, 3, 1, 4, 0, 2, 6, 5, 1, 0, 3, 2, 4, 0, 1, 6, 5, 3, 0, 2, 1, 4, 6, 0, 3, 5, 1, 2, 0, 4, 1]

def ws7WordP95 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 6
  | 1 => 8
  | 2 => 2
  | 3 => 1
  | 4 => 4
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ95 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 29
  | 1 => 47
  | 2 => 15
  | 3 => 8
  | 4 => 35
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ95 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [15, 21, 27, 4, 10, 16, 22, 28, 5, 11, 17, 23, 29, 6, 12, 18, 24, 1, 7, 13, 19, 0, 6, 12, 18, 24, 1, 7, 13, 19, 25, 2, 8, 14, 20, 0, 6, 12, 18, 24, 1, 7, 13, 19, 25, 2, 8, 14, 20, 26, 3, 9, 15]
  | 1 => [0, 8, 16, 24, 32, 40, 1, 9, 17, 25, 33, 41, 2, 10, 18, 26, 34, 42, 3, 11, 19, 27, 35, 43, 4, 12, 20, 28, 36, 44, 5, 13, 21, 29, 37, 45, 6, 14, 22, 30, 38, 46, 7, 15, 23, 31, 39, 47, 8, 16, 24, 32, 0]
  | 2 => [8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8]
  | 3 => [6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6]
  | 4 => [5, 9, 13, 17, 21, 25, 29, 0, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5, 9, 13, 17, 21, 25, 29, 33, 2, 6, 10, 14, 18, 22, 26, 30, 34, 3, 7, 11, 15, 19, 23, 27, 31, 35, 4, 8, 12, 16, 20, 24, 28, 32, 1, 5]
  | 5 => [5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5]
  | 6 => [8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8]
  | _ => []

theorem ws7Word95Weak :
    WeakValidRates (fun i => (ws7WordP95 i : ℝ) / (ws7WordQ95 i : ℝ))
      (periodic ws7Word95.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word95)) := by
  apply weakPeriodic_of_paths ws7Word95 (by decide) ws7WordP95 ws7WordQ95
    (by intro i; fin_cases i <;> norm_num [ws7WordQ95]) ws7WordZ95
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word96 : List (Fin 7) := [0, 2, 3, 4, 1, 0, 5, 2, 6, 0, 1, 3, 4, 0, 2, 5, 1, 6, 0, 3, 4, 2, 0, 1, 5, 3, 6, 0, 2, 4, 1, 0, 3, 5, 2, 6, 0, 1, 4, 3, 0, 2, 5, 1, 6, 0, 2, 4, 3, 0, 1, 5, 6]

def ws7WordP96 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 7
  | 1 => 3
  | 2 => 1
  | 3 => 1
  | 4 => 6
  | 5 => 6
  | 6 => 6
  | _ => 0

def ws7WordQ96 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 31
  | 1 => 20
  | 2 => 7
  | 3 => 8
  | 4 => 53
  | 5 => 53
  | 6 => 53
  | _ => 1

def ws7WordZ96 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [25, 1, 8, 15, 22, 29, 5, 12, 19, 26, 2, 9, 16, 23, 0, 7, 14, 21, 28, 4, 11, 18, 25, 1, 8, 15, 22, 29, 5, 12, 19, 26, 2, 9, 16, 23, 30, 6, 13, 20, 27, 3, 10, 17, 24, 31, 7, 14, 21, 28, 4, 11, 18, 25]
  | 1 => [8, 11, 14, 17, 20, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 0, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8, 11, 14, 17, 20, 3, 6, 9, 12, 15, 18, 1, 4, 7, 10, 13, 16, 19, 2, 5, 8]
  | 2 => [6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 6]
  | 3 => [5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5]
  | 4 => [33, 39, 45, 51, 4, 10, 16, 22, 28, 34, 40, 46, 52, 5, 11, 17, 23, 29, 35, 41, 47, 0, 6, 12, 18, 24, 30, 36, 42, 48, 1, 7, 13, 19, 25, 31, 37, 43, 49, 2, 8, 14, 20, 26, 32, 38, 44, 50, 3, 9, 15, 21, 27, 33]
  | 5 => [11, 17, 23, 29, 35, 41, 47, 0, 6, 12, 18, 24, 30, 36, 42, 48, 1, 7, 13, 19, 25, 31, 37, 43, 49, 2, 8, 14, 20, 26, 32, 38, 44, 50, 3, 9, 15, 21, 27, 33, 39, 45, 51, 4, 10, 16, 22, 28, 34, 40, 46, 52, 5, 11]
  | 6 => [0, 6, 12, 18, 24, 30, 36, 42, 48, 1, 7, 13, 19, 25, 31, 37, 43, 49, 2, 8, 14, 20, 26, 32, 38, 44, 50, 3, 9, 15, 21, 27, 33, 39, 45, 51, 4, 10, 16, 22, 28, 34, 40, 46, 52, 5, 11, 17, 23, 29, 35, 41, 47, 0]
  | _ => []

theorem ws7Word96Weak :
    WeakValidRates (fun i => (ws7WordP96 i : ℝ) / (ws7WordQ96 i : ℝ))
      (periodic ws7Word96.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word96)) := by
  apply weakPeriodic_of_paths ws7Word96 (by decide) ws7WordP96 ws7WordQ96
    (by intro i; fin_cases i <;> norm_num [ws7WordQ96]) ws7WordZ96
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word97 : List (Fin 7) := [1, 2, 0, 6, 4, 3, 1, 0, 5, 2, 6, 0, 1, 3, 4, 5, 0, 2, 1, 6, 3, 0, 4, 1, 2, 5, 0, 1, 3, 6, 4, 0, 2, 1, 5, 3, 0, 6, 1, 2, 4, 0, 5, 3, 1, 0, 6, 2, 4, 1, 0, 3, 5]

def ws7WordP97 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 6
  | 1 => 3
  | 2 => 7
  | 3 => 7
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ97 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 29
  | 1 => 17
  | 2 => 53
  | 3 => 53
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ97 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [14, 20, 26, 3, 9, 15, 21, 27, 4, 10, 16, 22, 0, 6, 12, 18, 24, 1, 7, 13, 19, 25, 2, 8, 14, 20, 26, 3, 9, 15, 21, 27, 4, 10, 16, 22, 28, 5, 11, 17, 23, 29, 6, 12, 18, 24, 1, 7, 13, 19, 25, 2, 8, 14]
  | 1 => [9, 0, 3, 6, 9, 12, 15, 1, 4, 7, 10, 13, 16, 2, 5, 8, 11, 14, 17, 3, 6, 9, 12, 15, 1, 4, 7, 10, 0, 3, 6, 9, 12, 15, 1, 4, 7, 10, 13, 0, 3, 6, 9, 12, 15, 1, 4, 7, 10, 13, 0, 3, 6, 9]
  | 2 => [39, 46, 0, 7, 14, 21, 28, 35, 42, 49, 3, 10, 17, 24, 31, 38, 45, 52, 6, 13, 20, 27, 34, 41, 48, 2, 9, 16, 23, 30, 37, 44, 51, 5, 12, 19, 26, 33, 40, 47, 1, 8, 15, 22, 29, 36, 43, 50, 4, 11, 18, 25, 32, 39]
  | 3 => [13, 20, 27, 34, 41, 48, 2, 9, 16, 23, 30, 37, 44, 51, 5, 12, 19, 26, 33, 40, 47, 1, 8, 15, 22, 29, 36, 43, 50, 4, 11, 18, 25, 32, 39, 46, 0, 7, 14, 21, 28, 35, 42, 49, 3, 10, 17, 24, 31, 38, 45, 52, 6, 13]
  | 4 => [4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4]
  | 5 => [1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1]
  | 6 => [6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6]
  | _ => []

theorem ws7Word97Weak :
    WeakValidRates (fun i => (ws7WordP97 i : ℝ) / (ws7WordQ97 i : ℝ))
      (periodic ws7Word97.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word97)) := by
  apply weakPeriodic_of_paths ws7Word97 (by decide) ws7WordP97 ws7WordQ97
    (by intro i; fin_cases i <;> norm_num [ws7WordQ97]) ws7WordZ97
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

def ws7Word98 : List (Fin 7) := [5, 2, 3, 1, 0, 4, 1, 6, 0, 2, 5, 3, 1, 0, 4, 1, 2, 6, 0, 5, 3, 1, 4, 0, 2, 1, 6, 5, 0, 3, 1, 4, 2, 0, 6, 1, 5, 3, 0, 2, 4, 1, 6, 0, 5, 1, 3, 2, 0, 4, 1, 6, 0]

def ws7WordP98 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 8
  | 1 => 1
  | 2 => 7
  | 3 => 6
  | 4 => 6
  | 5 => 1
  | 6 => 1
  | _ => 0

def ws7WordQ98 : Fin 7 → ℕ :=
  fun i => match i.val with
  | 0 => 39
  | 1 => 5
  | 2 => 53
  | 3 => 53
  | 4 => 53
  | 5 => 9
  | 6 => 9
  | _ => 1

def ws7WordZ98 : Fin 7 → List ℤ :=
  fun i => match i.val with
  | 0 => [1, 9, 17, 25, 33, 2, 10, 18, 26, 0, 8, 16, 24, 32, 1, 9, 17, 25, 33, 2, 10, 18, 26, 34, 3, 11, 19, 27, 35, 4, 12, 20, 28, 36, 5, 13, 21, 29, 37, 6, 14, 22, 30, 38, 7, 15, 23, 31, 39, 8, 16, 24, 32, 1]
  | 1 => [2, 3, 4, 5, 1, 2, 3, 0, 1, 2, 3, 4, 5, 1, 2, 3, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2]
  | 2 => [40, 47, 1, 8, 15, 22, 29, 36, 43, 50, 4, 11, 18, 25, 32, 39, 46, 0, 7, 14, 21, 28, 35, 42, 49, 3, 10, 17, 24, 31, 38, 45, 52, 6, 13, 20, 27, 34, 41, 48, 2, 9, 16, 23, 30, 37, 44, 51, 5, 12, 19, 26, 33, 40]
  | 3 => [37, 43, 49, 2, 8, 14, 20, 26, 32, 38, 44, 50, 3, 9, 15, 21, 27, 33, 39, 45, 51, 4, 10, 16, 22, 28, 34, 40, 46, 52, 5, 11, 17, 23, 29, 35, 41, 47, 0, 6, 12, 18, 24, 30, 36, 42, 48, 1, 7, 13, 19, 25, 31, 37]
  | 4 => [21, 27, 33, 39, 45, 51, 4, 10, 16, 22, 28, 34, 40, 46, 52, 5, 11, 17, 23, 29, 35, 41, 47, 0, 6, 12, 18, 24, 30, 36, 42, 48, 1, 7, 13, 19, 25, 31, 37, 43, 49, 2, 8, 14, 20, 26, 32, 38, 44, 50, 3, 9, 15, 21]
  | 5 => [8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8]
  | 6 => [1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1]
  | _ => []

theorem ws7Word98Weak :
    WeakValidRates (fun i => (ws7WordP98 i : ℝ) / (ws7WordQ98 i : ℝ))
      (periodic ws7Word98.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word98)) := by
  apply weakPeriodic_of_paths ws7Word98 (by decide) ws7WordP98 ws7WordQ98
    (by intro i; fin_cases i <;> norm_num [ws7WordQ98]) ws7WordZ98
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

end WeakSevenBandData
end RealPinwheel
