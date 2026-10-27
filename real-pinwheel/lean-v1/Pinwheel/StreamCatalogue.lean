import Pinwheel.Streams
import Pinwheel.StreamCycleLemmas
import Pinwheel.CatalogueData
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The thirteen literal mechanical-stream rows

The finite data in `CatalogueData` gives each row as two cyclic words.  This
file turns those words into the bilateral Beatty construction from
`Streams.lean`, and certifies the resulting residue classes and rate bounds.
-/

namespace RealPinwheel

open Set

def loadVec (a0 a1 a2 a3 a4 : ℚ) : Fin 5 → ℚ
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4

lemma sum_fin5 (f : Fin 5 → ℝ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_four]
  simp only [Fin.succ_zero_eq_one]
  have h2 : (Fin.succ (1 : Fin 4) : Fin 5) = 2 := by
    apply Fin.ext
    rfl
  have h3 : (Fin.succ (2 : Fin 4) : Fin 5) = 3 := by
    apply Fin.ext
    rfl
  have h4 : (Fin.succ (3 : Fin 4) : Fin 5) = 4 := by
    apply Fin.ext
    rfl
  rw [h2, h3, h4]
  ring

namespace Catalogue

/- The table is indexed by values rather than by `Fin` constructors.  This
   makes reduction of the finite certificates independent of proof fields in
   `Fin` values. -/
def streamLeftCycleTable : Nat → List (Fin 5)
  | 0 => [0]
  | 1 => [4]
  | 2 => [0]
  | 3 => [1]
  | 4 => [4]
  | 5 => [0]
  | 6 => [2]
  | 7 => [4]
  | 8 => [0, 1]
  | 9 => [1, 2]
  | 10 => [3, 4]
  | 11 => [0, 1]
  | 12 => [3, 4]
  | _ => []

def streamRightCycleTable : Nat → List (Fin 5)
  | 0 => [1, 2, 3, 4]
  | 1 => [0, 1, 2, 3]
  | 2 => [1, 2, 1, 3, 1, 2, 1, 4]
  | 3 => [0, 2, 0, 3, 0, 2, 0, 4]
  | 4 => [0, 1, 0, 2, 0, 1, 0, 3]
  | 5 => [1, 2, 3, 1, 2, 4]
  | 6 => [0, 1, 3, 0, 1, 4]
  | 7 => [0, 1, 2, 0, 1, 3]
  | 8 => [2, 3, 2, 4]
  | 9 => [0, 3, 0, 4]
  | 10 => [0, 1, 0, 2]
  | 11 => [2, 3, 4]
  | 12 => [0, 1, 2]
  | _ => []

def streamLeftCycle (j : Fin 13) : List (Fin 5) :=
  streamLeftCycleTable j.val

def streamRightCycle (j : Fin 13) : List (Fin 5) :=
  streamRightCycleTable j.val

def streamSide (j : Fin 13) (i : Fin 5) : Prop :=
  i ∈ streamLeftCycle j

def streamPeriodTable : Nat → Nat → ℤ
  | 0 => fun | 0 => 1 | 1 => 4 | 2 => 4 | 3 => 4 | 4 => 4 | _ => 1
  | 1 => fun | 0 => 4 | 1 => 4 | 2 => 4 | 3 => 4 | 4 => 1 | _ => 1
  | 2 => fun | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 8 | 4 => 8 | _ => 1
  | 3 => fun | 0 => 2 | 1 => 1 | 2 => 4 | 3 => 8 | 4 => 8 | _ => 1
  | 4 => fun | 0 => 2 | 1 => 4 | 2 => 8 | 3 => 8 | 4 => 1 | _ => 1
  | 5 => fun | 0 => 1 | 1 => 3 | 2 => 3 | 3 => 6 | 4 => 6 | _ => 1
  | 6 => fun | 0 => 3 | 1 => 3 | 2 => 1 | 3 => 6 | 4 => 6 | _ => 1
  | 7 => fun | 0 => 3 | 1 => 3 | 2 => 6 | 3 => 6 | 4 => 1 | _ => 1
  | 8 => fun | 0 => 2 | 1 => 2 | 2 => 2 | 3 => 4 | 4 => 4 | _ => 1
  | 9 => fun | 0 => 2 | 1 => 2 | 2 => 2 | 3 => 4 | 4 => 4 | _ => 1
  | 10 => fun | 0 => 2 | 1 => 4 | 2 => 4 | 3 => 2 | 4 => 2 | _ => 1
  | 11 => fun | 0 => 2 | 1 => 2 | 2 => 3 | 3 => 3 | 4 => 3 | _ => 1
  | 12 => fun | 0 => 3 | 1 => 3 | 2 => 3 | 3 => 2 | 4 => 2 | _ => 1
  | _ => fun _ => 1

def streamPeriod (j : Fin 13) (i : Fin 5) : ℤ :=
  streamPeriodTable j.val i.val

def streamResidueTable : Nat → Nat → ℤ
  | 0 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 0
  | 1 => fun | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | _ => 0
  | 2 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 7 | _ => 0
  | 3 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 7 | _ => 0
  | 4 => fun | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 7 | 4 => 0 | _ => 0
  | 5 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0
  | 6 => fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 5 | _ => 0
  | 7 => fun | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 0 | _ => 0
  | 8 => fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 3 | _ => 0
  | 9 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 3 | _ => 0
  | 10 => fun | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 1 | _ => 0
  | 11 => fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 2 | _ => 0
  | 12 => fun | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 1 | _ => 0
  | _ => fun _ => 0

def streamResidue (j : Fin 13) (i : Fin 5) : ℤ :=
  streamResidueTable j.val i.val

def streamParameter (j : Fin 13) (r : Fin 5 → ℝ) : ℝ :=
  match j.val with
  | 0 => r 0
  | 1 => r 4
  | 2 => r 0
  | 3 => r 1
  | 4 => r 4
  | 5 => r 0
  | 6 => r 2
  | 7 => r 4
  | 8 => 2 * r 0
  | 9 => 2 * r 1
  | 10 => 2 * r 3
  | 11 => 2 * r 0
  | 12 => 2 * r 3
  | _ => 0

lemma streamPeriod_pos (j : Fin 13) (i : Fin 5) : 0 < streamPeriod j i := by
  fin_cases j <;> fin_cases i <;> simp [streamPeriod, streamPeriodTable]

lemma streamResidue_nonneg (j : Fin 13) (i : Fin 5) : 0 ≤ streamResidue j i := by
  fin_cases j <;> fin_cases i <;> simp [streamResidue, streamResidueTable]

lemma streamResidue_lt_period (j : Fin 13) (i : Fin 5) :
    streamResidue j i < streamPeriod j i := by
  fin_cases j <;> fin_cases i <;>
    simp [streamPeriod, streamPeriodTable, streamResidue, streamResidueTable]

lemma streamLeft_periodic (j : Fin 13) (i : Fin 5) :
    streamSide j i → ListIndexPeriodic (streamLeftCycle j) i
      (streamPeriod j i) (streamResidue j i) := by
  intro hi
  fin_cases j <;> fin_cases i <;>
    simp [streamSide, streamLeftCycle, streamLeftCycleTable, streamPeriod,
      streamPeriodTable, streamResidue, streamResidueTable,
      ListIndexPeriodic] at hi ⊢
  all_goals
    intro k
    fin_cases k <;> norm_num <;> decide

lemma streamRight_periodic (j : Fin 13) (i : Fin 5) :
    ¬ streamSide j i → ListIndexPeriodic (streamRightCycle j) i
      (streamPeriod j i) (streamResidue j i) := by
  intro hi
  fin_cases j <;> fin_cases i <;>
    simp [streamSide, streamLeftCycle, streamLeftCycleTable,
      streamRightCycle, streamRightCycleTable, streamPeriod,
      streamPeriodTable, streamResidue, streamResidueTable,
      ListIndexPeriodic] at hi ⊢
  all_goals
    intro k
    fin_cases k <;> norm_num <;> decide

lemma stream_disjoint (j : Fin 13) :
    ∀ n k : ℤ, listCycle (streamLeftCycle j) n ≠
      listCycle (streamRightCycle j) k := by
  intro n k
  apply listCycle_ne_of_disjoint
  · fin_cases j <;> simp [streamLeftCycle, streamLeftCycleTable]
  · fin_cases j <;> simp [streamRightCycle, streamRightCycleTable]
  · fin_cases j <;> simp [streamLeftCycle, streamLeftCycleTable,
      streamRightCycle, streamRightCycleTable, List.Disjoint]

end Catalogue

lemma stream_row_of_bounds (j : Fin 13) (r : Fin 5 → ℝ)
    (hA0 : 0 < Catalogue.streamParameter j r)
    (hA1 : Catalogue.streamParameter j r < 1)
    (hr : ∀ i, 0 < r i)
    (hleftRate : ∀ i, Catalogue.streamSide j i →
      r i ≤ Catalogue.streamParameter j r / (Catalogue.streamPeriod j i : ℝ))
    (hrightRate : ∀ i, ¬ Catalogue.streamSide j i →
      r i ≤ (1 - Catalogue.streamParameter j r) /
        (Catalogue.streamPeriod j i : ℝ)) :
    SchedulableRates r := by
  have hleft : ∀ i, Catalogue.streamSide j i →
      IndexPeriodic (listCycle (Catalogue.streamLeftCycle j)) i
        (Catalogue.streamPeriod j i) (Catalogue.streamResidue j i) := by
    intro i hi
    exact listCycle_indexPeriodic
      (by
        fin_cases j <;> simp [Catalogue.streamLeftCycle,
          Catalogue.streamLeftCycleTable])
      (Catalogue.streamLeft_periodic j i hi)
  have hright : ∀ i, ¬ Catalogue.streamSide j i →
      IndexPeriodic (listCycle (Catalogue.streamRightCycle j)) i
        (Catalogue.streamPeriod j i) (Catalogue.streamResidue j i) := by
    intro i hi
    exact listCycle_indexPeriodic
      (by
        fin_cases j <;> simp [Catalogue.streamRightCycle,
          Catalogue.streamRightCycleTable])
      (Catalogue.streamRight_periodic j i hi)
  exact stream_schedulable_of_bounds
    (listCycle (Catalogue.streamLeftCycle j))
    (listCycle (Catalogue.streamRightCycle j))
    (Catalogue.streamSide j)
    (Catalogue.streamPeriod j) (Catalogue.streamResidue j)
    hA0 hA1 (Catalogue.stream_disjoint j) hleft hright r hr
    hleftRate hrightRate

lemma stream_row0 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 0, LinearLe v r 1) :
    SchedulableRates r := by
  have h01 : r 0 + 4 * r 1 ≤ 1 := by
    have h : LinearLe (loadVec 1 4 0 0 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 0 r
  · exact hr 0
  · norm_num [Catalogue.streamParameter]
    linarith [hr 1]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h01]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h01, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

lemma stream_row1 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 1, LinearLe v r 1) :
    SchedulableRates r := by
  have h04 : 4 * r 0 + r 4 ≤ 1 := by
    have h : LinearLe (loadVec 4 0 0 0 1) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 1 r
  · exact hr 4
  · norm_num [Catalogue.streamParameter]
    linarith [hr 0]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h04, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h04, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

lemma stream_row2 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 2, LinearLe v r 1) :
    SchedulableRates r := by
  have h01 : r 0 + 2 * r 1 ≤ 1 := by
    have h : LinearLe (loadVec 1 2 0 0 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  have h02 : r 0 + 4 * r 2 ≤ 1 := by
    have h : LinearLe (loadVec 1 0 4 0 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      right
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  have h03 : r 0 + 8 * r 3 ≤ 1 := by
    have h : LinearLe (loadVec 1 0 0 8 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      right
      right
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 2 r
  · exact hr 0
  · norm_num [Catalogue.streamParameter]
    linarith [hr 1]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h01, h02, h03, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h01, h02, h03, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

lemma stream_row3 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 3, LinearLe v r 1) :
    SchedulableRates r := by
  have h10 : 2 * r 0 + r 1 ≤ 1 := by
    have h : LinearLe (loadVec 2 1 0 0 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  have h12 : r 1 + 4 * r 2 ≤ 1 := by
    have h : LinearLe (loadVec 0 1 4 0 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      right
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  have h13 : r 1 + 8 * r 3 ≤ 1 := by
    have h : LinearLe (loadVec 0 1 0 8 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      right
      right
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 3 r
  · exact hr 1
  · norm_num [Catalogue.streamParameter]
    linarith [hr 0]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h10, h12, h13, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h10, h12, h13, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

lemma stream_row4 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 4, LinearLe v r 1) :
    SchedulableRates r := by
  have h04 : 2 * r 0 + r 4 ≤ 1 := by
    have h : LinearLe (loadVec 2 0 0 0 1) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  have h14 : 4 * r 1 + r 4 ≤ 1 := by
    have h : LinearLe (loadVec 0 4 0 0 1) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      right
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  have h24 : 8 * r 2 + r 4 ≤ 1 := by
    have h : LinearLe (loadVec 0 0 8 0 1) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      right
      right
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 4 r
  · exact hr 4
  · norm_num [Catalogue.streamParameter]
    linarith [hr 0]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h04, h14, h24, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h04, h14, h24, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

lemma stream_row5 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 5, LinearLe v r 1) :
    SchedulableRates r := by
  have h01 : r 0 + 3 * r 1 ≤ 1 := by
    have h : LinearLe (loadVec 1 3 0 0 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  have h03 : r 0 + 6 * r 3 ≤ 1 := by
    have h : LinearLe (loadVec 1 0 0 6 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      right
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 5 r
  · exact hr 0
  · norm_num [Catalogue.streamParameter]
    linarith [hr 1]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h01, h03, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h01, h03, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

lemma stream_row6 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 6, LinearLe v r 1) :
    SchedulableRates r := by
  have h02 : 3 * r 0 + r 2 ≤ 1 := by
    have h : LinearLe (loadVec 3 0 1 0 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  have h23 : r 2 + 6 * r 3 ≤ 1 := by
    have h : LinearLe (loadVec 0 0 1 6 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      right
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 6 r
  · exact hr 2
  · norm_num [Catalogue.streamParameter]
    linarith [hr 0]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h02, h23, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h02, h23, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

lemma stream_row7 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 7, LinearLe v r 1) :
    SchedulableRates r := by
  have h04 : 3 * r 0 + r 4 ≤ 1 := by
    have h : LinearLe (loadVec 3 0 0 0 1) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  have h24 : 6 * r 2 + r 4 ≤ 1 := by
    have h : LinearLe (loadVec 0 0 6 0 1) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      right
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 7 r
  · exact hr 4
  · norm_num [Catalogue.streamParameter]
    linarith [hr 0]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h04, h24, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h04, h24, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

lemma stream_row8 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 8, LinearLe v r 1) :
    SchedulableRates r := by
  have h02 : 2 * r 0 + 2 * r 2 ≤ 1 := by
    have h : LinearLe (loadVec 2 0 2 0 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  have h03 : 2 * r 0 + 4 * r 3 ≤ 1 := by
    have h : LinearLe (loadVec 2 0 0 4 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      right
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 8 r
  · norm_num [Catalogue.streamParameter]
    nlinarith [hr 0]
  · norm_num [Catalogue.streamParameter]
    linarith [hr 2]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h02, h03, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h02, h03, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

lemma stream_row9 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 9, LinearLe v r 1) :
    SchedulableRates r := by
  have h01 : 2 * r 0 + 2 * r 1 ≤ 1 := by
    have h : LinearLe (loadVec 2 2 0 0 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  have h13 : 2 * r 1 + 4 * r 3 ≤ 1 := by
    have h : LinearLe (loadVec 0 2 0 4 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      right
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 9 r
  · norm_num [Catalogue.streamParameter]
    nlinarith [hr 1]
  · norm_num [Catalogue.streamParameter]
    linarith [hr 0]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h01, h13, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h01, h13, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

lemma stream_row10 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 10, LinearLe v r 1) :
    SchedulableRates r := by
  have h03 : 2 * r 0 + 2 * r 3 ≤ 1 := by
    have h : LinearLe (loadVec 2 0 0 2 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  have h13 : 4 * r 1 + 2 * r 3 ≤ 1 := by
    have h : LinearLe (loadVec 0 4 0 2 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      right
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 10 r
  · norm_num [Catalogue.streamParameter]
    nlinarith [hr 3]
  · norm_num [Catalogue.streamParameter]
    linarith [hr 0]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h03, h13, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h03, h13, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

lemma stream_row11 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 11, LinearLe v r 1) :
    SchedulableRates r := by
  have h02 : 2 * r 0 + 3 * r 2 ≤ 1 := by
    have h : LinearLe (loadVec 2 0 3 0 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 11 r
  · norm_num [Catalogue.streamParameter]
    nlinarith [hr 0]
  · norm_num [Catalogue.streamParameter]
    linarith [hr 2]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h02, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h02, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

lemma stream_row12 (r : Fin 5 → ℝ) (ho : OrderedFive r)
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads 12, LinearLe v r 1) :
    SchedulableRates r := by
  have h03 : 3 * r 0 + 2 * r 3 ≤ 1 := by
    have h : LinearLe (loadVec 3 0 0 2 0) r 1 := hloads _ (by
      simp only [Catalogue.streamLoads, List.mem_cons, List.not_mem_nil]
      left
      rfl)
    simpa [LinearLe, sum_fin5, loadVec] using h
  apply stream_row_of_bounds 12 r
  · norm_num [Catalogue.streamParameter]
    nlinarith [hr 3]
  · norm_num [Catalogue.streamParameter]
    linarith [hr 0]
  · exact hr
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h03, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  · intro i hi
    fin_cases i <;>
      simp [Catalogue.streamSide, Catalogue.streamLeftCycle,
        Catalogue.streamLeftCycleTable, Catalogue.streamParameter,
        Catalogue.streamPeriod, Catalogue.streamPeriodTable] at hi ⊢
    all_goals norm_num
    all_goals linarith [h03, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

theorem stream_catalogue_schedulable (j : Fin 13) (r : Fin 5 → ℝ)
    (ho : OrderedFive r) (hr : ∀ i, 0 < r i)
    (hloads : ∀ v ∈ Catalogue.streamLoads j, LinearLe v r 1) :
    SchedulableRates r := by
  fin_cases j
  · exact stream_row0 r ho hr hloads
  · exact stream_row1 r ho hr hloads
  · exact stream_row2 r ho hr hloads
  · exact stream_row3 r ho hr hloads
  · exact stream_row4 r ho hr hloads
  · exact stream_row5 r ho hr hloads
  · exact stream_row6 r ho hr hloads
  · exact stream_row7 r ho hr hloads
  · exact stream_row8 r ho hr hloads
  · exact stream_row9 r ho hr hloads
  · exact stream_row10 r ho hr hloads
  · exact stream_row11 r ho hr hloads
  · exact stream_row12 r ho hr hloads

end RealPinwheel
