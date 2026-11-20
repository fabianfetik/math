import CorralFormalization.Core
import CorralFormalization.ListTools
import CorralFormalization.Arithmetic

set_option maxHeartbeats 0

namespace CorralFormalization

/-- The first indexed pair in the paper's odd word (4). -/
def oddConstructionFirstPair (A j : ℕ) : List ℕ :=
  [4 * A + 3 - 3 - 4 * j, 4 * j + 5]

/-- The second indexed pair in the paper's odd word (4). -/
def oddConstructionSecondPair (A j : ℕ) : List ℕ :=
  [4 * j + 2, 4 * A + 3 - 4 - 4 * j]

/-- The first indexed block of pairs in the word. -/
def oddConstructionFirstPairs (A : ℕ) : List ℕ :=
  (List.range A).flatMap (oddConstructionFirstPair A)

/-- The second indexed block of pairs in the word. -/
def oddConstructionSecondPairs (A : ℕ) : List ℕ :=
  (List.range (A - 1)).flatMap (oddConstructionSecondPair A)

/-- The initial portion before the second indexed pair family. -/
def oddConstructionPreSecond (A : ℕ) : List ℕ :=
  [4 * A + 5, 4 * A + 2] ++ oddConstructionFirstPairs A ++ [4 * A + 4]

/-- The concrete positive gap word in manuscript (4), in its stated order. -/
def oddConstructionGapWord (A : ℕ) : List ℕ :=
  [4 * A + 5, 4 * A + 2] ++
    oddConstructionFirstPairs A ++
    [4 * A + 4] ++
    oddConstructionSecondPairs A ++
    [4 * A - 2, 1]

/-- Sum of the first `j` entries of the actual paper word. -/
def oddConstructionPrefix (A j : ℕ) : ℕ :=
  ((oddConstructionGapWord A).take j).sum

def oddConstructionFirstEvenStream (A : ℕ) : List ℕ :=
  (List.range A).map (fun j => 4 * A + 3 - 3 - 4 * j)

def oddConstructionFirstOddStream (A : ℕ) : List ℕ :=
  (List.range A).map (fun j => 4 * j + 5)

def oddConstructionSecondEvenStream (A : ℕ) : List ℕ :=
  (List.range (A - 1)).map (fun j => 4 * j + 2)

def oddConstructionSecondOddStream (A : ℕ) : List ℕ :=
  (List.range (A - 1)).map (fun j => 4 * A + 3 - 4 - 4 * j)

/-- Canonical inventory of the permitted values, grouped by residue class
modulo four. The four groups enumerate respectively the multiples of four
from `4` through `4*A+4`, the values congruent to two from `2` through
`4*A+2`, the values congruent to one from `1` through `4*A+5`, and the
values congruent to three from `7` through `4*A-1`. -/
def oddConstructionInventoryClass0 (A : ℕ) : List ℕ :=
  (List.range A).map (fun j => 4 * j + 4) ++ [4 * A + 4]

def oddConstructionInventoryClass2 (A : ℕ) : List ℕ :=
  [4 * A + 2] ++ oddConstructionSecondEvenStream A ++ [4 * A - 2]

def oddConstructionInventoryClass1 (A : ℕ) : List ℕ :=
  [1] ++ oddConstructionFirstOddStream A ++ [4 * A + 5]

def oddConstructionInventoryClass3 (A : ℕ) : List ℕ :=
  (List.range (A - 1)).map (fun j => 4 * j + 7)

def oddConstructionGapInventory (A : ℕ) : List ℕ :=
  oddConstructionInventoryClass0 A ++ oddConstructionInventoryClass2 A ++
    oddConstructionInventoryClass1 A ++ oddConstructionInventoryClass3 A

/-- Canonical increasing list for each permitted residue class modulo four. -/
def oddConstructionInventoryCanonicalClass0 (A : ℕ) : List ℕ :=
  (List.range (A + 1)).map (fun j => 4 * j + 4)

def oddConstructionInventoryCanonicalClass2 (A : ℕ) : List ℕ :=
  (List.range (A + 1)).map (fun j => 4 * j + 2)

def oddConstructionInventoryCanonicalClass1 (A : ℕ) : List ℕ :=
  (List.range (A + 2)).map (fun j => 4 * j + 1)

def oddConstructionInventoryCanonicalClass3 (A : ℕ) : List ℕ :=
  (List.range (A - 1)).map (fun j => 4 * j + 7)

/-- The ordinary interval inventory with the two excluded odd values removed,
written as four explicit residue-class ranges. -/
def oddConstructionGapCanonicalInventory (A : ℕ) : List ℕ :=
  oddConstructionInventoryCanonicalClass0 A ++ oddConstructionInventoryCanonicalClass2 A ++
    oddConstructionInventoryCanonicalClass1 A ++ oddConstructionInventoryCanonicalClass3 A

theorem oddConstructionFirstPairs_perm_streams (A : ℕ) :
    List.Perm (oddConstructionFirstPairs A)
      (oddConstructionFirstEvenStream A ++ oddConstructionFirstOddStream A) := by
  change List.Perm
    ((List.range A).flatMap (fun j => [4 * A + 3 - 3 - 4 * j, 4 * j + 5]))
    ((List.range A).map (fun j => 4 * A + 3 - 3 - 4 * j) ++
      (List.range A).map (fun j => 4 * j + 5))
  exact interleave_perm (List.range A)
    (fun j => 4 * A + 3 - 3 - 4 * j) (fun j => 4 * j + 5)

theorem oddConstructionSecondPairs_perm_streams (A : ℕ) :
    List.Perm (oddConstructionSecondPairs A)
      (oddConstructionSecondEvenStream A ++ oddConstructionSecondOddStream A) := by
  change List.Perm
    ((List.range (A - 1)).flatMap (fun j => [4 * j + 2, 4 * A + 3 - 4 - 4 * j]))
    ((List.range (A - 1)).map (fun j => 4 * j + 2) ++
      (List.range (A - 1)).map (fun j => 4 * A + 3 - 4 - 4 * j))
  exact interleave_perm (List.range (A - 1))
    (fun j => 4 * j + 2) (fun j => 4 * A + 3 - 4 - 4 * j)

theorem oddConstruction_inventory_chunk_perm (A : ℕ) :
    List.Perm
      ([4 * A + 5] ++ [4 * A + 2] ++ oddConstructionFirstEvenStream A ++
        oddConstructionFirstOddStream A ++ [4 * A + 4] ++
        oddConstructionSecondEvenStream A ++ oddConstructionSecondOddStream A ++
        [4 * A - 2] ++ [1])
      (oddConstructionFirstEvenStream A ++ [4 * A + 4] ++ [4 * A + 2] ++
        oddConstructionSecondEvenStream A ++ [4 * A - 2] ++ [1] ++
        oddConstructionFirstOddStream A ++ [4 * A + 5] ++
        oddConstructionSecondOddStream A) := by
  let T : List ℕ := [4 * A + 5]
  let H : List ℕ := [4 * A + 2]
  let F : List ℕ := oddConstructionFirstEvenStream A
  let O : List ℕ := oddConstructionFirstOddStream A
  let D : List ℕ := [4 * A + 4]
  let E : List ℕ := oddConstructionSecondEvenStream A
  let Z : List ℕ := oddConstructionSecondOddStream A
  let X : List ℕ := [4 * A - 2]
  let Y : List ℕ := [1]
  have h01 : List.Perm
      (T ++ H ++ F ++ O ++ D ++ E ++ Z ++ X ++ Y)
      (F ++ T ++ H ++ O ++ D ++ E ++ Z ++ X ++ Y) := by
    simpa [List.append_assoc] using
      swap_blocks_perm ([] : List ℕ) (T ++ H) F
        (O ++ D ++ E ++ Z ++ X ++ Y)
  have h12 : List.Perm
      (F ++ T ++ H ++ O ++ D ++ E ++ Z ++ X ++ Y)
      (F ++ D ++ T ++ H ++ O ++ E ++ Z ++ X ++ Y) := by
    simpa [List.append_assoc] using
      swap_blocks_perm F (T ++ H ++ O) D (E ++ Z ++ X ++ Y)
  have h23 : List.Perm
      (F ++ D ++ T ++ H ++ O ++ E ++ Z ++ X ++ Y)
      (F ++ D ++ H ++ T ++ O ++ E ++ Z ++ X ++ Y) := by
    simpa [List.append_assoc] using
      swap_blocks_perm (F ++ D) T H (O ++ E ++ Z ++ X ++ Y)
  have h34 : List.Perm
      (F ++ D ++ H ++ T ++ O ++ E ++ Z ++ X ++ Y)
      (F ++ D ++ H ++ E ++ T ++ O ++ Z ++ X ++ Y) := by
    simpa [List.append_assoc] using
      swap_blocks_perm (F ++ D ++ H) (T ++ O) E (Z ++ X ++ Y)
  have h45 : List.Perm
      (F ++ D ++ H ++ E ++ T ++ O ++ Z ++ X ++ Y)
      (F ++ D ++ H ++ E ++ T ++ O ++ X ++ Y ++ Z) := by
    simpa [List.append_assoc] using
      swap_blocks_perm (F ++ D ++ H ++ E ++ T ++ O) Z (X ++ Y) []
  have h56 : List.Perm
      (F ++ D ++ H ++ E ++ T ++ O ++ X ++ Y ++ Z)
      (F ++ D ++ H ++ E ++ X ++ Y ++ T ++ O ++ Z) := by
    simpa [List.append_assoc] using
      swap_blocks_perm (F ++ D ++ H ++ E) (T ++ O) (X ++ Y) Z
  have h67 : List.Perm
      (F ++ D ++ H ++ E ++ X ++ Y ++ T ++ O ++ Z)
      (F ++ D ++ H ++ E ++ X ++ Y ++ O ++ T ++ Z) := by
    simpa [List.append_assoc] using
      swap_blocks_perm (F ++ D ++ H ++ E ++ X ++ Y) T O Z
  have hshuffle : List.Perm
      (T ++ H ++ F ++ O ++ D ++ E ++ Z ++ X ++ Y)
      (F ++ D ++ H ++ E ++ X ++ Y ++ O ++ T ++ Z) := by
    exact h01.trans (h12.trans (h23.trans (h34.trans (h45.trans (h56.trans h67)))))
  simpa [T, H, F, O, D, E, Z, X, Y, List.append_assoc] using hshuffle

theorem oddConstruction_firstEven_stream_perm (A : ℕ) :
    List.Perm ((List.range A).map (fun j => 4 * A + 3 - 3 - 4 * j))
      ((List.range A).map (fun j => 4 * j + 4)) := by
  have hrev : (((List.range A).map (fun j => 4 * j + 4)).reverse) =
      (List.range A).map (fun j => 4 * A + 3 - 3 - 4 * j) := by
    rw [← List.map_reverse, List.range_eq_range', List.reverse_range',
      ← List.range_eq_range', List.map_map]
    apply List.map_congr_left
    intro j hj
    have hjlt : j < A := List.mem_range.mp hj
    simp only [Function.comp_apply]
    omega
  exact hrev ▸ List.reverse_perm _

theorem oddConstruction_secondOdd_stream_perm (A : ℕ) (hA : 2 ≤ A) :
    List.Perm ((List.range (A - 1)).map (fun j => 4 * A - 1 - 4 * j))
      ((List.range (A - 1)).map (fun j => 4 * j + 7)) := by
  have hrev : (((List.range (A - 1)).map (fun j => 4 * j + 7)).reverse) =
      (List.range (A - 1)).map (fun j => 4 * A - 1 - 4 * j) := by
    rw [← List.map_reverse, List.range_eq_range', List.reverse_range',
      ← List.range_eq_range', List.map_map]
    apply List.map_congr_left
    intro j hj
    have hjlt : j < A - 1 := List.mem_range.mp hj
    simp only [Function.comp_apply]
    omega
  exact hrev ▸ List.reverse_perm _

theorem oddConstructionGapWord_perm_inventory (A : ℕ) (hA : 2 ≤ A) :
    List.Perm (oddConstructionGapWord A) (oddConstructionGapInventory A) := by
  have hfirst := oddConstructionFirstPairs_perm_streams A
  have hsecond := oddConstructionSecondPairs_perm_streams A
  have hstream : List.Perm (oddConstructionGapWord A)
      ([4 * A + 5] ++ [4 * A + 2] ++ oddConstructionFirstEvenStream A ++
        oddConstructionFirstOddStream A ++ [4 * A + 4] ++
        oddConstructionSecondEvenStream A ++ oddConstructionSecondOddStream A ++
        [4 * A - 2] ++ [1]) := by
    have hdecomp : oddConstructionGapWord A =
        [4 * A + 5, 4 * A + 2] ++ oddConstructionFirstPairs A ++
          [4 * A + 4] ++ oddConstructionSecondPairs A ++ [4 * A - 2, 1] := rfl
    rw [hdecomp]
    have h1ctx := perm_in_context hfirst [4 * A + 5, 4 * A + 2]
      ([4 * A + 4] ++ oddConstructionSecondPairs A ++ [4 * A - 2, 1])
    have h2ctx := perm_in_context hsecond
      ([4 * A + 5, 4 * A + 2] ++ oddConstructionFirstEvenStream A ++
        oddConstructionFirstOddStream A ++ [4 * A + 4])
      [4 * A - 2, 1]
    have h1ctx' : List.Perm
        ([4 * A + 5, 4 * A + 2] ++ oddConstructionFirstPairs A ++ [4 * A + 4] ++
          oddConstructionSecondPairs A ++ [4 * A - 2, 1])
        ([4 * A + 5, 4 * A + 2] ++ oddConstructionFirstEvenStream A ++
          oddConstructionFirstOddStream A ++ [4 * A + 4] ++
          oddConstructionSecondPairs A ++ [4 * A - 2, 1]) := by
      simpa [List.append_assoc] using h1ctx
    have h2ctx' : List.Perm
        ([4 * A + 5, 4 * A + 2] ++ oddConstructionFirstEvenStream A ++
          oddConstructionFirstOddStream A ++ [4 * A + 4] ++
          oddConstructionSecondPairs A ++ [4 * A - 2, 1])
        ([4 * A + 5] ++ [4 * A + 2] ++ oddConstructionFirstEvenStream A ++
          oddConstructionFirstOddStream A ++ [4 * A + 4] ++
          oddConstructionSecondEvenStream A ++ oddConstructionSecondOddStream A ++
          [4 * A - 2] ++ [1]) := by
      simpa [List.append_assoc] using h2ctx
    exact h1ctx'.trans h2ctx'
  have hgroup := oddConstruction_inventory_chunk_perm A
  have hfirstrev := oddConstruction_firstEven_stream_perm A
  have hsecondrev := oddConstruction_secondOdd_stream_perm A hA
  have hgrouped : List.Perm (oddConstructionGapWord A)
      (oddConstructionGapInventory A) := by
    apply List.Perm.trans hstream
    apply List.Perm.trans hgroup
    have hfrev := perm_in_context hfirstrev []
      ([4 * A + 4] ++ [4 * A + 2] ++ oddConstructionSecondEvenStream A ++
        [4 * A - 2] ++ [1] ++ oddConstructionFirstOddStream A ++ [4 * A + 5] ++
        oddConstructionSecondOddStream A)
    have hsecondrevctx := perm_in_context hsecondrev
      ((List.range A).map (fun j => 4 * j + 4) ++ [4 * A + 4] ++ [4 * A + 2] ++
        oddConstructionSecondEvenStream A ++ [4 * A - 2] ++ [1] ++
        oddConstructionFirstOddStream A ++ [4 * A + 5]) []
    have hfrev' := by
      simpa [List.append_assoc] using hfrev
    have hsecondrevctx' := by
      simpa [List.append_assoc] using hsecondrevctx
    simpa [oddConstructionGapInventory, oddConstructionInventoryClass0,
      oddConstructionInventoryClass1, oddConstructionInventoryClass2,
      oddConstructionInventoryClass3, oddConstructionFirstEvenStream,
      oddConstructionFirstOddStream, oddConstructionSecondEvenStream,
      oddConstructionSecondOddStream, List.append_assoc] using hfrev'.trans hsecondrevctx'
  exact hgrouped

theorem oddConstructionInventoryClass0_eq_canonical (A : ℕ) :
    oddConstructionInventoryClass0 A = oddConstructionInventoryCanonicalClass0 A := by
  unfold oddConstructionInventoryClass0 oddConstructionInventoryCanonicalClass0
  rw [List.range_succ, List.map_append]
  simp

theorem oddConstructionInventoryClass1_eq_canonical (A : ℕ) :
    oddConstructionInventoryClass1 A = oddConstructionInventoryCanonicalClass1 A := by
  unfold oddConstructionInventoryClass1 oddConstructionInventoryCanonicalClass1 oddConstructionFirstOddStream
  have hsplit : List.range (A + 2) =
      List.range 1 ++ (List.range (A + 1)).map (fun j => 1 + j) := by
    rw [show A + 2 = 1 + (A + 1) by omega, List.range_add]
  rw [hsplit]
  simp only [List.range_one, List.map_cons, List.map_nil, List.map_append,
    List.map_map]
  rw [List.range_succ, List.map_append]
  simp [Function.comp_def]
  constructor
  · intro a ha
    omega
  · omega

theorem oddConstructionInventoryClass2_perm_canonical (A : ℕ) (hA : 2 ≤ A) :
    List.Perm (oddConstructionInventoryClass2 A)
      (oddConstructionInventoryCanonicalClass2 A) := by
  have hrange : List.range (A + 1) = List.range (A - 1) ++ [A - 1, A] := by
    calc
      List.range (A + 1) = List.range ((A - 1) + 2) := by congr 1; omega
      _ = List.range (A - 1) ++ (List.range 2).map (fun x => A - 1 + x) := by
        rw [List.range_add]
      _ = List.range (A - 1) ++ [A - 1, A] := by
        simp [List.range_succ]
        omega
  have hcanonical : oddConstructionInventoryCanonicalClass2 A =
      oddConstructionSecondEvenStream A ++ [4 * A - 2, 4 * A + 2] := by
    unfold oddConstructionInventoryCanonicalClass2 oddConstructionSecondEvenStream
    rw [hrange, List.map_append]
    simp
    omega
  unfold oddConstructionInventoryClass2
  rw [hcanonical]
  simpa [List.append_assoc] using
    (List.perm_append_comm : List.Perm
      ([4 * A + 2] ++ (oddConstructionSecondEvenStream A ++ [4 * A - 2]))
      ((oddConstructionSecondEvenStream A ++ [4 * A - 2]) ++ [4 * A + 2]))

theorem oddConstructionInventoryClass3_eq_canonical (A : ℕ) :
    oddConstructionInventoryClass3 A = oddConstructionInventoryCanonicalClass3 A := rfl

theorem oddConstructionGapInventory_perm_canonical (A : ℕ) (hA : 2 ≤ A) :
    List.Perm (oddConstructionGapInventory A) (oddConstructionGapCanonicalInventory A) := by
  have h0 : List.Perm (oddConstructionInventoryClass0 A)
      (oddConstructionInventoryCanonicalClass0 A) := by
    rw [oddConstructionInventoryClass0_eq_canonical]
  have h2 := oddConstructionInventoryClass2_perm_canonical A hA
  have h1 : List.Perm (oddConstructionInventoryClass1 A)
      (oddConstructionInventoryCanonicalClass1 A) := by
    rw [oddConstructionInventoryClass1_eq_canonical]
  have h3 : List.Perm (oddConstructionInventoryClass3 A)
      (oddConstructionInventoryCanonicalClass3 A) := by
    rw [oddConstructionInventoryClass3_eq_canonical]
  simpa [oddConstructionGapInventory, oddConstructionGapCanonicalInventory,
    List.append_assoc] using h0.append (h2.append (h1.append h3))

theorem oddConstructionFirstPair_sum (A j : ℕ) (hAj : j < A) :
    (oddConstructionFirstPair A j).sum = 4 * A + 5 := by
  simp [oddConstructionFirstPair]
  omega

theorem oddConstructionSecondPair_sum (A j : ℕ) (hAj : j < A - 1) :
    (oddConstructionSecondPair A j).sum = 4 * A + 1 := by
  simp [oddConstructionSecondPair]
  omega

theorem oddConstructionFirstPair_positive (A j : ℕ) (hAj : j < A) :
    ∀ x ∈ oddConstructionFirstPair A j, 0 < x := by
  intro x hx
  simp [oddConstructionFirstPair] at hx
  rcases hx with h | h
  · subst x
    omega
  · subst x
    omega

theorem oddConstructionSecondPair_positive (A j : ℕ) (hA : 2 ≤ A)
    (hAj : j < A - 1) :
    ∀ x ∈ oddConstructionSecondPair A j, 0 < x := by
  intro x hx
  simp [oddConstructionSecondPair] at hx
  rcases hx with h | h
  · subst x
    omega
  · subst x
    have hsecond : 4 * A - 1 - 4 * j = 4 * (A - 1 - j) + 3 := by omega
    rw [hsecond]
    omega

theorem oddConstructionFirstPairs_positive (A : ℕ) {x : ℕ}
    (hx : x ∈ oddConstructionFirstPairs A) : 0 < x := by
  rcases List.mem_flatMap.mp hx with ⟨j, hj, hxj⟩
  exact oddConstructionFirstPair_positive A j (List.mem_range.mp hj) x hxj

theorem oddConstructionSecondPairs_positive (A : ℕ) {x : ℕ}
    (hx : x ∈ oddConstructionSecondPairs A) : 0 < x := by
  rcases List.mem_flatMap.mp hx with ⟨j, hj, hxj⟩
  have hAj : j < A - 1 := List.mem_range.mp hj
  have hA : 2 ≤ A := by omega
  exact oddConstructionSecondPair_positive A j hA hAj x hxj

theorem oddConstructionFirstPairs_upto_length (A t : ℕ) :
    ((List.range t).flatMap (oddConstructionFirstPair A)).length = 2 * t := by
  rw [length_flatMap_eq_sum_lengths]
  rw [sum_map_const_on (List.range t)
    (fun j => (oddConstructionFirstPair A j).length) 2]
  · simp [List.length_range, Nat.mul_comm]
  · intro j hj
    simp [oddConstructionFirstPair]

theorem oddConstructionFirstPairs_length (A : ℕ) :
    (oddConstructionFirstPairs A).length = 2 * A := by
  exact oddConstructionFirstPairs_upto_length A A

theorem oddConstructionFirstPairs_take_complete (A t : ℕ) (ht : t ≤ A) :
    (oddConstructionFirstPairs A).take (2 * t) =
      (List.range t).flatMap (oddConstructionFirstPair A) := by
  have hsplit : List.range A =
      List.range t ++ List.map (fun x => t + x) (List.range (A - t)) := by
    calc
      List.range A = List.range (t + (A - t)) := by congr 1; omega
      _ = _ := by rw [List.range_add]
  change ((List.range A).flatMap (oddConstructionFirstPair A)).take (2 * t) = _
  rw [hsplit, List.flatMap_append]
  have hlen : ((List.range t).flatMap (oddConstructionFirstPair A)).length = 2 * t :=
    oddConstructionFirstPairs_upto_length A t
  rw [List.take_append_of_le_length (by rw [hlen])]
  rw [← hlen, List.take_length]

theorem oddConstructionFirstPairs_upto_sum (A t : ℕ) (ht : t ≤ A) :
    ((List.range t).flatMap (oddConstructionFirstPair A)).sum =
      t * (4 * A + 5) := by
  rw [sum_flatMap_eq_sum_sums]
  rw [sum_map_const_on (List.range t)
    (fun j => (oddConstructionFirstPair A j).sum) (4 * A + 5)]
  · simp [List.length_range]
  · intro j hj
    have hjt : j < t := List.mem_range.mp hj
    exact oddConstructionFirstPair_sum A j (by omega)

theorem oddConstructionFirstPairs_take_complete_sum (A t : ℕ) (ht : t ≤ A) :
    ((oddConstructionFirstPairs A).take (2 * t)).sum = t * (4 * A + 5) := by
  rw [oddConstructionFirstPairs_take_complete A t ht]
  exact oddConstructionFirstPairs_upto_sum A t ht

theorem oddConstructionFirstPairs_take_one_more (A t : ℕ) (ht : t < A) :
    (oddConstructionFirstPairs A).take (2 * t + 1) =
      (List.range t).flatMap (oddConstructionFirstPair A) ++
        [4 * A + 3 - 3 - 4 * t] := by
  have hsplit : List.range A =
      List.range (t + 1) ++
        List.map (fun x => t + 1 + x) (List.range (A - (t + 1))) := by
    calc
      List.range A = List.range ((t + 1) + (A - (t + 1))) := by
        congr 1
        omega
      _ = _ := by rw [List.range_add]
  have hdecomp : oddConstructionFirstPairs A =
      (List.range t).flatMap (oddConstructionFirstPair A) ++
        (oddConstructionFirstPair A t ++
          ((List.map (fun x => t + 1 + x) (List.range (A - (t + 1)))).flatMap
            (oddConstructionFirstPair A))) := by
    change (List.range A).flatMap (oddConstructionFirstPair A) = _
    rw [hsplit, List.flatMap_append, List.range_succ, List.flatMap_append]
    simp [List.flatMap]
  rw [hdecomp, List.take_append]
  have hlen : ((List.range t).flatMap (oddConstructionFirstPair A)).length = 2 * t :=
    oddConstructionFirstPairs_upto_length A t
  have htake : ((List.range t).flatMap (oddConstructionFirstPair A)).take
      (2 * t + 1) = (List.range t).flatMap (oddConstructionFirstPair A) :=
    List.take_of_length_le (by rw [hlen]; omega)
  rw [htake]
  have hdiff : 2 * t + 1 -
      ((List.range t).flatMap (oddConstructionFirstPair A)).length = 1 := by
    rw [hlen]
    omega
  rw [hdiff, List.take_append_of_le_length]
  · simp [oddConstructionFirstPair]
  · simp [oddConstructionFirstPair]

theorem oddConstructionFirstPairs_take_one_more_sum (A t : ℕ) (ht : t < A) :
    ((oddConstructionFirstPairs A).take (2 * t + 1)).sum =
      t * (4 * A + 5) + (4 * A + 3 - 3 - 4 * t) := by
  rw [oddConstructionFirstPairs_take_one_more A t ht]
  simp [oddConstructionFirstPairs_upto_sum A t (by omega)]

theorem oddConstructionSecondPairs_upto_length (A t : ℕ) :
    ((List.range t).flatMap (oddConstructionSecondPair A)).length = 2 * t := by
  rw [length_flatMap_eq_sum_lengths]
  rw [sum_map_const_on (List.range t)
    (fun j => (oddConstructionSecondPair A j).length) 2]
  · simp [List.length_range, Nat.mul_comm]
  · intro j hj
    simp [oddConstructionSecondPair]

theorem oddConstructionSecondPairs_take_complete (A t : ℕ) (ht : t ≤ A - 1) :
    (oddConstructionSecondPairs A).take (2 * t) =
      (List.range t).flatMap (oddConstructionSecondPair A) := by
  have hsplit : List.range (A - 1) =
      List.range t ++ List.map (fun x => t + x) (List.range (A - 1 - t)) := by
    calc
      List.range (A - 1) = List.range (t + ((A - 1) - t)) := by congr 1; omega
      _ = _ := by rw [List.range_add]
  change ((List.range (A - 1)).flatMap (oddConstructionSecondPair A)).take (2 * t) = _
  rw [hsplit, List.flatMap_append]
  have hlen : ((List.range t).flatMap (oddConstructionSecondPair A)).length = 2 * t :=
    oddConstructionSecondPairs_upto_length A t
  rw [List.take_append_of_le_length (by rw [hlen])]
  rw [← hlen, List.take_length]

theorem oddConstructionSecondPairs_upto_sum (A t : ℕ) (ht : t ≤ A - 1) :
    ((List.range t).flatMap (oddConstructionSecondPair A)).sum =
      t * (4 * A + 1) := by
  rw [sum_flatMap_eq_sum_sums]
  rw [sum_map_const_on (List.range t)
    (fun j => (oddConstructionSecondPair A j).sum) (4 * A + 1)]
  · simp [List.length_range]
  · intro j hj
    have hjt : j < t := List.mem_range.mp hj
    exact oddConstructionSecondPair_sum A j (by omega)

theorem oddConstructionSecondPairs_take_complete_sum (A t : ℕ)
    (ht : t ≤ A - 1) :
    ((oddConstructionSecondPairs A).take (2 * t)).sum = t * (4 * A + 1) := by
  rw [oddConstructionSecondPairs_take_complete A t ht]
  exact oddConstructionSecondPairs_upto_sum A t ht

theorem oddConstructionSecondPairs_take_one_more (A t : ℕ) (ht : t < A - 1) :
    (oddConstructionSecondPairs A).take (2 * t + 1) =
      (List.range t).flatMap (oddConstructionSecondPair A) ++ [4 * t + 2] := by
  have hsplit : List.range (A - 1) =
      List.range (t + 1) ++
        List.map (fun x => t + 1 + x) (List.range (A - 1 - (t + 1))) := by
    calc
      List.range (A - 1) =
          List.range ((t + 1) + ((A - 1) - (t + 1))) := by congr 1; omega
      _ = _ := by rw [List.range_add]
  have hdecomp : oddConstructionSecondPairs A =
      (List.range t).flatMap (oddConstructionSecondPair A) ++
        (oddConstructionSecondPair A t ++
          ((List.map (fun x => t + 1 + x) (List.range (A - 1 - (t + 1)))).flatMap
            (oddConstructionSecondPair A))) := by
    change (List.range (A - 1)).flatMap (oddConstructionSecondPair A) = _
    rw [hsplit, List.flatMap_append, List.range_succ, List.flatMap_append]
    simp [List.flatMap]
  rw [hdecomp, List.take_append]
  have hlen : ((List.range t).flatMap (oddConstructionSecondPair A)).length = 2 * t :=
    oddConstructionSecondPairs_upto_length A t
  have htake : ((List.range t).flatMap (oddConstructionSecondPair A)).take
      (2 * t + 1) = (List.range t).flatMap (oddConstructionSecondPair A) :=
    List.take_of_length_le (by rw [hlen]; omega)
  rw [htake]
  have hdiff : 2 * t + 1 -
      ((List.range t).flatMap (oddConstructionSecondPair A)).length = 1 := by
    rw [hlen]
    omega
  rw [hdiff, List.take_append_of_le_length]
  · simp [oddConstructionSecondPair]
  · simp [oddConstructionSecondPair]

theorem oddConstructionSecondPairs_take_one_more_sum (A t : ℕ)
    (ht : t < A - 1) :
    ((oddConstructionSecondPairs A).take (2 * t + 1)).sum =
      t * (4 * A + 1) + (4 * t + 2) := by
  rw [oddConstructionSecondPairs_take_one_more A t ht]
  simp [oddConstructionSecondPairs_upto_sum A t (by omega)]

theorem oddConstructionPreSecond_length (A : ℕ) :
    (oddConstructionPreSecond A).length = 2 * A + 3 := by
  simp [oddConstructionPreSecond, oddConstructionFirstPairs_length, List.length_append]

theorem oddConstructionPreSecond_sum (A : ℕ) :
    (oddConstructionPreSecond A).sum = (A + 3) * (4 * A + 3) + 2 * A + 2 := by
  simp only [oddConstructionPreSecond, List.sum_append, List.sum_cons, List.sum_nil]
  rw [oddConstructionFirstPairs]
  rw [oddConstructionFirstPairs_upto_sum A A (by omega)]
  ring

theorem oddConstructionGapWord_eq_preSecond (A : ℕ) :
    oddConstructionGapWord A =
      oddConstructionPreSecond A ++ (oddConstructionSecondPairs A ++ [4 * A - 2, 1]) := by
  simp [oddConstructionGapWord, oddConstructionPreSecond, List.append_assoc]

theorem oddConstructionGapWord_take_second_block (A j : ℕ)
    (hlo : 2 * A + 3 ≤ j) (hhi : j ≤ 4 * A + 1) :
    (oddConstructionGapWord A).take j =
      oddConstructionPreSecond A ++
        (oddConstructionSecondPairs A).take (j - (2 * A + 3)) := by
  rw [oddConstructionGapWord_eq_preSecond]
  rw [List.take_append]
  have hpre : (oddConstructionPreSecond A).take j = oddConstructionPreSecond A :=
    List.take_of_length_le (by rw [oddConstructionPreSecond_length]; omega)
  rw [hpre]
  have hcut : j - (oddConstructionPreSecond A).length ≤
      (oddConstructionSecondPairs A).length := by
    rw [oddConstructionPreSecond_length]
    have hsecondlen : (oddConstructionSecondPairs A).length = 2 * (A - 1) := by
      change ((List.range (A - 1)).flatMap (oddConstructionSecondPair A)).length = _
      exact oddConstructionSecondPairs_upto_length A (A - 1)
    rw [hsecondlen]
    omega
  rw [List.take_append_of_le_length hcut]
  simp [oddConstructionPreSecond_length]

theorem oddConstructionGapWord_take_final_prefix (A : ℕ) (hA : 2 ≤ A) :
    (oddConstructionGapWord A).take (4 * A + 2) =
      oddConstructionPreSecond A ++ (oddConstructionSecondPairs A ++ [4 * A - 2]) := by
  rw [oddConstructionGapWord_eq_preSecond, List.take_append]
  have hpre : (oddConstructionPreSecond A).take (4 * A + 2) = oddConstructionPreSecond A :=
    List.take_of_length_le (by rw [oddConstructionPreSecond_length]; omega)
  rw [hpre]
  have hsecondlen : (oddConstructionSecondPairs A).length = 2 * (A - 1) := by
    change ((List.range (A - 1)).flatMap (oddConstructionSecondPair A)).length = _
    exact oddConstructionSecondPairs_upto_length A (A - 1)
  rw [List.take_append]
  have hsecond : (oddConstructionSecondPairs A).take (4 * A + 2 -
      (oddConstructionPreSecond A).length) = oddConstructionSecondPairs A := by
    apply List.take_of_length_le
    rw [oddConstructionPreSecond_length, hsecondlen]
    omega
  rw [hsecond]
  have hlast : 4 * A + 2 - (oddConstructionPreSecond A).length -
      (oddConstructionSecondPairs A).length = 1 := by
    rw [oddConstructionPreSecond_length, hsecondlen]
    omega
  rw [hlast]
  simp

theorem oddConstructionPrefix_final_value (A : ℕ) (hA : 2 ≤ A) :
    oddConstructionPrefix A (4 * A + 2) = (2 * A + 2) * (4 * A + 3) + (4 * A + 2) := by
  have hsub : A - 1 + 1 = A := Nat.sub_add_cancel (by omega)
  have htail : 4 * A - 2 + 2 = 4 * A := Nat.sub_add_cancel (by omega)
  have hprod : A * (A - 1) + A = A ^ 2 := by
    calc
      A * (A - 1) + A = A * ((A - 1) + 1) := by ring
      _ = A * A := by rw [hsub]
      _ = A ^ 2 := by ring
  unfold oddConstructionPrefix
  rw [oddConstructionGapWord_take_final_prefix A hA, List.sum_append, List.sum_append]
  rw [oddConstructionPreSecond_sum]
  rw [oddConstructionSecondPairs]
  rw [sum_flatMap_eq_sum_sums]
  rw [sum_map_const_on (List.range (A - 1))
    (fun j => (oddConstructionSecondPair A j).sum) (4 * A + 1)]
  · simp [List.length_range]
    ring_nf
    rw [← hprod]
    omega
  · intro j hj
    exact oddConstructionSecondPair_sum A j (List.mem_range.mp hj)

theorem oddConstructionPrefixResidueValue_actual_final (A : ℕ) (hA : 2 ≤ A) :
    oddConstructionPrefix A (4 * A + 2) % (4 * A + 3) =
      oddCorePrefixResidueValue A (4 * A + 2) := by
  rw [oddConstructionPrefix_final_value A hA]
  have hrem : 4 * A + 2 < 4 * A + 3 := by omega
  rw [mul_add_mod_eq (2 * A + 2) (4 * A + 2) (4 * A + 3) hrem]
  unfold oddCorePrefixResidueValue
  split_ifs <;> omega

theorem oddConstructionPrefixResidueValue_actual_second_block (A j : ℕ)
    (hA : 2 ≤ A) (hlo : 2 * A + 3 ≤ j) (hhi : j ≤ 4 * A + 1) :
    oddConstructionPrefix A j % (4 * A + 3) = oddCorePrefixResidueValue A j := by
  have hmBound : j - (2 * A + 3) ≤ 2 * (A - 1) := by omega
  by_cases hmEven : (j - (2 * A + 3)) % 2 = 0
  · let t := (j - (2 * A + 3)) / 2
    have hm : j - (2 * A + 3) = 2 * t := by dsimp [t]; omega
    have ht : t ≤ A - 1 := by dsimp [t]; omega
    have hprefix : oddConstructionPrefix A j =
        (A + 3 + t) * (4 * A + 3) + (2 * A + 2 - 2 * t) := by
      unfold oddConstructionPrefix
      rw [oddConstructionGapWord_take_second_block A j hlo hhi]
      rw [List.sum_append, oddConstructionPreSecond_sum]
      rw [hm, oddConstructionSecondPairs_take_complete_sum A t ht]
      ring_nf
      omega
    have hrem : 2 * A + 2 - 2 * t < 4 * A + 3 := by omega
    rw [hprefix, mul_add_mod_eq (A + 3 + t)
      (2 * A + 2 - 2 * t) (4 * A + 3) hrem]
    have hjOdd : j % 2 = 1 := by omega
    have hjne0 : j ≠ 0 := by omega
    have hjne1 : j ≠ 1 := by omega
    have hjhigh : ¬ j ≤ 2 * A + 1 := by omega
    have hjneMid : j ≠ 2 * A + 2 := by omega
    have htable : oddCorePrefixResidueValue A j = 2 * A + 2 - 2 * t := by
      by_cases hjle : j ≤ 4 * A
      · have hform : oddCorePrefixResidueValue A j = 4 * A + 5 - j := by
          simp [oddCorePrefixResidueValue, hjne0, hjne1, hjhigh,
            hjneMid, hjle, hjOdd]
        rw [hform]
        omega
      · have hjeq : j = 4 * A + 1 := by omega
        have hn0 : 4 * A + 1 ≠ 0 := by omega
        have hn1 : 4 * A + 1 ≠ 1 := by omega
        have hnlow : ¬ 4 * A + 1 ≤ 2 * A + 1 := by omega
        have hnmid : 4 * A + 1 ≠ 2 * A + 2 := by omega
        have hnupper : ¬ 4 * A + 1 ≤ 4 * A := by omega
        have hval : oddCorePrefixResidueValue A (4 * A + 1) = 4 := by
          unfold oddCorePrefixResidueValue
          simp only [if_neg hn0, if_neg hn1, if_neg hnlow, if_neg hnmid,
            if_neg hnupper, if_true]
        rw [hjeq, hval]
        omega
    rw [htable]
  · have hmOdd : (j - (2 * A + 3)) % 2 = 1 := by omega
    let t := (j - (2 * A + 3)) / 2
    have hm : j - (2 * A + 3) = 2 * t + 1 := by dsimp [t]; omega
    have ht : t < A - 1 := by dsimp [t]; omega
    have hprefix : oddConstructionPrefix A j =
        (A + 3 + t) * (4 * A + 3) + j := by
      unfold oddConstructionPrefix
      rw [oddConstructionGapWord_take_second_block A j hlo hhi]
      rw [List.sum_append, oddConstructionPreSecond_sum]
      rw [hm, oddConstructionSecondPairs_take_one_more_sum A t ht]
      ring_nf
      omega
    have hrem : j < 4 * A + 3 := by omega
    rw [hprefix, mul_add_mod_eq (A + 3 + t) j (4 * A + 3) hrem]
    have hjEven : j % 2 = 0 := by omega
    have hjle : j ≤ 4 * A := by omega
    have hjne0 : j ≠ 0 := by omega
    have hjne1 : j ≠ 1 := by omega
    have hjhigh : ¬ j ≤ 2 * A + 1 := by omega
    have hjneMid : j ≠ 2 * A + 2 := by omega
    have htable : oddCorePrefixResidueValue A j = j := by
      simp [oddCorePrefixResidueValue, hjne0, hjne1, hjhigh,
        hjneMid, hjle, hjEven]
    rw [htable]

theorem oddConstructionGapWord_take_before_middle (A j : ℕ)
    (hlo : 2 ≤ j) (hhi : j ≤ 2 * A + 2) :
    (oddConstructionGapWord A).take j =
      [4 * A + 5, 4 * A + 2] ++ (oddConstructionFirstPairs A).take (j - 2) := by
  simp only [oddConstructionGapWord, List.append_assoc]
  rw [List.take_append]
  have hstart : ([4 * A + 5, 4 * A + 2]).take j = [4 * A + 5, 4 * A + 2] :=
    List.take_of_length_le (by simp; omega)
  rw [hstart]
  simp only [List.length_cons, List.length_nil]
  have hfirst : j - 2 ≤ (oddConstructionFirstPairs A).length := by
    rw [oddConstructionFirstPairs_length]
    omega
  rw [List.take_append]
  have htail : (j - 2) - (oddConstructionFirstPairs A).length = 0 := by omega
  rw [htail]
  simp

theorem oddConstructionPrefix_zero (A : ℕ) : oddConstructionPrefix A 0 = 0 := by
  simp [oddConstructionPrefix]

theorem oddConstructionPrefix_one (A : ℕ) : oddConstructionPrefix A 1 = 4 * A + 5 := by
  simp [oddConstructionPrefix, oddConstructionGapWord]

theorem oddConstructionPrefixResidueValue_actual_first_block (A j : ℕ)
    (hA : 2 ≤ A) (hj : j ≤ 2 * A + 2) :
    oddConstructionPrefix A j % (4 * A + 3) = oddCorePrefixResidueValue A j := by
  by_cases hj0 : j = 0
  · subst j
    simp [oddConstructionPrefix_zero, oddCorePrefixResidueValue]
  · by_cases hj1 : j = 1
    · subst j
      rw [oddConstructionPrefix_one]
      have hdecomp : 4 * A + 5 = 1 * (4 * A + 3) + 2 := by omega
      rw [hdecomp]
      rw [mul_add_mod_eq 1 2 (4 * A + 3) (by omega)]
      simp [oddCorePrefixResidueValue]
    · have hlo : 2 ≤ j := by omega
      by_cases hmEven : (j - 2) % 2 = 0
      · let t := (j - 2) / 2
        have hm : j - 2 = 2 * t := by dsimp [t]; omega
        have ht : t ≤ A := by dsimp [t]; omega
        have hprefix : oddConstructionPrefix A j =
            (t + 2) * (4 * A + 3) + (2 * t + 1) := by
          unfold oddConstructionPrefix
          rw [oddConstructionGapWord_take_before_middle A j hlo hj]
          rw [List.sum_append]
          simp only [List.sum_cons, List.sum_nil]
          rw [hm, oddConstructionFirstPairs_take_complete_sum A t ht]
          ring
        have hrem : 2 * t + 1 < 4 * A + 3 := by omega
        rw [hprefix, mul_add_mod_eq (t + 2) (2 * t + 1)
          (4 * A + 3) hrem]
        have hjEven : j % 2 = 0 := by omega
        have htable : oddCorePrefixResidueValue A j = j - 1 := by
          by_cases hjle : j ≤ 2 * A + 1
          · simp [oddCorePrefixResidueValue, hj0, hj1, hjle, hjEven]
          · have hjeq : j = 2 * A + 2 := by omega
            simp [oddCorePrefixResidueValue, hjeq]
        have hremj : 2 * t + 1 = j - 1 := by omega
        rw [hremj, htable]
      · have hmOdd : (j - 2) % 2 = 1 := by omega
        let t := (j - 2) / 2
        have hm : j - 2 = 2 * t + 1 := by dsimp [t]; omega
        have ht : t < A := by dsimp [t]; omega
        have hprefix : oddConstructionPrefix A j =
            (t + 2) * (4 * A + 3) + (4 * A + 3 - 2 * t - 2) := by
          unfold oddConstructionPrefix
          rw [oddConstructionGapWord_take_before_middle A j hlo hj]
          rw [List.sum_append]
          simp only [List.sum_cons, List.sum_nil]
          rw [hm, oddConstructionFirstPairs_take_one_more_sum A t ht]
          have hgap : 4 * A + 3 - 3 - 4 * t = 4 * A - 4 * t := by omega
          rw [hgap]
          have hremSimpl : 4 * A + 3 - 2 * t - 2 = 4 * A + 1 - 2 * t := by omega
          rw [hremSimpl]
          ring_nf
          omega
        have hrem : 4 * A + 3 - 2 * t - 2 < 4 * A + 3 := by omega
        rw [hprefix, mul_add_mod_eq (t + 2)
          (4 * A + 3 - 2 * t - 2) (4 * A + 3) hrem]
        have hjOdd : j % 2 = 1 := by omega
        have hjle : j ≤ 2 * A + 1 := by omega
        have htable : oddCorePrefixResidueValue A j = 4 * A + 4 - j := by
          simp [oddCorePrefixResidueValue, hj0, hj1, hjle, hjOdd]
        have hremj : 4 * A + 3 - 2 * t - 2 = 4 * A + 4 - j := by omega
        rw [hremj, htable]

theorem oddConstructionSecondPairs_length (A : ℕ) :
    (oddConstructionSecondPairs A).length =
      2 * (A - 1) := by
  change ((List.range (A - 1)).flatMap (oddConstructionSecondPair A)).length =
    2 * (A - 1)
  rw [length_flatMap_eq_sum_lengths]
  rw [sum_map_const_on (List.range (A - 1))
    (fun j => (oddConstructionSecondPair A j).length) 2]
  · simp [List.length_range, Nat.mul_comm]
  · intro j hj
    simp [oddConstructionSecondPair]

theorem oddConstructionGapWord_length (A : ℕ) (hA : 2 ≤ A) :
    (oddConstructionGapWord A).length = 4 * A + 3 := by
  simp only [oddConstructionGapWord, List.length_append, List.length_cons, List.length_nil]
  rw [oddConstructionFirstPairs_length, oddConstructionSecondPairs_length]
  omega

theorem oddConstructionFirstPairs_sum (A : ℕ) :
    (oddConstructionFirstPairs A).sum = A * (4 * A + 5) := by
  change ((List.range A).flatMap (oddConstructionFirstPair A)).sum = A * (4 * A + 5)
  rw [sum_flatMap_eq_sum_sums]
  rw [sum_map_const_on (List.range A)
    (fun j => (oddConstructionFirstPair A j).sum) (4 * A + 5)]
  · simp [List.length_range]
  · intro j hj
    exact oddConstructionFirstPair_sum A j (List.mem_range.mp hj)

theorem oddConstructionSecondPairs_sum (A : ℕ) :
    (oddConstructionSecondPairs A).sum =
      (A - 1) * (4 * A + 1) := by
  change ((List.range (A - 1)).flatMap (oddConstructionSecondPair A)).sum =
    (A - 1) * (4 * A + 1)
  rw [sum_flatMap_eq_sum_sums]
  rw [sum_map_const_on (List.range (A - 1))
    (fun j => (oddConstructionSecondPair A j).sum) (4 * A + 1)]
  · simp [List.length_range]
  · intro j hj
    exact oddConstructionSecondPair_sum A j (List.mem_range.mp hj)

theorem oddConstructionGapWord_sum (A : ℕ) (hA : 2 ≤ A) :
    (oddConstructionGapWord A).sum = (2 * A + 3) * (4 * A + 3) := by
  have hsub : A - 1 + 1 = A := Nat.sub_add_cancel (by omega)
  have htail : 4 * A - 2 + 2 = 4 * A := Nat.sub_add_cancel (by omega)
  simp only [oddConstructionGapWord, List.sum_append, List.sum_cons, List.sum_nil]
  rw [oddConstructionFirstPairs_sum, oddConstructionSecondPairs_sum]
  nlinarith [hsub, htail]

theorem oddConstructionGapWord_positive (A : ℕ) (hA : 2 ≤ A) {x : ℕ}
    (hx : x ∈ oddConstructionGapWord A) : 0 < x := by
  simp [oddConstructionGapWord] at hx
  rcases hx with h | h | h | h | h | h | h
  · omega
  · omega
  · exact oddConstructionFirstPairs_positive A h
  · omega
  · exact oddConstructionSecondPairs_positive A h
  · omega
  · omega

theorem oddConstructionPrefixResidueValue_actual_all (A : ℕ) (hA : 2 ≤ A)
    (j : Fin (4 * A + 3)) :
    oddConstructionPrefix A j.val % (4 * A + 3) = oddCorePrefixResidueValue A j.val := by
  rcases j with ⟨j, hj⟩
  by_cases hfirst : j ≤ 2 * A + 2
  · exact oddConstructionPrefixResidueValue_actual_first_block A j hA hfirst
  · by_cases hsecond : j ≤ 4 * A + 1
    · exact oddConstructionPrefixResidueValue_actual_second_block A j hA (by omega) hsecond
    · have hlast : j = 4 * A + 2 := by omega
      subst j
      exact oddConstructionPrefixResidueValue_actual_final A hA

end CorralFormalization
