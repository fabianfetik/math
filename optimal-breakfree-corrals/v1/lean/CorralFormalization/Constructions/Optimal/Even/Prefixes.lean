import CorralFormalization.Constructions.Optimal.Even.Word

namespace CorralFormalization

/-- The paper's piecewise indexed low gap `a_j`. -/
def evenConstructionLowAt (k j : ℕ) : ℕ :=
  if j < k then 2 * k - 1 - 2 * j else 4 * k - 2 - 2 * j

theorem evenConstructionLowList_get (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 * k - 1) :
    (evenConstructionLowList k).getD j 0 = evenConstructionLowAt k j := by
  unfold evenConstructionLowList evenConstructionLowAt
  by_cases hjk : j < k
  · simp only [if_pos hjk]
    rw [List.getD_append _ _ 0 j (by simpa using hjk)]
    rw [List.getD_eq_getElem _ 0 (by simpa using hjk), List.getElem_map]
    simp
  · simp only [if_neg hjk]
    rw [List.getD_append_right _ _ 0 j (by simp; omega)]
    simp only [List.length_map, List.length_range]
    rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_map]
    simp only [List.getElem_range]
    omega

/-- The two explicitly ordered blocks have the printed indexed values. -/
theorem evenConstructionLowList_eq_indexed (k : ℕ) (hk : 1 ≤ k) :
    evenConstructionLowList k = (List.range (2 * k - 1)).map (evenConstructionLowAt k) := by
  apply List.ext_getElem
  · simp [evenConstructionLowList_length k hk]
  · intro j hj hmap
    have hj' : j < 2 * k - 1 := by
      simpa [evenConstructionLowList_length k hk] using hj
    have hget := evenConstructionLowList_get k j hk hj'
    rw [List.getD_eq_getElem _ 0 hj] at hget
    simpa using hget

def evenConstructionPair (k j : ℕ) : List ℕ :=
  [evenConstructionLowAt k j, 4 * k - evenConstructionLowAt k j]

def evenConstructionPairs (k : ℕ) : List ℕ :=
  (List.range (2 * k - 1)).flatMap (evenConstructionPair k)

def evenConstructionPrefix (k j : ℕ) : ℕ := ((evenConstructionGapWord k).take j).sum

theorem evenConstructionGapWord_eq_indexed (k : ℕ) (hk : 1 ≤ k) :
    evenConstructionGapWord k = evenConstructionPairs k ++ [2 * k] := by
  unfold evenConstructionGapWord evenConstructionPairs
  rw [evenConstructionLowList_eq_indexed k hk, List.flatMap_map]
  rfl

theorem evenConstructionPair_sum (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 * k - 1) :
    (evenConstructionPair k j).sum = 4 * k := by
  unfold evenConstructionPair evenConstructionLowAt
  split_ifs <;> simp only [List.sum_cons, List.sum_nil, add_zero] <;> omega

theorem evenConstructionPairs_upto_length (k t : ℕ) :
    ((List.range t).flatMap (evenConstructionPair k)).length = 2 * t := by
  rw [length_flatMap_eq_sum_lengths]
  rw [sum_map_const_on (List.range t) (fun j => (evenConstructionPair k j).length) 2]
  · simp [List.length_range, Nat.mul_comm]
  · intro j hj
    simp [evenConstructionPair]

theorem evenConstructionPairs_length (k : ℕ) :
    (evenConstructionPairs k).length = 2 * (2 * k - 1) := by
  exact evenConstructionPairs_upto_length k (2 * k - 1)

theorem evenConstructionPairs_take_complete (k t : ℕ) (ht : t ≤ 2 * k - 1) :
    (evenConstructionPairs k).take (2 * t) = (List.range t).flatMap (evenConstructionPair k) := by
  have hsplit : List.range (2 * k - 1) =
      List.range t ++ List.map (fun x => t + x) (List.range (2 * k - 1 - t)) := by
    calc
      List.range (2 * k - 1) = List.range (t + (2 * k - 1 - t)) := by congr 1; omega
      _ = _ := by rw [List.range_add]
  change ((List.range (2 * k - 1)).flatMap (evenConstructionPair k)).take (2 * t) = _
  rw [hsplit, List.flatMap_append]
  have hlen := evenConstructionPairs_upto_length k t
  rw [List.take_append_of_le_length (by rw [hlen])]
  rw [← hlen, List.take_length]

theorem evenConstructionPairs_upto_sum (k t : ℕ) (hk : 1 ≤ k) (ht : t ≤ 2 * k - 1) :
    ((List.range t).flatMap (evenConstructionPair k)).sum = t * (4 * k) := by
  rw [sum_flatMap_eq_sum_sums]
  rw [sum_map_const_on (List.range t) (fun j => (evenConstructionPair k j).sum) (4 * k)]
  · simp
  · intro j hj
    exact evenConstructionPair_sum k j hk (by have := List.mem_range.mp hj; omega)

theorem evenConstructionPairs_take_one_more (k t : ℕ) (ht : t < 2 * k - 1) :
    (evenConstructionPairs k).take (2 * t + 1) =
      (List.range t).flatMap (evenConstructionPair k) ++ [evenConstructionLowAt k t] := by
  have hsplit : List.range (2 * k - 1) =
      List.range (t + 1) ++
        List.map (fun x => t + 1 + x) (List.range (2 * k - 1 - (t + 1))) := by
    calc
      List.range (2 * k - 1) = List.range ((t + 1) + (2 * k - 1 - (t + 1))) := by
        congr 1
        omega
      _ = _ := by rw [List.range_add]
  have hdecomp : evenConstructionPairs k =
      (List.range t).flatMap (evenConstructionPair k) ++
        (evenConstructionPair k t ++
          ((List.map (fun x => t + 1 + x) (List.range (2 * k - 1 - (t + 1)))).flatMap
            (evenConstructionPair k))) := by
    change (List.range (2 * k - 1)).flatMap (evenConstructionPair k) = _
    rw [hsplit, List.flatMap_append, List.range_succ, List.flatMap_append]
    simp [List.flatMap]
  rw [hdecomp, List.take_append]
  have hlen := evenConstructionPairs_upto_length k t
  have htake : ((List.range t).flatMap (evenConstructionPair k)).take (2 * t + 1) =
      (List.range t).flatMap (evenConstructionPair k) := List.take_of_length_le (by rw [hlen]; omega)
  rw [htake]
  have hdiff : 2 * t + 1 - ((List.range t).flatMap (evenConstructionPair k)).length = 1 := by
    rw [hlen]
    omega
  rw [hdiff, List.take_append_of_le_length]
  · simp [evenConstructionPair]
  · simp [evenConstructionPair]

/-- Every complete pair contributes `4k` to an actual proper prefix. -/
theorem evenConstructionPrefix_even (k t : ℕ) (hk : 1 ≤ k) (ht : t ≤ 2 * k - 1) :
    evenConstructionPrefix k (2 * t) = t * (4 * k) := by
  unfold evenConstructionPrefix
  rw [evenConstructionGapWord_eq_indexed k hk]
  rw [List.take_append_of_le_length (by rw [evenConstructionPairs_length]; omega)]
  rw [evenConstructionPairs_take_complete k t ht]
  exact evenConstructionPairs_upto_sum k t hk ht

/-- The intermediate proper prefix in each pair adds the printed `a_t`. -/
theorem evenConstructionPrefix_odd (k t : ℕ) (hk : 1 ≤ k) (ht : t < 2 * k - 1) :
    evenConstructionPrefix k (2 * t + 1) = t * (4 * k) + evenConstructionLowAt k t := by
  unfold evenConstructionPrefix
  rw [evenConstructionGapWord_eq_indexed k hk]
  rw [List.take_append_of_le_length (by rw [evenConstructionPairs_length]; omega)]
  rw [evenConstructionPairs_take_one_more k t ht]
  simp [evenConstructionPairs_upto_sum k t hk (by omega)]

end CorralFormalization
