import CorralFormalization.GapPermutation
import CorralFormalization.ListTools
import CorralFormalization.Arithmetic

namespace CorralFormalization

/-- The descending odd and even blocks in the paper's even-height word. -/
def evenConstructionLowList (k : ℕ) : List ℕ :=
  (List.range k).map (fun j => 2 * k - 1 - 2 * j) ++
    (List.range (k - 1)).map (fun j => 2 * k - 2 - 2 * j)

/-- Equation (2), including its final central gap. -/
def evenConstructionGapWord (k : ℕ) : List ℕ :=
  (evenConstructionLowList k).flatMap (fun a => [a, 4 * k - a]) ++ [2 * k]

theorem evenConstructionLowList_length (k : ℕ) (hk : 1 ≤ k) :
    (evenConstructionLowList k).length = 2 * k - 1 := by
  simp [evenConstructionLowList]
  omega

theorem evenConstructionLowList_nodup (k : ℕ) (hk : 1 ≤ k) :
    (evenConstructionLowList k).Nodup := by
  unfold evenConstructionLowList
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply List.Nodup.map_on _ List.nodup_range
    intro i hi j hj hij
    simp only [List.mem_range] at hi hj
    omega
  · apply List.Nodup.map_on _ List.nodup_range
    intro i hi j hj hij
    simp only [List.mem_range] at hi hj
    omega
  · intro x hx y hy heq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    simp only [List.mem_range] at hi hj
    omega

theorem evenConstructionLowList_mem (k x : ℕ) (hk : 1 ≤ k) :
    x ∈ evenConstructionLowList k ↔ 0 < x ∧ x < 2 * k := by
  simp only [evenConstructionLowList, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  · rintro ⟨hxpos, hxhi⟩
    by_cases hodd : x % 2 = 1
    · left
      refine ⟨(2 * k - 1 - x) / 2, ?_, ?_⟩ <;> omega
    · right
      refine ⟨(2 * k - 2 - x) / 2, ?_, ?_⟩ <;> omega

/-- The actual low list is a permutation of `1,...,2k-1`. -/
theorem evenConstructionLowList_perm (k : ℕ) (hk : 1 ≤ k) :
    (evenConstructionLowList k).Perm (fullGapList (2 * k - 1)) := by
  apply (List.perm_ext_iff_of_nodup (evenConstructionLowList_nodup k hk)
    (fullGapList_nodup (2 * k - 1))).2
  intro x
  rw [evenConstructionLowList_mem k x hk, fullGapList_mem]
  omega

/-- Separate the actual paired word into the low values and their
complements, followed by the central value. -/
theorem evenConstructionGapWord_perm_split (k : ℕ) :
    (evenConstructionGapWord k).Perm
      (evenConstructionLowList k ++ (evenConstructionLowList k).map (fun a => 4 * k - a) ++ [2 * k]) := by
  unfold evenConstructionGapWord
  have hp := interleave_perm (evenConstructionLowList k) id (fun a => 4 * k - a)
  simpa using hp.append_right [2 * k]

/-- The complementary half has no repetitions. -/
theorem evenConstructionComplement_nodup (k : ℕ) (hk : 1 ≤ k) :
    ((evenConstructionLowList k).map (fun a => 4 * k - a)).Nodup := by
  apply List.Nodup.map_on _ (evenConstructionLowList_nodup k hk)
  intro x hx y hy hxy
  have hx' := (evenConstructionLowList_mem k x hk).1 hx
  have hy' := (evenConstructionLowList_mem k y hk).1 hy
  omega

theorem evenConstructionComplement_mem (k x : ℕ) (hk : 1 ≤ k) :
    x ∈ (evenConstructionLowList k).map (fun a => 4 * k - a) ↔
      2 * k < x ∧ x < 4 * k := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' := (evenConstructionLowList_mem k a hk).1 ha
    omega
  · rintro ⟨hxlo, hxhi⟩
    refine ⟨4 * k - x, (evenConstructionLowList_mem k _ hk).2 (by omega), ?_⟩
    omega

/-- The split word contains no duplicates, across its three ranges. -/
theorem evenConstructionSplit_nodup (k : ℕ) (hk : 1 ≤ k) :
    (evenConstructionLowList k ++ (evenConstructionLowList k).map (fun a => 4 * k - a) ++ [2 * k]).Nodup := by
  rw [List.nodup_append]
  refine ⟨?_, by simp, ?_⟩
  · rw [List.nodup_append]
    refine ⟨evenConstructionLowList_nodup k hk, evenConstructionComplement_nodup k hk, ?_⟩
    intro x hx y hy heq
    have hx' := (evenConstructionLowList_mem k x hk).1 hx
    have hy' := (evenConstructionComplement_mem k y hk).1 hy
    omega
  · intro x hx y hy heq
    simp only [List.mem_singleton] at hy
    subst y
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · have := (evenConstructionLowList_mem k x hk).1 hx
      omega
    · have := (evenConstructionComplement_mem k x hk).1 hx
      omega

/-- The actual word is exactly a permutation of the full optimal gap
inventory, including multiplicities. -/
theorem evenConstructionGapWord_perm_full (k : ℕ) (hk : 1 ≤ k) :
    (evenConstructionGapWord k).Perm (fullGapList (4 * k - 1)) := by
  apply (evenConstructionGapWord_perm_split k).trans
  apply (List.perm_ext_iff_of_nodup (evenConstructionSplit_nodup k hk)
    (fullGapList_nodup (4 * k - 1))).2
  intro x
  simp only [List.mem_append, List.mem_singleton,
    evenConstructionLowList_mem k x hk, evenConstructionComplement_mem k x hk, fullGapList_mem]
  omega

theorem evenConstructionGapWord_length (k : ℕ) (hk : 1 ≤ k) :
    (evenConstructionGapWord k).length = 4 * k - 1 := by
  have hp := (evenConstructionGapWord_perm_full k hk).length_eq
  simpa [fullGapList] using hp

theorem evenConstructionGapWord_positive (k : ℕ) (hk : 1 ≤ k)
    (x : ℕ) (hx : x ∈ evenConstructionGapWord k) : 0 < x := by
  exact ((fullGapList_mem (4 * k - 1) x).1
    ((evenConstructionGapWord_perm_full k hk).mem_iff.mp hx)).1

/-- Every pair in the actual word sums to `4k`; its total is `2k(4k-1)`. -/
theorem evenConstructionGapWord_sum (k : ℕ) (hk : 1 ≤ k) :
    (evenConstructionGapWord k).sum = 2 * k * (4 * k - 1) := by
  unfold evenConstructionGapWord
  rw [List.sum_append, sum_flatMap_eq_sum_sums]
  have hpairs : ((evenConstructionLowList k).map (fun a => ([a, 4 * k - a] : List ℕ).sum)).sum =
      (2 * k - 1) * (4 * k) := by
    rw [sum_map_const_on (evenConstructionLowList k)
      (fun a => ([a, 4 * k - a] : List ℕ).sum) (4 * k)]
    · rw [evenConstructionLowList_length k hk]
    · intro a ha
      have := (evenConstructionLowList_mem k a hk).1 ha
      simp only [List.sum_cons, List.sum_nil, add_zero]
      omega
  rw [hpairs]
  simp only [List.sum_cons, List.sum_nil, add_zero]
  have hs : 4 * k - 1 + 1 = 4 * k := by omega
  have hl : 2 * k - 1 + 1 = 2 * k := by omega
  have hleft : (2 * k - 1) * (4 * k) + 4 * k = (2 * k) * (4 * k) := by
    calc
      _ = (2 * k - 1 + 1) * (4 * k) := by ring
      _ = (2 * k) * (4 * k) := by rw [hl]
  have hright : (2 * k) * (4 * k - 1) + 2 * k = (2 * k) * (4 * k) := by
    calc
      _ = (2 * k) * (4 * k - 1 + 1) := by ring
      _ = (2 * k) * (4 * k) := by rw [hs]
  omega

end CorralFormalization
