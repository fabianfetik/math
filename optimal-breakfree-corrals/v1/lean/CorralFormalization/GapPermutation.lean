import CorralFormalization.PositiveGapWord

namespace CorralFormalization

/-- The ordinary ordered list of the permitted gap lengths. -/
def fullGapList (n : ℕ) : List ℕ := (List.range n).map (fun j => j + 1)

theorem fullGapList_nodup (n : ℕ) : (fullGapList n).Nodup := by
  apply List.Nodup.map
  · intro i j hij
    dsimp at hij
    omega
  · exact List.nodup_range

theorem fullGapList_mem (n x : ℕ) : x ∈ fullGapList n ↔ 0 < x ∧ x ≤ n := by
  simp only [fullGapList, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨hx0, hxn⟩
    exact ⟨x - 1, by omega, by omega⟩

/-- View an entry of an actual gap list as a zero-based element of `Fin n`. -/
def gapListFin {n : ℕ} (g : List ℕ) (hlen : g.length = n)
    (hrange : ∀ x ∈ g, 0 < x ∧ x ≤ n) (j : Fin n) : Fin n :=
  ⟨g[j.val]'(by rw [hlen]; exact j.isLt) - 1, by
    have hm := hrange _ (List.getElem_mem (by rw [hlen]; exact j.isLt))
    omega⟩

theorem gapListFin_value {n : ℕ} (g : List ℕ) (hlen : g.length = n)
    (hrange : ∀ x ∈ g, 0 < x ∧ x ≤ n) (j : Fin n) :
    (gapListFin g hlen hrange j).val + 1 = g[j.val]'(by rw [hlen]; exact j.isLt) := by
  have hm := hrange _ (List.getElem_mem (by rw [hlen]; exact j.isLt))
  dsimp [gapListFin]
  omega

theorem gapListFin_injective {n : ℕ} (g : List ℕ) (hlen : g.length = n)
    (hrange : ∀ x ∈ g, 0 < x ∧ x ≤ n) (hnodup : g.Nodup) :
    Function.Injective (gapListFin g hlen hrange) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  have hi := gapListFin_value g hlen hrange i
  have hj := gapListFin_value g hlen hrange j
  have hget : g.get ⟨i.val, by rw [hlen]; exact i.isLt⟩ =
      g.get ⟨j.val, by rw [hlen]; exact j.isLt⟩ := by
    change g[i.val]'_ = g[j.val]'_
    omega
  have hindex := (List.nodup_iff_injective_get.mp hnodup) hget
  have hval : i.val = j.val := congrArg (fun k : Fin g.length => k.val) hindex
  exact Fin.ext hval

/-- The gap list, viewed as the permutation required by the original
corral definition. -/
noncomputable def gapListPerm {n : ℕ} (g : List ℕ) (hlen : g.length = n)
    (hrange : ∀ x ∈ g, 0 < x ∧ x ≤ n) (hnodup : g.Nodup) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (gapListFin g hlen hrange)
    ⟨gapListFin_injective g hlen hrange hnodup,
      (Finite.injective_iff_surjective).1 (gapListFin_injective g hlen hrange hnodup)⟩

theorem gapListPerm_value {n : ℕ} (g : List ℕ) (hlen : g.length = n)
    (hrange : ∀ x ∈ g, 0 < x ∧ x ≤ n) (hnodup : g.Nodup) (j : Fin n) :
    (gapListPerm g hlen hrange hnodup j).val + 1 = g.getD j.val 0 := by
  rw [List.getD_eq_getElem g 0 (by rw [hlen]; exact j.isLt)]
  exact gapListFin_value g hlen hrange j

/-- A prefix list sum is the corresponding range sum of indexed entries. -/
theorem sum_range_getD_eq_take (g : List ℕ) (k : ℕ) (hk : k ≤ g.length) :
    (∑ i ∈ Finset.range k, g.getD i 0) = (g.take k).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, List.sum_take_succ g k (by omega), ih (by omega)]
    rw [List.getD_eq_getElem g 0 (by omega)]

/-- The original finite-sum definition agrees with the actual prefix sum of
the chosen gap list through position `j+1`. -/
theorem gapListPerm_partialSum {n : ℕ} (g : List ℕ) (hlen : g.length = n)
    (hrange : ∀ x ∈ g, 0 < x ∧ x ≤ n) (hnodup : g.Nodup) (j : Fin n) :
    partialSum (gapListPerm g hlen hrange hnodup) j = (g.take (j.val + 1)).sum := by
  unfold partialSum
  simp_rw [gapListPerm_value]
  let f : ℕ → ℕ := fun k => if k ≤ j.val then g.getD k 0 else 0
  change (∑ k : Fin n, f k.val) = (g.take (j.val + 1)).sum
  rw [Fin.sum_univ_eq_sum_range f n]
  have hsubset : Finset.range (j.val + 1) ⊆ Finset.range n := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hzero : ∀ k ∈ Finset.range n, k ∉ Finset.range (j.val + 1) → f k = 0 := by
    intro k hk hnot
    have hk : j.val < k := by simp only [Finset.mem_range] at hnot; omega
    simp [f, Nat.not_le.mpr hk]
  rw [← Finset.sum_subset hsubset hzero]
  have heq : (∑ k ∈ Finset.range (j.val + 1), f k) =
      ∑ k ∈ Finset.range (j.val + 1), g.getD k 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ j.val := by simp only [Finset.mem_range] at hk; omega
    simp [f, hk']
  rw [heq, sum_range_getD_eq_take g (j.val + 1) (by rw [hlen]; omega)]

end CorralFormalization
