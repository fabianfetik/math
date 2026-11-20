import CorralFormalization.CorralRows

namespace CorralFormalization

theorem finiteCyclicGapInventory_singleton (W a : ℕ) :
    finiteCyclicGapInventory W {a} = Multiset.ofList [W] := by
  simp [finiteCyclicGapInventory, cyclicGaps, adjacentGaps]

/-- Since the wrap gap is at most the order, the first point of a bounded
row with gaps `[n]` lies strictly before `n`. -/
theorem gap_row_min_lt_order (W n : ℕ) (S : Finset ℕ) (hne : S.Nonempty)
    (hbound : ∀ x ∈ S, x < W)
    (hgap : finiteCyclicGapInventory W S = Multiset.ofList (fullGapList n)) :
    S.min' hne < n := by
  obtain ⟨c, cs, horder, hset⟩ := nonempty_finite_sites_have_ordered_list S hne
  have hn : (c :: cs).Nodup := horder.imp (by intro a b hab; omega)
  have hsort : S.sort (· ≤ ·) = c :: cs := by
    rw [← hset]
    exact (List.toFinset_sort (· ≤ ·) hn).2 (horder.imp (by intro a b hab; omega))
  obtain ⟨_, hmin, _⟩ := ordered_list_extrema c cs horder
  have hmin' : S.min' hne = c := by simpa [hset] using hmin
  have hlast : (c :: cs).getLast (by simp) < W := by
    apply hbound
    rw [← hset]
    exact List.mem_toFinset.mpr (List.getLast_mem (by simp))
  have hwrap : c + W - (c :: cs).getLast (by simp) ∈
      finiteCyclicGapInventory W S := by
    simp [finiteCyclicGapInventory, hsort, cyclicGaps]
  rw [hgap] at hwrap
  have hle := ((fullGapList_mem n _).1 (Multiset.mem_coe.mp hwrap)).2
  rw [hmin']
  omega

/-- Preserve all old representatives and insert one point just beyond the
old clock, aligned with this row's least point. -/
def extendRowSites (n : ℕ) (S : Finset ℕ) (hne : S.Nonempty) : Finset ℕ :=
  S ∪ {width n + S.min' hne}

theorem extendRowSites_gaps (n : ℕ) (S : Finset ℕ) (hne : S.Nonempty)
    (hbound : ∀ x ∈ S, x < width n)
    (hgap : finiteCyclicGapInventory (width n) S = Multiset.ofList (fullGapList n)) :
    finiteCyclicGapInventory (width (n + 1)) (extendRowSites n S hne) =
      Multiset.ofList (fullGapList (n + 1)) := by
  let a := S.min' hne
  have ha : a < n + 1 := by
    have := gap_row_min_lt_order (width n) n S hne hbound hgap
    dsimp [a]
    omega
  have hsingle : ({a} : Finset ℕ).Nonempty := by simp
  have hD : ∀ x ∈ ({a} : Finset ℕ), x < n + 1 := by
    intro x hx
    have hx' := Finset.mem_singleton.mp hx
    subst x
    exact ha
  have hheads : S.min' hne = ({a} : Finset ℕ).min' hsingle := by simp [a]
  have hjoin := finite_set_cyclic_gap_join (width n) (n + 1) S {a} hne hsingle
    hbound hD (Or.inl hheads)
  rw [width_succ]
  change finiteCyclicGapInventory (width n + (n + 1)) (S ∪ {width n + a}) = _
  simpa [hgap, finiteCyclicGapInventory_singleton, fullGapList_succ,
    ← Multiset.coe_add] using hjoin

/-- General order extension on disjoint row families. Full occupancy is
neither assumed nor preserved. -/
def CorralRows.extend {h n : ℕ} (R : CorralRows h n) : CorralRows h (n + 1) where
  sites i := extendRowSites n (R.sites i) (R.nonempty i)
  nonempty i := by
    obtain ⟨x, hx⟩ := R.nonempty i
    exact ⟨x, Finset.mem_union.mpr (Or.inl hx)⟩
  bounded i x hx := by
    rw [width_succ]
    rcases Finset.mem_union.mp hx with hold | hnew
    · have := R.bounded i x hold
      omega
    · have hx' := Finset.mem_singleton.mp hnew
      have ha := gap_row_min_lt_order (width n) n (R.sites i) (R.nonempty i)
        (R.bounded i) (R.gaps i)
      omega
  disjoint i j hij := by
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    rcases Finset.mem_union.mp hxi with hi | hi <;>
      rcases Finset.mem_union.mp hxj with hj | hj
    · exact Finset.disjoint_left.mp (R.disjoint i j hij) hi hj
    · have hxb := R.bounded i x hi
      have hxeq := Finset.mem_singleton.mp hj
      omega
    · have hxb := R.bounded j x hj
      have hxeq := Finset.mem_singleton.mp hi
      omega
    · have hxi' := Finset.mem_singleton.mp hi
      have hxj' := Finset.mem_singleton.mp hj
      have heq : (R.sites i).min' (R.nonempty i) = (R.sites j).min' (R.nonempty j) := by omega
      have hmi := Finset.min'_mem (R.sites i) (R.nonempty i)
      have hmj := Finset.min'_mem (R.sites j) (R.nonempty j)
      rw [← heq] at hmj
      exact Finset.disjoint_left.mp (R.disjoint i j hij) hmi hmj
  gaps i := extendRowSites_gaps n (R.sites i) (R.nonempty i) (R.bounded i) (R.gaps i)

/-- Any positive-order original corral extends to the next order at the
same height, with no extra geometric assumption on its source. -/
theorem originalCorral_succ_order (h n : ℕ) (hh : 0 < h) (hn : 0 < n)
    (hc : OriginalCorral h n) : OriginalCorral h (n + 1) := by
  obtain ⟨R⟩ := originalCorral_nonempty_rows hn hc
  exact R.extend.original hh

theorem originalCorral_add_order (h n : ℕ) (hh : 0 < h) (hn : 0 < n)
    (hc : OriginalCorral h n) (d : ℕ) : OriginalCorral h (n + d) := by
  induction d with
  | zero => simpa using hc
  | succ d ih =>
    have hnext := originalCorral_succ_order h (n + d) hh (by omega) ih
    simpa [Nat.add_assoc] using hnext

theorem originalCorral_mono_order (h n m : ℕ) (hh : 0 < h) (hn : 0 < n)
    (hc : OriginalCorral h n) (hnm : n ≤ m) : OriginalCorral h m := by
  have hresult := originalCorral_add_order h n hh hn hc (m - n)
  simpa [Nat.add_sub_of_le hnm] using hresult

end CorralFormalization
