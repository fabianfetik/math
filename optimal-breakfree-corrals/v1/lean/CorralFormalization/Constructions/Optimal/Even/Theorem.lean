import CorralFormalization.Constructions.Optimal.Even.Partition

namespace CorralFormalization

theorem evenConstructionWidth_eq (k : ℕ) (hk : 1 ≤ k) :
    width (4 * k - 1) = evenConstructionClock k := by
  unfold width evenConstructionClock
  have hs : 4 * k - 1 + 1 = 4 * k := by omega
  rw [hs, evenConstructionPeriod_eq k hk]
  have hprod : (4 * k - 1) * (4 * k) = (k * (2 * (4 * k - 1))) * 2 := by ring
  rw [hprod]
  simp

theorem evenConstructionRowSource_nonempty (k : ℕ) (hk : 1 ≤ k) (b : Fin 2) :
    (evenConstructionRowSource k b).Nonempty := by
  fin_cases b
  · simpa [evenConstructionRowSource] using evenConstructionRawPrefixSet_nonempty k hk
  · simpa [evenConstructionRowSource] using evenConstructionReflectedSet_nonempty k hk

theorem evenConstructionRowSource_bound (k : ℕ) (hk : 1 ≤ k) (b : Fin 2)
    (q : ℕ) (hq : q ∈ evenConstructionRowSource k b) : q < evenConstructionClock k := by
  fin_cases b
  · exact evenConstructionRawPrefixSet_clock_bound k q hk (by simpa [evenConstructionRowSource] using hq)
  · exact evenConstructionReflectedSet_bound k q hk (by simpa [evenConstructionRowSource] using hq)

theorem evenConstructionRowSource_gaps (k : ℕ) (hk : 1 ≤ k) (b : Fin 2) :
    finiteCyclicGapInventory (evenConstructionClock k) (evenConstructionRowSource k b) =
      Multiset.ofList (fullGapList (4 * k - 1)) := by
  have hperm : Multiset.ofList (evenConstructionGapWord k) =
      Multiset.ofList (fullGapList (4 * k - 1)) :=
    Multiset.coe_eq_coe.mpr (evenConstructionGapWord_perm_full k hk)
  fin_cases b
  · simpa [evenConstructionRowSource, evenConstructionRawPrefixSet_gaps k hk] using hperm
  · simpa [evenConstructionRowSource, evenConstructionReflectedSet_gaps k hk] using hperm

/-- Index the paper's two families of `k` rows by the original `Fin (2k)`. -/
def evenConstructionRows (k : ℕ) (i : Fin (2 * k)) : Finset ℕ :=
  let bs := (finProdFinEquiv (m := 2) (n := k)).symm i
  evenConstructionRowPair k bs.1 bs.2

theorem evenConstructionRows_nonempty (k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * k)) :
    (evenConstructionRows k i).Nonempty := by
  let bs := (finProdFinEquiv (m := 2) (n := k)).symm i
  obtain ⟨q, hq⟩ := evenConstructionRowSource_nonempty k hk bs.1
  exact ⟨_, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩

theorem evenConstructionRows_bound (k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * k))
    (x : ℕ) (hx : x ∈ evenConstructionRows k i) : x < evenConstructionClock k := by
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hx
  exact Nat.mod_lt _ (evenConstructionClock_pos k hk)

theorem evenConstructionRows_partition (k : ℕ) (hk : 1 ≤ k) (x : ℕ)
    (hx : x < evenConstructionClock k) :
    ∃! i : Fin (2 * k), x ∈ evenConstructionRows k i := by
  obtain ⟨bs, hbs, huniq⟩ := evenConstructionRowPair_partition k hk x hx
  let e := finProdFinEquiv (m := 2) (n := k)
  refine ⟨e bs, ?_, ?_⟩
  · simpa [evenConstructionRows, e] using hbs
  · intro i hi
    have hpair : x ∈ evenConstructionRowPair k (e.symm i).1 (e.symm i).2 := by
      simpa [evenConstructionRows, e] using hi
    have heq := huniq (e.symm i) hpair
    apply e.symm.injective
    simpa using heq

theorem evenConstructionRows_gaps (k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * k)) :
    finiteCyclicGapInventory (evenConstructionClock k) (evenConstructionRows k i) =
      Multiset.ofList (fullGapList (4 * k - 1)) := by
  let bs := (finProdFinEquiv (m := 2) (n := k)).symm i
  change finiteCyclicGapInventory (evenConstructionClock k)
    ((evenConstructionRowSource k bs.1).image
      (fun q => (q + evenConstructionPeriod k * bs.2.val) % evenConstructionClock k)) = _
  rw [finite_set_cyclic_gap_rotate _ _ _ (evenConstructionClock_pos k hk)
    (evenConstructionRowSource_bound k hk bs.1)]
  exact evenConstructionRowSource_gaps k hk bs.1

namespace OptimalEven

/-- The actual even construction supplies the original permutations and
shifts for every positive even height `2k`. -/
theorem exists_corral (k : ℕ) (hk : 1 ≤ k) :
    OriginalCorral (2 * k) (4 * k - 1) := by
  apply originalCorral_of_gap_rows (2 * k) (4 * k - 1) (by omega) (evenConstructionRows k)
  · exact evenConstructionRows_nonempty k hk
  · intro i x hx
    rw [evenConstructionWidth_eq k hk]
    exact evenConstructionRows_bound k hk i x hx
  · intro x hx
    rw [evenConstructionWidth_eq k hk] at hx
    exact evenConstructionRows_partition k hk x hx
  · intro i
    rw [evenConstructionWidth_eq k hk]
    exact evenConstructionRows_gaps k hk i

end OptimalEven

end CorralFormalization
