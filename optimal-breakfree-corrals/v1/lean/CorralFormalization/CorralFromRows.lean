import CorralFormalization.GapWitness

namespace CorralFormalization

/-- A nonempty bounded row with the complete gap inventory yields an actual
permutation and integer shift in the original corral predicate. The returned
partial-sum arrivals lie in that same row and are individually injective. -/
theorem gapRow_original_witness (n : ℕ) (S : Finset ℕ)
    (hne : S.Nonempty) (hbound : ∀ x ∈ S, x < width n)
    (hgap : finiteCyclicGapInventory (width n) S = Multiset.ofList (fullGapList n)) :
    ∃ (ρ : Equiv.Perm (Fin n)) (τ : ℤ),
      (∀ j : Fin n, ((τ : ZMod (width n)) + (partialSum ρ j : ZMod (width n))).val ∈ S) ∧
      Function.Injective (fun j : Fin n =>
        (τ : ZMod (width n)) + (partialSum ρ j : ZMod (width n))) := by
  obtain ⟨c, cs, horder, hset⟩ := nonempty_finite_sites_have_ordered_list S hne
  have hn : (c :: cs).Nodup := horder.imp (by intro a b hab; omega)
  have hsort : S.sort (· ≤ ·) = c :: cs := by
    rw [← hset]
    exact (List.toFinset_sort (· ≤ ·) hn).2 (horder.imp (by intro a b hab; omega))
  have horder' : (c :: cs).Pairwise (· ≤ ·) :=
    horder.imp (by intro a b hab; omega)
  have hbound' : ∀ x ∈ c :: cs, x < width n := by
    intro x hx
    apply hbound x
    rw [← hset]
    exact List.mem_toFinset.mpr hx
  have hW : 0 < width n := by
    have hc := hbound' c (by simp)
    omega
  letI : NeZero (width n) := ⟨by omega⟩
  let g := cyclicGaps (width n) c cs
  have hg : Multiset.ofList g = Multiset.ofList (fullGapList n) := by
    simpa [finiteCyclicGapInventory, hsort, g] using hgap
  have hperm : g.Perm (fullGapList n) := Multiset.coe_eq_coe.mp hg
  have hlen : g.length = n := by
    have hl := hperm.length_eq
    simpa [fullGapList] using hl
  have hrange : ∀ x ∈ g, 0 < x ∧ x ≤ n := by
    intro x hx
    exact (fullGapList_mem n x).1 (hperm.mem_iff.mp hx)
  have hnodup : g.Nodup := hperm.nodup_iff.mpr (fullGapList_nodup n)
  have hpos : ∀ x ∈ g, 0 < x := by
    intro x hx
    exact (hrange x hx).1
  let ρ := gapListPerm g hlen hrange hnodup
  have hval (j : Fin n) :
      ((c : ZMod (width n)) + (partialSum ρ j : ZMod (width n))).val =
        gapArrival (width n) c g j := by
    rw [ZMod.val_add, ZMod.val_natCast, ZMod.val_natCast]
    rw [gapListPerm_partialSum g hlen hrange hnodup]
    exact (Nat.add_mod c (g.take (j.val + 1)).sum (width n)).symm
  refine ⟨ρ, (c : ℤ), ?_, ?_⟩
  · intro j
    simp only [Int.cast_natCast]
    rw [hval]
    have hin := gapArrival_mem_sites (width n) c cs hW horder' hbound' hlen j
    rw [← hset]
    exact List.mem_toFinset.mpr hin
  · intro j k hjk
    apply gapArrival_injective (width n) c cs horder' hbound' hlen hpos
    have heq := congrArg ZMod.val hjk
    simp only [Int.cast_natCast] at heq
    rw [hval, hval] at heq
    exact heq

/-- Pairwise disjoint bounded rows with the complete gap inventory construct
the original permutations and shifts; unused clock positions are allowed. -/
theorem originalCorral_of_disjoint_gap_rows (h n : ℕ) (hh : 0 < h)
    (rows : Fin h → Finset ℕ)
    (hne : ∀ i, (rows i).Nonempty)
    (hbound : ∀ i x, x ∈ rows i → x < width n)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (rows i) (rows j))
    (hgap : ∀ i, finiteCyclicGapInventory (width n) (rows i) =
      Multiset.ofList (fullGapList n)) : OriginalCorral h n := by
  classical
  have hW : 0 < width n := by
    let i : Fin h := ⟨0, hh⟩
    obtain ⟨x, hx⟩ := hne i
    have := hbound i x hx
    omega
  letI : NeZero (width n) := ⟨by omega⟩
  have hwitness : ∀ i, ∃ (ρ : Equiv.Perm (Fin n)) (τ : ℤ),
      (∀ j : Fin n, ((τ : ZMod (width n)) + (partialSum ρ j : ZMod (width n))).val ∈ rows i) ∧
      Function.Injective (fun j : Fin n =>
        (τ : ZMod (width n)) + (partialSum ρ j : ZMod (width n))) := by
    intro i
    exact gapRow_original_witness n (rows i) (hne i) (hbound i) (hgap i)
  choose ρ τ hmem hinj using hwitness
  refine ⟨ρ, τ, ?_⟩
  intro a b hab
  rcases a with ⟨i, j⟩
  rcases b with ⟨i', j'⟩
  change (τ i : ZMod (width n)) + (partialSum (ρ i) j : ZMod (width n)) =
    (τ i' : ZMod (width n)) + (partialSum (ρ i') j' : ZMod (width n)) at hab
  let x := ((τ i : ZMod (width n)) + (partialSum (ρ i) j : ZMod (width n))).val
  have hx : x ∈ rows i := hmem i j
  have hx' : x ∈ rows i' := by
    have heq := congrArg ZMod.val hab
    change x = ((τ i' : ZMod (width n)) + (partialSum (ρ i') j' : ZMod (width n))).val at heq
    rw [heq]
    exact hmem i' j'
  have hii' : i = i' := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisjoint i i' hne) hx hx'
  have hjj' : j = j' := by
    apply hinj i
    simpa only [← hii'] using hab
  exact Prod.ext hii' hjj'

/-- A complete partition is a special case of disjoint gap rows. This keeps
the original optimal-order interface available. -/
theorem originalCorral_of_gap_rows (h n : ℕ) (hh : 0 < h)
    (rows : Fin h → Finset ℕ)
    (hne : ∀ i, (rows i).Nonempty)
    (hbound : ∀ i x, x ∈ rows i → x < width n)
    (hpartition : ∀ x, x < width n → ∃! i, x ∈ rows i)
    (hgap : ∀ i, finiteCyclicGapInventory (width n) (rows i) =
      Multiset.ofList (fullGapList n)) : OriginalCorral h n := by
  apply originalCorral_of_disjoint_gap_rows h n hh rows hne hbound ?_ hgap
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨owner, _, huniq⟩ := hpartition x (hbound i x hxi)
  exact hij ((huniq i hxi).trans (huniq j hxj).symm)

end CorralFormalization
