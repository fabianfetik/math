import CorralFormalization.Constructions.Optimal.Even.Lift
import CorralFormalization.CorralFromRows

namespace CorralFormalization

theorem evenConstructionRawPrefixSet_nonempty (k : ℕ) (hk : 1 ≤ k) :
    (evenConstructionRawPrefixSet k).Nonempty := by
  refine ⟨0, (evenConstructionRawPrefixSet_mem k 0 hk).2 ?_⟩
  exact ⟨0, by omega, by simp [evenConstructionPrefix]⟩

theorem evenConstructionReflectedSet_nonempty (k : ℕ) (hk : 1 ≤ k) :
    (evenConstructionReflectedSet k).Nonempty := by
  obtain ⟨q, hq⟩ := evenConstructionRawPrefixSet_nonempty k hk
  exact ⟨_, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩

/-- The reflected actual prefix set is a rotation of the actual prefix set
of the reversed printed gap word. -/
theorem evenConstructionReflectedSet_eq_rotated_reverse (k : ℕ) (hk : 1 ≤ k) :
    evenConstructionReflectedSet k =
      (properPrefixSites (evenConstructionGapWord k).reverse).toFinset.image
        (fun q => (q + evenConstructionShift k) % evenConstructionClock k) := by
  have hpos : ∀ x ∈ evenConstructionGapWord k, 0 < x := evenConstructionGapWord_positive k hk
  have hsumpos : 0 < (evenConstructionGapWord k).sum := by
    rw [← evenConstructionClock_eq_sum k hk]
    exact evenConstructionClock_pos k hk
  rw [properPrefixSites_reverse_reflect (evenConstructionGapWord k) hpos hsumpos]
  rw [← evenConstructionClock_eq_sum k hk]
  unfold evenConstructionReflectedSet evenConstructionRawPrefixSet
  rw [Finset.image_image]
  apply Finset.image_congr
  intro q hq
  simp only [Function.comp_apply]
  rw [Nat.mod_add_mod]
  have hlt : q < evenConstructionClock k := by
    rw [evenConstructionClock_eq_sum k hk]
    exact properPrefixSites_lt_sum (evenConstructionGapWord k) hpos q (List.mem_toFinset.mp hq)
  congr 1
  omega

theorem evenConstructionRawPrefixSet_gaps (k : ℕ) (hk : 1 ≤ k) :
    finiteCyclicGapInventory (evenConstructionClock k) (evenConstructionRawPrefixSet k) =
      Multiset.ofList (evenConstructionGapWord k) := by
  have hpos : ∀ x ∈ evenConstructionGapWord k, 0 < x := evenConstructionGapWord_positive k hk
  have hlen := evenConstructionGapWord_length k hk
  have hsum := evenConstructionClock_eq_sum k hk
  cases hw : evenConstructionGapWord k with
  | nil => simp [hw] at hlen; omega
  | cons x xs =>
    have hpos' : ∀ z ∈ x :: xs, 0 < z := by simpa [hw] using hpos
    have hsum' : evenConstructionClock k = (x :: xs).sum := by simpa [hw] using hsum
    unfold evenConstructionRawPrefixSet
    rw [hw, hsum']
    exact properPrefixSites_finite_gaps x xs hpos'

theorem evenConstructionReflectedSet_gaps (k : ℕ) (hk : 1 ≤ k) :
    finiteCyclicGapInventory (evenConstructionClock k) (evenConstructionReflectedSet k) =
      Multiset.ofList (evenConstructionGapWord k) := by
  rw [evenConstructionReflectedSet_eq_rotated_reverse k hk]
  have hpos : ∀ x ∈ (evenConstructionGapWord k).reverse, 0 < x := by
    intro x hx
    exact evenConstructionGapWord_positive k hk x (by simpa using hx)
  have hbound : ∀ q ∈ (properPrefixSites (evenConstructionGapWord k).reverse).toFinset,
      q < evenConstructionClock k := by
    intro q hq
    have hlt := properPrefixSites_lt_sum (evenConstructionGapWord k).reverse hpos q
      (List.mem_toFinset.mp hq)
    simpa [← evenConstructionClock_eq_sum k hk] using hlt
  rw [finite_set_cyclic_gap_rotate _ _ _ (evenConstructionClock_pos k hk) hbound]
  have hsum : evenConstructionClock k = (evenConstructionGapWord k).reverse.sum := by
    simpa using evenConstructionClock_eq_sum k hk
  have hlen := evenConstructionGapWord_length k hk
  have hrevlen : (evenConstructionGapWord k).reverse.length = 4 * k - 1 := by simpa using hlen
  cases hw : (evenConstructionGapWord k).reverse with
  | nil =>
    simp [hw] at hrevlen
    omega
  | cons x xs =>
    have hpos' : ∀ z ∈ x :: xs, 0 < z := by simpa [hw] using hpos
    have hsum' : evenConstructionClock k = (x :: xs).sum := by simpa [hw] using hsum
    rw [hsum', properPrefixSites_finite_gaps x xs hpos']
    have hperm : (x :: xs).Perm (evenConstructionGapWord k) := by
      rw [← hw]
      exact List.reverse_perm _
    exact Multiset.coe_eq_coe.mpr hperm

end CorralFormalization
