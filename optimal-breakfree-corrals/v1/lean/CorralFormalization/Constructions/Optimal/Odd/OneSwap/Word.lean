import CorralFormalization.Constructions.Optimal.Odd.CoreGaps

/-! Literal word data for the one-swap odd construction. The earlier word
lemmas use `A ≥ 2`; the same word is also valid at
`A = 1` as well.  This module extends precisely those reusable word facts.
-/

namespace CorralFormalization.OneSwapOdd

def h (A : ℕ) : ℕ := 2 * A + 3
def K (A : ℕ) : ℕ := 4 * A + 3
def U (A : ℕ) : ℕ := h A * K A

theorem word_length (A : ℕ) (hA : 1 ≤ A) :
    (oddConstructionGapWord A).length = K A := by
  by_cases h1 : A = 1
  · subst A; decide
  · exact oddConstructionGapWord_length A (by omega)

theorem word_positive (A : ℕ) (hA : 1 ≤ A) :
    ∀ x ∈ oddConstructionGapWord A, 0 < x := by
  by_cases h1 : A = 1
  · subst A; decide
  · intro x hx
    exact oddConstructionGapWord_positive A (by omega) hx

theorem word_sum (A : ℕ) (hA : 1 ≤ A) :
    (oddConstructionGapWord A).sum = U A := by
  by_cases h1 : A = 1
  · subst A; decide
  · exact oddConstructionGapWord_sum A (by omega)

theorem word_inventory (A : ℕ) (hA : 1 ≤ A) :
    (oddConstructionGapWord A).Perm (oddConstructionAllowedGapInventory A) := by
  by_cases h1 : A = 1
  · subst A; decide
  · exact oddConstructionGapWord_perm_allowed A (by omega)

theorem word_plus_missing_inventory (A : ℕ) (hA : 1 ≤ A) :
    Multiset.ofList (oddConstructionGapWord A) + Multiset.ofList [3, K A] =
      Multiset.ofList (oddConstructionFullGapInventory A) := by
  by_cases h1 : A = 1
  · subst A
    apply Multiset.coe_eq_coe.mpr
    decide
  · exact oddConstructionWord_plus_missing_inventory A (by omega)

theorem prefix_residue_bijective (A : ℕ) (hA : 1 ≤ A) :
    Function.Bijective (actualOddPrefixResidue A) := by
  by_cases h1 : A = 1
  · subst A; decide
  · exact actualOddPrefixResidue_bijective A (by omega)

theorem prefix_lt (A : ℕ) (hA : 1 ≤ A) (j : Fin (K A)) :
    oddConstructionPrefix A j.val < U A := by
  have hj : j.val < (oddConstructionGapWord A).length := by
    rw [word_length A hA]; exact j.isLt
  have hm : oddConstructionPrefix A j.val ∈ properPrefixSites (oddConstructionGapWord A) :=
    (mem_properPrefixSites_iff _ _).2 ⟨j.val, hj, rfl⟩
  have ht := properPrefixSites_lt_sum _ (word_positive A hA) _ hm
  simpa [word_sum A hA] using ht

theorem prefix_monotone (A : ℕ) : Monotone (oddConstructionPrefix A) := by
  intro i j hij
  exact (List.take_sublist_take_left hij).sum_le_sum (by intros; omega)

theorem prefix_E (A t : ℕ) (hA : 1 ≤ A) (ht : t < A) :
    oddConstructionPrefix A (2 * A + 3 + 2 * t) =
      (A + 3 + t) * K A + (2 * A + 2 - 2 * t) := by
  by_cases h1 : A = 1
  · subst A
    have ht0 : t = 0 := by omega
    subst t; decide
  · exact oddConstructionPrefix_E A t (by omega) ht

theorem prefix_F (A t : ℕ) (hA : 1 ≤ A) (ht : t < A - 1) :
    oddConstructionPrefix A (2 * A + 4 + 2 * t) =
      (A + 3 + t) * K A + (2 * A + 4 + 2 * t) := by
  exact oddConstructionPrefix_F A t (by omega) ht

theorem prefix_final (A : ℕ) (hA : 1 ≤ A) :
    oddConstructionPrefix A (4 * A + 2) = U A - 1 := by
  by_cases h1 : A = 1
  · subst A; decide
  · rw [oddConstructionPrefix_final_value A (by omega)]
    unfold U h K
    ring_nf
    omega

theorem raw_prefix_bound (A : ℕ) (hA : 1 ≤ A)
    (p : ℕ) (hp : p ∈ oddConstructionRawPrefixSet A) : p < U A := by
  have hm : p ∈ properPrefixSites (oddConstructionGapWord A) := List.mem_toFinset.mp hp
  have ht := properPrefixSites_lt_sum _ (word_positive A hA) _ hm
  simpa [word_sum A hA] using ht

theorem raw_prefix_eq_image (A : ℕ) (hA : 1 ≤ A) :
    oddConstructionRawPrefixSet A = Finset.univ.image
      (fun j : Fin (K A) => oddConstructionPrefix A j.val) := by
  ext p
  simp only [oddConstructionRawPrefixSet, List.mem_toFinset, mem_properPrefixSites_iff,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hp⟩
    exact ⟨⟨j, by rw [← word_length A hA]; exact hj⟩, hp⟩
  · rintro ⟨j, hj⟩
    exact ⟨j.val, by rw [word_length A hA]; exact j.isLt, hj⟩

theorem raw_prefix_gaps (A : ℕ) (hA : 1 ≤ A) :
    finiteCyclicGapInventory (U A) (oddConstructionRawPrefixSet A) =
      Multiset.ofList (oddConstructionGapWord A) := by
  have hlen := word_length A hA
  have hsum := word_sum A hA
  have hpos := word_positive A hA
  cases hw : oddConstructionGapWord A with
  | nil => simp [hw, K] at hlen
  | cons x xs =>
    have hpos' : ∀ z ∈ x :: xs, 0 < z := by simpa [hw] using hpos
    have hsum' : (x :: xs).sum = U A := by simpa [hw] using hsum
    unfold oddConstructionRawPrefixSet
    rw [hw, ← hsum']
    exact properPrefixSites_finite_gaps x xs hpos'

end CorralFormalization.OneSwapOdd
