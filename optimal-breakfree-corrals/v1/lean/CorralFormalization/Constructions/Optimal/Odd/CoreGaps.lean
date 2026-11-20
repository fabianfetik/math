import CorralFormalization.Constructions.Optimal.Odd.Join
import CorralFormalization.Constructions.Optimal.Odd.Inventory
import CorralFormalization.PositiveGapWord

namespace CorralFormalization

/-! This module uses the earlier two-swap odd construction. References to
the paper and its numbered equations below concern that earlier manuscript,
not the one-swap odd construction printed in the manuscript. The gap word
itself is shared by the two constructions. -/

open OddSeamAssignment

/-- The actual set of proper prefix points of the printed odd word. -/
def oddConstructionRawPrefixSet (A : ℕ) : Finset ℕ :=
  (properPrefixSites (oddConstructionGapWord A)).toFinset

/-- The chronological prefix list and the previously used Fin-indexed
prefix definition represent the same finite set. -/
theorem oddConstructionRawPrefixSet_eq_image (A : ℕ) (hA : 2 ≤ A) :
    oddConstructionRawPrefixSet A = Finset.univ.image
      (fun j : Fin (4 * A + 3) => oddConstructionPrefix A j.val) := by
  ext p
  simp only [oddConstructionRawPrefixSet, List.mem_toFinset, mem_properPrefixSites_iff,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hp⟩
    have hj' : j < 4 * A + 3 := by
      simpa [oddConstructionGapWord_length A hA] using hj
    exact ⟨⟨j, hj'⟩, hp⟩
  · rintro ⟨j, hj⟩
    refine ⟨j.val, ?_, hj⟩
    simpa [oddConstructionGapWord_length A hA] using j.isLt

theorem oddConstructionRawPrefixSet_bound (A : ℕ) (hA : 2 ≤ A)
    (p : ℕ) (hp : p ∈ oddConstructionRawPrefixSet A) :
    p < (2 * A + 3) * (4 * A + 3) := by
  have hpos : ∀ x ∈ oddConstructionGapWord A, 0 < x := by
    intro x hx
    exact oddConstructionGapWord_positive A hA hx
  have hp' : p ∈ properPrefixSites (oddConstructionGapWord A) := List.mem_toFinset.mp hp
  have hlt := properPrefixSites_lt_sum (oddConstructionGapWord A) hpos p hp'
  simpa [oddConstructionGapWord_sum A hA] using hlt

/-- Before shifting, the sorted cyclic gaps of the actual prefix set are
the entries of the actual printed word, with multiplicities. -/
theorem oddConstructionRawPrefixSet_gaps (A : ℕ) (hA : 2 ≤ A) :
    finiteCyclicGapInventory ((2 * A + 3) * (4 * A + 3)) (oddConstructionRawPrefixSet A) =
      Multiset.ofList (oddConstructionGapWord A) := by
  have hlen := oddConstructionGapWord_length A hA
  have hsum := oddConstructionGapWord_sum A hA
  have hpos : ∀ x ∈ oddConstructionGapWord A, 0 < x := by
    intro x hx
    exact oddConstructionGapWord_positive A hA hx
  cases hw : oddConstructionGapWord A with
  | nil => simp [hw] at hlen
  | cons x xs =>
    have hpos' : ∀ z ∈ x :: xs, 0 < z := by simpa [hw] using hpos
    have hsum' : (x :: xs).sum = (2 * A + 3) * (4 * A + 3) := by
      simpa [hw] using hsum
    unfold oddConstructionRawPrefixSet
    rw [hw, ← hsum']
    exact properPrefixSites_finite_gaps x xs hpos'

/-- The paper's `Q` is exactly the physical shift of those actual prefixes. -/
theorem oddConstructionQ_eq_shifted_raw (A : ℕ) (hA : 2 ≤ A) :
    actualOddQ A = (oddConstructionRawPrefixSet A).image
      (fun p => (p + (2 * A - 3)) % ((2 * A + 3) * (4 * A + 3))) := by
  rw [oddConstructionRawPrefixSet_eq_image A hA, Finset.image_image]
  rfl

/-- Each first-factor row is one cyclic translate of the actual prefix set. -/
theorem oddConstructionCoreSites_eq_rotated_raw (A : ℕ) (hA : 2 ≤ A)
    (s : Fin (2 * A + 3)) :
    oddConstructionCoreSites A s = (oddConstructionRawPrefixSet A).image
      (fun p => (p + ((2 * A - 3) + (4 * A + 3) * s.val)) %
        ((2 * A + 3) * (4 * A + 3))) := by
  unfold oddConstructionCoreSites translatedSites
  rw [oddConstructionQ_eq_shifted_raw A hA, Finset.image_image]
  apply Finset.image_congr
  intro p hp
  simp only [Function.comp_apply]
  rw [Nat.mod_add_mod]
  simp [Nat.add_assoc]

/-- Every actual core row has the cyclic gap multiset of the printed word. -/
theorem oddConstructionCoreSites_gaps (A : ℕ) (hA : 2 ≤ A)
    (s : Fin (2 * A + 3)) :
    finiteCyclicGapInventory ((2 * A + 3) * (4 * A + 3)) (oddConstructionCoreSites A s) =
      Multiset.ofList (oddConstructionGapWord A) := by
  rw [oddConstructionCoreSites_eq_rotated_raw A hA s]
  rw [finite_set_cyclic_gap_rotate _ _ _ (by positivity) (oddConstructionRawPrefixSet_bound A hA)]
  exact oddConstructionRawPrefixSet_gaps A hA

/-- The actual completed rows (12) partition the full clock and each has
exactly the gap lengths `1,...,4A+5`, with multiplicity one. -/
theorem oddConstructionJoinedSites_partition_and_exact_gaps (A : ℕ) (hA : 2 ≤ A) :
    (∀ x, x < (2 * A + 3) * (4 * A + 3) + 2 * h A ↔
      ∃! s : Fin (h A), x ∈ oddConstructionJoinedSites A s) ∧
    ∀ s : Fin (h A),
      finiteCyclicGapInventory ((2 * A + 3) * (4 * A + 3) + 2 * h A)
          (oddConstructionJoinedSites A s) =
        Multiset.ofList (oddConstructionFullGapInventory A) := by
  obtain ⟨hpartition, hgaps⟩ := oddConstructionJoinedSites_partition_and_gaps A hA
  refine ⟨hpartition, ?_⟩
  intro s
  have hk : 2 * h A - 3 = 4 * A + 3 := by dsimp [h]; omega
  calc
    _ = finiteCyclicGapInventory ((2 * A + 3) * (4 * A + 3)) (oddConstructionCoreSites A s) +
          Multiset.ofList [3, 2 * h A - 3] := hgaps s
    _ = Multiset.ofList (oddConstructionGapWord A) + Multiset.ofList [3, 4 * A + 3] := by
      rw [oddConstructionCoreSites_gaps A hA s, hk]
    _ = Multiset.ofList (oddConstructionFullGapInventory A) := oddConstructionWord_plus_missing_inventory A hA

end CorralFormalization
