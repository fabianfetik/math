import CorralFormalization.Constructions.Optimal.Odd.CoreGaps
import CorralFormalization.CorralFromRows
import CorralFormalization.Bases

namespace CorralFormalization

/-! This module uses the earlier two-swap odd construction. References to
the paper and its numbered equations below concern that earlier manuscript,
not the one-swap odd construction printed in the manuscript. -/

open OddSeamAssignment OddCorePhysicalRows

/-- The combined clock in (12) is exactly the original triangular width
at the optimal order `4A+5`. -/
theorem oddConstructionWidth_eq (A : ℕ) :
    width (4 * A + 5) = (2 * A + 3) * (4 * A + 3) + 2 * h A := by
  unfold width h
  have hprod : (4 * A + 5) * (4 * A + 5 + 1) =
      ((2 * A + 3) * (4 * A + 3) + 2 * (2 * A + 3)) * 2 := by ring
  rw [hprod]
  simp

namespace OptimalOdd

/-- For every `A≥2`, the earlier two-swap odd construction supplies the
permutations, integer shifts, and all distinct partial sums required by the
literal original contract at height `2A+3` and order `4A+5`. -/
theorem exists_corral (A : ℕ) (hA : 2 ≤ A) :
    OriginalCorral (2 * A + 3) (4 * A + 5) := by
  apply originalCorral_of_gap_rows (2 * A + 3) (4 * A + 5) (by omega)
    (oddConstructionJoinedSites A)
  · intro s
    obtain ⟨x, hx⟩ := oddConstructionCoreSites_nonempty A hA s
    refine ⟨x, ?_⟩
    exact Finset.mem_union.mpr (Or.inl hx)
  · intro s x hx
    rw [oddConstructionWidth_eq]
    exact joined_row_site_lt (oddConstructionCoreSites A) (physicalRowSites A) (oddConstructionOwnerFin A)
      (oddConstructionCoreSites_bound A) (oddConstructionPhysicalSites_bound A hA) s x hx
  · intro x hx
    rw [oddConstructionWidth_eq] at hx
    exact ((oddConstructionJoinedSites_partition_and_exact_gaps A hA).1 x).1 hx
  · intro s
    rw [oddConstructionWidth_eq]
    have hgap := (oddConstructionJoinedSites_partition_and_exact_gaps A hA).2 s
    simpa only [oddConstructionFullGapInventory_eq_range, fullGapList] using hgap

/-- The earlier odd construction together with the checked small cases
proves the literal optimal-order corral contract at every positive odd
height. -/
theorem all_heights (height : ℕ) (hpos : 0 < height)
    (hodd : height % 2 = 1) :
    OriginalCorral height (2 * height - 1) := by
  by_cases h1 : height = 1
  · subst height
    exact optimal_base_height_one
  · by_cases h3 : height = 3
    · subst height
      exact optimal_base_height_three
    · by_cases h5 : height = 5
      · subst height
        exact optimal_base_height_five
      · let A := (height - 3) / 2
        have hA : 2 ≤ A := by dsimp [A]; omega
        have hheight : height = 2 * A + 3 := by dsimp [A]; omega
        have horder : 2 * height - 1 = 4 * A + 5 := by omega
        rw [horder, hheight]
        exact exists_corral A hA

end OptimalOdd

end CorralFormalization
