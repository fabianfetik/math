import CorralFormalization.Constructions.Optimal.Even.Injective
import CorralFormalization.PositiveGapWord

namespace CorralFormalization

/-- The actual proper-prefix points of the even-height word. -/
def evenConstructionRawPrefixSet (k : ℕ) : Finset ℕ :=
  (properPrefixSites (evenConstructionGapWord k)).toFinset

theorem evenConstructionRawPrefixSet_mem (k p : ℕ) (hk : 1 ≤ k) :
    p ∈ evenConstructionRawPrefixSet k ↔
      ∃ j, j < 4 * k - 1 ∧ evenConstructionPrefix k j = p := by
  simp only [evenConstructionRawPrefixSet, List.mem_toFinset, mem_properPrefixSites_iff,
    evenConstructionGapWord_length k hk, evenConstructionPrefix]

theorem evenConstructionRawPrefixSet_bound (k p : ℕ) (hk : 1 ≤ k)
    (hp : p ∈ evenConstructionRawPrefixSet k) :
    p < 2 * k * (4 * k - 1) := by
  have hpos : ∀ x ∈ evenConstructionGapWord k, 0 < x := evenConstructionGapWord_positive k hk
  have hp' : p ∈ properPrefixSites (evenConstructionGapWord k) := List.mem_toFinset.mp hp
  simpa [evenConstructionGapWord_sum k hk] using
    properPrefixSites_lt_sum (evenConstructionGapWord k) hpos p hp'

/-- The displayed projected set is the projection of the actual points. -/
theorem evenConstructionRawPrefixSet_projection (k : ℕ) (hk : 1 ≤ k) :
    (evenConstructionRawPrefixSet k).image (fun p => p % evenConstructionPeriod k) =
      evenConstructionProjectedSet k := by
  ext x
  simp only [Finset.mem_image, evenConstructionRawPrefixSet_mem k _ hk,
    evenConstructionProjectedSet, Finset.mem_range]
  constructor
  · rintro ⟨p, ⟨j, hj, rfl⟩, heq⟩
    exact ⟨j, hj, heq⟩
  · rintro ⟨j, hj, heq⟩
    exact ⟨evenConstructionPrefix k j, ⟨j, hj, rfl⟩, heq⟩

/-- Each projected residue has at most one actual proper-prefix point. -/
theorem evenConstructionRawPrefixSet_projection_injective (k p q : ℕ) (hk : 1 ≤ k)
    (hp : p ∈ evenConstructionRawPrefixSet k) (hq : q ∈ evenConstructionRawPrefixSet k)
    (heq : p % evenConstructionPeriod k = q % evenConstructionPeriod k) : p = q := by
  obtain ⟨i, hi, rfl⟩ := (evenConstructionRawPrefixSet_mem k p hk).1 hp
  obtain ⟨j, hj, rfl⟩ := (evenConstructionRawPrefixSet_mem k q hk).1 hq
  rw [evenConstructionProjectedCode_actual k i hk hi,
    evenConstructionProjectedCode_actual k j hk hj] at heq
  have hij := evenConstructionProjectedCode_injective k i j hk hi hj heq
  rw [hij]

end CorralFormalization
