import CorralFormalization.Constructions.Optimal.Even.Projection

set_option maxHeartbeats 0

namespace CorralFormalization

/-- The two normalized even-residue intervals in the paper's table. -/
def evenConstructionXTable (k u : ℕ) : Prop :=
  if k % 2 = 0 then
    u ≤ 3 * (k / 2) - 1 ∨
      (4 * (k / 2) ≤ u ∧ u ≤ 7 * (k / 2) - 2)
  else
    u ≤ 3 * (k / 2) ∨
      (4 * (k / 2) + 2 ≤ u ∧ u ≤ 7 * (k / 2) + 2)

/-- The two normalized odd-residue intervals in the paper's table. -/
def evenConstructionYTable (k u : ℕ) : Prop :=
  if k % 2 = 0 then
    ((k / 2) ≤ u ∧ u ≤ 2 * (k / 2) - 1) ∨
      (5 * (k / 2) - 1 ≤ u ∧ u ≤ 6 * (k / 2) - 2)
  else
    ((k / 2) ≤ u ∧ u ≤ 2 * (k / 2)) ∨
      (5 * (k / 2) + 2 ≤ u ∧ u ≤ 6 * (k / 2) + 1)

/-- Collecting the actual normalized E/O families gives exactly the
paper's even-residue interval table. -/
theorem evenConstructionXFamilies_iff_table (k u : ℕ) (hk : 1 ≤ k) :
    evenConstructionXFamilies k u ↔ evenConstructionXTable k u := by
  constructor
  · intro h
    unfold evenConstructionXFamilies at h
    unfold evenConstructionXTable
    split_ifs <;>
      rcases h with h | h | ⟨r, hr0, hr1, hr2⟩ | ⟨r, hr0, hr1, hr2⟩ <;> omega
  · intro htable
    unfold evenConstructionXFamilies
    by_cases h0 : u < k
    · exact Or.inl h0
    · by_cases h1 : 2 * k ≤ u ∧ u < 3 * k
      · exact Or.inr (Or.inl h1)
      · by_cases h2 : u < 2 * k
        · right; right; left
          refine ⟨2 * k - 1 - u, ?_, ?_, ?_⟩ <;>
            (unfold evenConstructionXTable at htable; split_ifs at htable <;> omega)
        · right; right; right
          refine ⟨4 * k - 2 - u, ?_, ?_, ?_⟩ <;>
            (unfold evenConstructionXTable at htable; split_ifs at htable <;> omega)

/-- Collecting the actual normalized E/O families gives exactly the
paper's odd-residue interval table, including the empty `k=1` interval. -/
theorem evenConstructionYFamilies_iff_table (k u : ℕ) (hk : 1 ≤ k) :
    evenConstructionYFamilies k u ↔ evenConstructionYTable k u := by
  constructor
  · intro h
    unfold evenConstructionYFamilies at h
    unfold evenConstructionYTable
    split_ifs <;> rcases h with ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩ <;> omega
  · intro htable
    unfold evenConstructionYFamilies
    by_cases h0 : u < k
    · left
      refine ⟨k - 1 - u, ?_, ?_⟩ <;>
        (unfold evenConstructionYTable at htable; split_ifs at htable <;> omega)
    · right
      refine ⟨3 * k - 2 - u, ?_, ?_⟩ <;>
        (unfold evenConstructionYTable at htable; split_ifs at htable <;> omega)

/-- The paper's normalized interval table is precisely the actual
projected proper-prefix set. -/
theorem evenConstructionProjectedSet_table (k x : ℕ) (hk : 1 ≤ k) :
    x ∈ evenConstructionProjectedSet k ↔
      (∃ u, x = 2 * u ∧ evenConstructionXTable k u) ∨
      (∃ u, x = 2 * u + 1 ∧ evenConstructionYTable k u) := by
  rw [evenConstructionProjectedSet_normalized k x hk]
  simp only [evenConstructionXFamilies_iff_table k _ hk, evenConstructionYFamilies_iff_table k _ hk]

end CorralFormalization
