import CorralFormalization.GapWitness

namespace CorralFormalization

/-- Reversing a positive cyclic gap word reflects its actual prefix sites
through zero, including the fixed initial site. -/
theorem properPrefixSites_reverse_reflect (g : List ℕ)
    (hpos : ∀ x ∈ g, 0 < x) (hW : 0 < g.sum) :
    (properPrefixSites g.reverse).toFinset =
      (properPrefixSites g).toFinset.image (fun p => (g.sum - p) % g.sum) := by
  have hlen : 0 < g.length := by
    cases g with
    | nil => simp at hW
    | cons x xs => simp
  ext p
  simp only [List.mem_toFinset, mem_properPrefixSites_iff, List.length_reverse,
    Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hp⟩
    by_cases hj0 : j = 0
    · subst j
      simp at hp
      subst p
      refine ⟨0, ⟨0, hlen, by simp⟩, ?_⟩
      simp
    · let i := g.length - j
      have hi0 : 0 < i := by dsimp [i]; omega
      have hi : i < g.length := by dsimp [i]; omega
      have hs0 := positive_take_sum_strict g hpos 0 i hi0 (by omega)
      simp only [List.take_zero, List.sum_nil] at hs0
      have hsite : (g.take i).sum < g.sum :=
        properPrefixSites_lt_sum g hpos _
          ((mem_properPrefixSites_iff g _).2 ⟨i, hi, rfl⟩)
      have htake : (g.reverse.take j).sum = (g.drop i).sum := by
        dsimp [i]
        rw [List.take_reverse, List.sum_reverse]
      have hsum := List.sum_take_add_sum_drop g i
      refine ⟨(g.take i).sum, ⟨i, hi, rfl⟩, ?_⟩
      rw [Nat.mod_eq_of_lt (by omega : g.sum - (g.take i).sum < g.sum)]
      omega
  · rintro ⟨q, ⟨i, hi, hq⟩, hp⟩
    subst q
    by_cases hi0 : i = 0
    · subst i
      simp at hp
      subst p
      exact ⟨0, hlen, by simp⟩
    · let j := g.length - i
      have hj : j < g.length := by dsimp [j]; omega
      have hs0 := positive_take_sum_strict g hpos 0 i (by omega) (by omega)
      simp only [List.take_zero, List.sum_nil] at hs0
      have hsite : (g.take i).sum < g.sum :=
        properPrefixSites_lt_sum g hpos _
          ((mem_properPrefixSites_iff g _).2 ⟨i, hi, rfl⟩)
      have htake : (g.reverse.take j).sum = (g.drop i).sum := by
        have hindex : g.length - j = i := by dsimp [j]; omega
        rw [List.take_reverse, List.sum_reverse, hindex]
      have hsum := List.sum_take_add_sum_drop g i
      rw [Nat.mod_eq_of_lt (by omega : g.sum - (g.take i).sum < g.sum)] at hp
      refine ⟨j, hj, ?_⟩
      omega

end CorralFormalization
