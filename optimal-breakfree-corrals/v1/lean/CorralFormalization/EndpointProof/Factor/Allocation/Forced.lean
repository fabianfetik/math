import CorralFormalization.EndpointProof.Factor.Allocation.Protected

/-!
# Protecting forced terminals without consuming another retained role

The `excluded` set stands for terminals assigned to the other layers. This
module constructs the actual protected piece for one layer; a simultaneous
allocation must still prove that its different protected pieces are disjoint
and that its common filling pool has sufficient capacity.
-/

namespace EndpointFactor.Allocation

open scoped Classical
variable {α : Type*} [DecidableEq α]

/-- Retain as many eligible raw coordinates as possible after protecting a
prescribed set. The possible loss relative to ideal capped raw retention is
at most the number of excluded plus forced coordinates. -/
theorem exists_forced_retained_piece (raw target forced excluded : Finset α)
    (capacity : ℕ)
    (hforced : forced ⊆ target \ excluded)
    (hforcecap : forced.card ≤ capacity) :
    ∃ kept : Finset α,
      forced ⊆ kept ∧ kept ⊆ target \ excluded ∧ kept ⊆ forced ∪ raw ∧
      kept.card ≤ capacity ∧
      min (raw ∩ target).card capacity ≤
        (raw ∩ kept).card + excluded.card + forced.card := by
  let available := (raw ∩ (target \ excluded)) \ forced
  let count := min available.card (capacity - forced.card)
  obtain ⟨retained, hretained, hretainedcard⟩ :=
    Finset.exists_subset_card_eq (s := available) (n := count)
      (by dsimp [count]; exact Nat.min_le_left _ _)
  let kept := forced ∪ retained
  have hdisj : Disjoint forced retained := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp (hretained hy)).2 hx
  have hsubset : kept ⊆ target \ excluded := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hforced h
    · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp (hretained h)).1).2
  have hrawsubset : retained ⊆ raw ∩ kept := by
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp (hretained hx)).1).1,
        Finset.mem_union_right _ hx⟩
  have hcard : kept.card ≤ capacity := by
    dsimp only [kept]
    rw [Finset.card_union_of_disjoint hdisj, hretainedcard]
    dsimp [count]
    have hmin := Nat.min_le_right available.card (capacity - forced.card)
    omega
  have havailable : available = (raw ∩ target) \ (excluded ∪ forced) := by
    ext x
    simp only [available, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    tauto
  have hraw_bound : (raw ∩ target).card ≤ available.card + excluded.card + forced.card := by
    have h := Finset.card_le_card_sdiff_add_card (s := raw ∩ target) (t := excluded ∪ forced)
    rw [← havailable] at h
    have hu := Finset.card_union_le excluded forced
    omega
  have hmin_bound : min (raw ∩ target).card capacity ≤
      retained.card + excluded.card + forced.card := by
    rw [hretainedcard]
    dsimp [count]
    by_cases h1 : (raw ∩ target).card ≤ capacity
    · rw [min_eq_left h1]
      by_cases h2 : available.card ≤ capacity - forced.card
      · rw [min_eq_left h2]; omega
      · rw [min_eq_right (le_of_not_ge h2)]; omega
    · rw [min_eq_right (le_of_not_ge h1)]
      by_cases h2 : available.card ≤ capacity - forced.card
      · rw [min_eq_left h2]; omega
      · rw [min_eq_right (le_of_not_ge h2)]; omega
  have hretain := Finset.card_le_card hrawsubset
  refine ⟨kept, Finset.subset_union_left, hsubset, ?_, hcard, ?_⟩
  · apply Finset.union_subset Finset.subset_union_left
    intro x hx
    exact Finset.mem_union_right _
      ((Finset.mem_inter.mp (Finset.mem_sdiff.mp (hretained hx)).1).1)
  · omega

end EndpointFactor.Allocation
