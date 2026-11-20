import CorralFormalization.EndpointProof.Factor.Allocation.Capped

/-!
# Simultaneous capped retention for actual raw inventories

This supplies ordinary pools and a potentially smaller closing bank at once:
every raw role is protected before any fill is chosen. No raw role is assumed
to fit its capacity; its physical retained intersection is exactly optimal.
-/

open scoped BigOperators Classical symmDiff
namespace EndpointFactor.Allocation
variable {α : Type*} [DecidableEq α]

/-- Pairwise disjoint raw roles can simultaneously be filled to arbitrary
capacities while retaining exactly `min |raw ∩ W| capacity` raw elements.
The chosen sets are actual disjoint subsets of `W`; their leftover is exact. -/
theorem exists_capped_raw_allocation (n : ℕ) (W : Finset α)
    (raw : Fin n → Finset α) (cap : Fin n → ℕ)
    (hraw : ∀ i j, i ≠ j → Disjoint (raw i) (raw j))
    (hroom : (∑ i, cap i) ≤ W.card) :
    ∃ chosen : Fin n → Finset α,
      (∀ i, chosen i ⊆ W ∧ (chosen i).card = cap i ∧
        (raw i ∩ chosen i).card = min (raw i ∩ W).card (cap i) ∧
        (raw i ∆ chosen i).card =
          max ((raw i).card - cap i) (cap i + 2*(raw i \ W).card - (raw i).card)) ∧
      (∀ i j, i ≠ j → Disjoint (chosen i) (chosen j)) ∧
      (W \ Finset.univ.biUnion chosen).card + (∑ i, cap i) = W.card := by
  have hexists (i : Fin n) : ∃ kept : Finset α,
      kept ⊆ raw i ∩ W ∧ kept.card = min (raw i ∩ W).card (cap i) :=
    Finset.exists_subset_card_eq (Nat.min_le_left _ _)
  choose kept hkeepsub hkeepcard using hexists
  have hsub : ∀ i, kept i ⊆ W := fun i => (hkeepsub i).trans Finset.inter_subset_right
  have hcap : ∀ i, (kept i).card ≤ cap i := by
    intro i
    rw [hkeepcard]
    exact Nat.min_le_right _ _
  have hkeepdisj : ∀ i j, i ≠ j → Disjoint (kept i) (kept j) := by
    intro i j hij
    exact (hraw i j hij).mono ((hkeepsub i).trans Finset.inter_subset_left)
      ((hkeepsub j).trans Finset.inter_subset_left)
  obtain ⟨chosen, hchosen, hpair, hleft⟩ :=
    exists_indexed_protected_allocation_with_remainder n W kept cap hsub hcap hkeepdisj hroom
  refine ⟨chosen, ?_, hpair, hleft⟩
  intro i
  have hret : kept i ⊆ raw i ∩ chosen i := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hkeepsub i hx)).1, (hchosen i).1 hx⟩
  have hlow := Finset.card_le_card hret
  rw [hkeepcard] at hlow
  have hupper1 : (raw i ∩ chosen i).card ≤ (raw i ∩ W).card :=
    Finset.card_le_card (Finset.inter_subset_inter_left (hchosen i).2.1)
  have hupper2 : (raw i ∩ chosen i).card ≤ cap i := by
    have h := Finset.card_le_card (Finset.inter_subset_right : raw i ∩ chosen i ⊆ chosen i)
    simpa [(hchosen i).2.2] using h
  have hinter : (raw i ∩ chosen i).card = min (raw i ∩ W).card (cap i) :=
    le_antisymm (le_min hupper1 hupper2) hlow
  exact ⟨(hchosen i).2.1, (hchosen i).2.2, hinter,
    capped_symmDiff_eq_max (raw i) W (chosen i) (cap i) (hchosen i).2.2 hinter⟩

/-- A role whose eligible raw inventory fits its capacity is retained in full. -/
theorem capped_allocation_retains_fitting (raw W chosen : Finset α) (capacity : ℕ)
    (hchosen : chosen ⊆ W)
    (hinter : (raw ∩ chosen).card = min (raw ∩ W).card capacity)
    (hfit : (raw ∩ W).card ≤ capacity) : raw ∩ W ⊆ chosen := by
  have hsub : raw ∩ chosen ⊆ raw ∩ W := Finset.inter_subset_inter_left hchosen
  have hcard : (raw ∩ W).card ≤ (raw ∩ chosen).card := by simpa [hfit] using hinter.ge
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  intro x hx
  have hx' : x ∈ raw ∩ chosen := by simpa [heq] using hx
  exact (Finset.mem_inter.mp hx').2

end EndpointFactor.Allocation
