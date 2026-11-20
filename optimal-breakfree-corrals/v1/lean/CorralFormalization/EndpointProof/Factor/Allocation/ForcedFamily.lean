import CorralFormalization.EndpointProof.Factor.Allocation.Forced

/-!
# Simultaneous special classes with prescribed terminals

The protected pieces of all classes are chosen before any filling. The common
filling carrier uses only the raw classes, reserve and forced points, never
unlisted generic raw classes. Its exact available capacity is an explicit
input, to be established from the particular paper sample and constants.
-/

open scoped BigOperators Classical
namespace EndpointFactor.Allocation
variable {α : Type*} [DecidableEq α]

def forcedUnion {n : ℕ} (forced : Fin n → Finset α) : Finset α :=
  Finset.univ.biUnion forced

def rawEligibleUnion {n : ℕ} (raw : Fin n → Finset α) (W : Finset α) : Finset α :=
  Finset.univ.biUnion (fun i => raw i ∩ W)

def forcedCarrier {n : ℕ} (raw forced : Fin n → Finset α)
    (W reserve : Finset α) : Finset α :=
  rawEligibleUnion raw W ∪ (reserve ∩ W) ∪ forcedUnion forced

theorem forced_subset_union {n : ℕ} (forced : Fin n → Finset α) (i : Fin n) :
    forced i ⊆ forcedUnion forced := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩

theorem rawEligible_subset_union {n : ℕ} (raw : Fin n → Finset α) (W : Finset α)
    (i : Fin n) : raw i ∩ W ⊆ rawEligibleUnion raw W := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩

/-- Construct actual equal- or unequal-sized disjoint classes from disjoint
raw roles, protecting every forced point. For each class the number of raw
points retained is at most the total forced inventory below its individual
ideal capped retention. The carrier's room is not assumed by definition: it
is the one numerical premise still requiring the paper's reserve estimates. -/
theorem exists_forced_classes (n : ℕ) (raw forced : Fin n → Finset α)
    (W reserve : Finset α) (cap : Fin n → ℕ)
    (hraw : ∀ i j, i ≠ j → Disjoint (raw i) (raw j))
    (hforced : ∀ i j, i ≠ j → Disjoint (forced i) (forced j))
    (hforceW : ∀ i, forced i ⊆ W)
    (hforcecap : ∀ i, (forced i).card ≤ cap i)
    (hroom : (∑ i, cap i) ≤ (forcedCarrier raw forced W reserve).card) :
    ∃ chosen : Fin n → Finset α,
      (∀ i, forced i ⊆ chosen i ∧ chosen i ⊆ forcedCarrier raw forced W reserve ∧
        chosen i ⊆ W ∧ (chosen i).card = cap i ∧
        min (raw i ∩ W).card (cap i) ≤ (raw i ∩ chosen i).card + (forcedUnion forced).card) ∧
      (∀ i j, i ≠ j → Disjoint (chosen i) (chosen j)) ∧
      ((forcedCarrier raw forced W reserve) \ Finset.univ.biUnion chosen).card +
        (∑ i, cap i) = (forcedCarrier raw forced W reserve).card := by
  let F := forcedUnion forced
  have hforcedF (i : Fin n) : forced i ⊆ F := forced_subset_union forced i
  have hforceeligible (i : Fin n) : forced i ⊆ W \ (F \ forced i) := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hforceW i hx,
      fun h => (Finset.mem_sdiff.mp h).2 hx⟩
  have hexists (i : Fin n) :=
    exists_forced_retained_piece (raw i) W (forced i) (F \ forced i) (cap i)
      (hforceeligible i) (hforcecap i)
  choose kept hkeepforce hkeepW hkeepraw hkeepcap hretained using hexists
  have hFcard (i : Fin n) : (F \ forced i).card + (forced i).card = F.card :=
    Finset.card_sdiff_add_card_eq_card (hforcedF i)
  have hkeepcarrier (i : Fin n) : kept i ⊆ forcedCarrier raw forced W reserve := by
    intro x hx
    have hxW : x ∈ W := (Finset.mem_sdiff.mp (hkeepW i hx)).1
    rcases Finset.mem_union.mp (hkeepraw i hx) with hf | hr
    · exact Finset.mem_union_right _ (hforcedF i hf)
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact rawEligible_subset_union raw W i (Finset.mem_inter.mpr ⟨hr, hxW⟩)
  have hkeepdisj (i j : Fin n) (hij : i ≠ j) : Disjoint (kept i) (kept j) := by
    apply Finset.disjoint_left.mpr
    intro x hi hj
    by_cases hxF : x ∈ F
    · have hxi : x ∈ forced i := by
        by_contra hx
        exact (Finset.mem_sdiff.mp (hkeepW i hi)).2 (Finset.mem_sdiff.mpr ⟨hxF, hx⟩)
      have hxj : x ∈ forced j := by
        by_contra hx
        exact (Finset.mem_sdiff.mp (hkeepW j hj)).2 (Finset.mem_sdiff.mpr ⟨hxF, hx⟩)
      exact Finset.disjoint_left.mp (hforced i j hij) hxi hxj
    · have hxi : x ∈ raw i := by
        rcases Finset.mem_union.mp (hkeepraw i hi) with hf | hr
        · exact (hxF (hforcedF i hf)).elim
        · exact hr
      have hxj : x ∈ raw j := by
        rcases Finset.mem_union.mp (hkeepraw j hj) with hf | hr
        · exact (hxF (hforcedF j hf)).elim
        · exact hr
      exact Finset.disjoint_left.mp (hraw i j hij) hxi hxj
  obtain ⟨chosen, hchosen, hpair, hleft⟩ :=
    exists_indexed_protected_allocation_with_remainder n (forcedCarrier raw forced W reserve)
      kept cap hkeepcarrier hkeepcap hkeepdisj hroom
  have hcarrierW : forcedCarrier raw forced W reserve ⊆ W := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxraw | hxf
    · rcases Finset.mem_union.mp hxraw with hxraw | hxr
      · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hxraw
        exact (Finset.mem_inter.mp hi).2
      · exact (Finset.mem_inter.mp hxr).2
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hxf
      exact hforceW i hi
  refine ⟨chosen, ?_, hpair, hleft⟩
  intro i
  have hrawsub : raw i ∩ kept i ⊆ raw i ∩ chosen i :=
    Finset.inter_subset_inter_left (hchosen i).1
  have hrawcard := Finset.card_le_card hrawsub
  refine ⟨(hkeepforce i).trans (hchosen i).1, (hchosen i).2.1,
    (hchosen i).2.1.trans hcarrierW, (hchosen i).2.2, ?_⟩
  have h := hretained i
  have hc := hFcard i
  change min (raw i ∩ W).card (cap i) ≤ (raw i ∩ chosen i).card + F.card
  omega

end EndpointFactor.Allocation
