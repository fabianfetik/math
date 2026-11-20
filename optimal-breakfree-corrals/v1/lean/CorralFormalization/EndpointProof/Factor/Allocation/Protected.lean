import CorralFormalization.EndpointProof.Factor.CommonFactorSample

/-!
# Simultaneous finite allocation with protected inventories

Before filling any layer, all retained raw points (and prescribed terminals)
must be protected simultaneously. The theorem below constructs actual
pairwise disjoint filled sets, not merely a numerical capacity certificate.
-/

namespace EndpointFactor.Allocation

open scoped Classical

structure Request (α : Type*) where
  keep : Finset α
  capacity : ℕ

variable {α : Type*} [DecidableEq α]

def keepUnion : List (Request α) → Finset α
  | [] => ∅
  | r :: rs => r.keep ∪ keepUnion rs

def keepTotal : List (Request α) → ℕ
  | [] => 0
  | r :: rs => r.keep.card + keepTotal rs

def capacityTotal : List (Request α) → ℕ
  | [] => 0
  | r :: rs => r.capacity + capacityTotal rs

theorem keepUnion_card_le (rs : List (Request α)) :
    (keepUnion rs).card ≤ keepTotal rs := by
  induction rs with
  | nil => simp [keepUnion, keepTotal]
  | cons r rs ih =>
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)

omit [DecidableEq α] in
theorem keepTotal_le_capacityTotal (rs : List (Request α))
    (hcap : ∀ r ∈ rs, r.keep.card ≤ r.capacity) :
    keepTotal rs ≤ capacityTotal rs := by
  induction rs with
  | nil => simp [keepTotal, capacityTotal]
  | cons r rs ih =>
      have hhead := hcap r (by simp)
      have htail : ∀ t ∈ rs, t.keep.card ≤ t.capacity := by
        intro t ht
        exact hcap t (by simp [ht])
      exact Nat.add_le_add hhead (ih htail)

theorem keepUnion_subset (rs : List (Request α)) (W : Finset α)
    (hsub : ∀ r ∈ rs, r.keep ⊆ W) : keepUnion rs ⊆ W := by
  induction rs with
  | nil => simp [keepUnion]
  | cons r rs ih =>
      simp only [keepUnion, Finset.union_subset_iff]
      exact ⟨hsub r (by simp), ih (by
        intro t ht; exact hsub t (by simp [ht]))⟩

theorem disjoint_keepUnion (A : Finset α) (rs : List (Request α))
    (hdisj : ∀ r ∈ rs, Disjoint A r.keep) : Disjoint A (keepUnion rs) := by
  induction rs with
  | nil => simp [keepUnion]
  | cons r rs ih =>
      simp only [keepUnion, Finset.disjoint_union_right]
      exact ⟨hdisj r (by simp), ih (by
        intro t ht; exact hdisj t (by simp [ht]))⟩

theorem keep_subset_keepUnion {r : Request α} {rs : List (Request α)}
    (hr : r ∈ rs) : r.keep ⊆ keepUnion rs := by
  induction rs with
  | nil => simp at hr
  | cons t ts ih =>
      simp only [keepUnion]
      rcases List.mem_cons.mp hr with heq | hmem
      · subst r; exact Finset.subset_union_left
      · exact (ih hmem).trans Finset.subset_union_right

omit [DecidableEq α] in
theorem forall2_selected_subset {W : Finset α} {rs : List (Request α)}
    {out : List (Finset α)}
    (h : List.Forall₂ (fun r A => r.keep ⊆ A ∧ A ⊆ W ∧ A.card = r.capacity) rs out) :
    ∀ B ∈ out, B ⊆ W := by
  induction h with
  | nil => simp
  | cons hrel htail ih =>
      intro B hB
      rcases List.mem_cons.mp hB with heq | hmem
      · subst B; exact hrel.2.1
      · exact ih B hmem

/-- Every retained piece is protected before the first capacity is filled.
The total capacity may be smaller than `W.card`; unused elements remain. -/
theorem exists_protected_allocation (W : Finset α) (rs : List (Request α))
    (hsub : ∀ r ∈ rs, r.keep ⊆ W)
    (hcap : ∀ r ∈ rs, r.keep.card ≤ r.capacity)
    (hdisj : rs.Pairwise (fun r t => Disjoint r.keep t.keep))
    (hroom : capacityTotal rs ≤ W.card) :
    ∃ out : List (Finset α),
      List.Forall₂ (fun r A => r.keep ⊆ A ∧ A ⊆ W ∧ A.card = r.capacity) rs out ∧
      out.Pairwise Disjoint := by
  induction rs generalizing W with
  | nil =>
      exact ⟨[], by simp, by simp⟩
  | cons r rs ih =>
      have hpairs := List.pairwise_cons.mp hdisj
      have hsubhead : r.keep ⊆ W := hsub r (by simp)
      have hsubtail : ∀ t ∈ rs, t.keep ⊆ W := by
        intro t ht; exact hsub t (by simp [ht])
      have hcaph : r.keep.card ≤ r.capacity := hcap r (by simp)
      have hcpt : ∀ t ∈ rs, t.keep.card ≤ t.capacity := by
        intro t ht; exact hcap t (by simp [ht])
      have hrestsub : keepUnion rs ⊆ W := keepUnion_subset rs W hsubtail
      have hrestcard : (keepUnion rs).card ≤ capacityTotal rs :=
        (keepUnion_card_le rs).trans (keepTotal_le_capacityTotal rs hcpt)
      have hkeep_disj : Disjoint r.keep (keepUnion rs) := disjoint_keepUnion _ rs hpairs.1
      have hkeepavail : r.keep ⊆ W \ keepUnion rs := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨hsubhead hx, (Finset.disjoint_left.mp hkeep_disj hx)⟩
      have hroom' : r.capacity + capacityTotal rs ≤ W.card := by simpa [capacityTotal] using hroom
      have havail : r.capacity ≤ (W \ keepUnion rs).card := by
        have hc := Finset.card_sdiff_add_card_eq_card hrestsub
        omega
      obtain ⟨A, hkeepA, hAavail, hAcard⟩ :=
        Finset.exists_subsuperset_card_eq hkeepavail hcaph havail
      have hAW : A ⊆ W := hAavail.trans Finset.sdiff_subset
      have hArest : Disjoint A (keepUnion rs) :=
        Finset.disjoint_left.mpr (by
          intro x hxA hxrest
          exact (Finset.mem_sdiff.mp (hAavail hxA)).2 hxrest)
      have hrestsub' : ∀ t ∈ rs, t.keep ⊆ W \ A := by
        intro t ht x hx
        have hxt : x ∈ keepUnion rs := keep_subset_keepUnion ht hx
        exact Finset.mem_sdiff.mpr ⟨hsubtail t ht hx,
          fun hxA => Finset.disjoint_left.mp hArest hxA hxt⟩
      have hroomtail : capacityTotal rs ≤ (W \ A).card := by
        have hc := Finset.card_sdiff_add_card_eq_card hAW
        omega
      obtain ⟨tail, htail, htaildisj⟩ := ih (W \ A) hrestsub' hcpt hpairs.2 hroomtail
      have htail_subset : ∀ B ∈ tail, B ⊆ W \ A := forall2_selected_subset htail
      refine ⟨A :: tail, ?_, ?_⟩
      · apply List.Forall₂.cons
        · exact ⟨hkeepA, hAW, hAcard⟩
        · exact htail.imp (fun _ _ h => ⟨h.1, h.2.1.trans Finset.sdiff_subset, h.2.2⟩)
      · apply List.pairwise_cons.mpr
        refine ⟨?_, htaildisj⟩
        intro B hB
        have hBw : B ⊆ W \ A := htail_subset B hB
        exact Finset.disjoint_left.mpr (by
          intro x hxA hxB
          exact (Finset.mem_sdiff.mp (hBw hxB)).2 hxA)

omit [DecidableEq α] in
theorem capacityTotal_eq_sum (rs : List (Request α)) :
    capacityTotal rs = (rs.map Request.capacity).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [capacityTotal, ih]

/-- Indexed form: actual pairwise-disjoint sets with each protected raw
inventory retained and exact capacities; usable for layers or colour pools. -/
theorem exists_indexed_protected_allocation (n : ℕ) (W : Finset α)
    (keep : Fin n → Finset α) (cap : Fin n → ℕ)
    (hsub : ∀ i, keep i ⊆ W)
    (hcap : ∀ i, (keep i).card ≤ cap i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (keep i) (keep j))
    (hroom : (∑ i, cap i) ≤ W.card) :
    ∃ chosen : Fin n → Finset α,
      (∀ i, keep i ⊆ chosen i ∧ chosen i ⊆ W ∧ (chosen i).card = cap i) ∧
      (∀ i j, i ≠ j → Disjoint (chosen i) (chosen j)) := by
  let requests : List (Request α) := List.ofFn (fun i => ⟨keep i, cap i⟩)
  have hrsub : ∀ r ∈ requests, r.keep ⊆ W := by
    intro r hr
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hr
    subst r
    exact hsub i
  have hrcap : ∀ r ∈ requests, r.keep.card ≤ r.capacity := by
    intro r hr
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hr
    subst r
    exact hcap i
  have hrdisj : requests.Pairwise (fun r t => Disjoint r.keep t.keep) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact hdisj i j (ne_of_lt hij)
  have hrtotal : capacityTotal requests = ∑ i, cap i := by
    rw [capacityTotal_eq_sum]
    simp [requests, List.map_ofFn, List.sum_ofFn]
  obtain ⟨out, hout, hpairs⟩ :=
    exists_protected_allocation W requests hrsub hrcap hrdisj (by simpa [hrtotal] using hroom)
  have hlen : out.length = n := by
    have h := hout.length_eq
    simpa [requests] using h.symm
  let chosen (i : Fin n) : Finset α := out.get ⟨i.val, by simpa [hlen] using i.isLt⟩
  refine ⟨chosen, ?_, ?_⟩
  · intro i
    have h := hout.get (i := i.val) (by simpa [requests] using i.isLt)
      (by simpa [hlen] using i.isLt)
    simpa [requests, chosen, List.get_eq_getElem] using h
  · intro i j hij
    have hpair := List.pairwise_iff_get.mp hpairs
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact hpair ⟨i.val, by simpa [hlen] using i.isLt⟩
        ⟨j.val, by simpa [hlen] using j.isLt⟩ hijlt
    · exact (hpair ⟨j.val, by simpa [hlen] using j.isLt⟩
        ⟨i.val, by simpa [hlen] using i.isLt⟩ hjilt).symm

/-- A protected allocation has exactly the expected number of unused
elements, since its chosen sets are actually pairwise disjoint. -/
theorem exists_indexed_protected_allocation_with_remainder
    (n : ℕ) (W : Finset α) (keep : Fin n → Finset α) (cap : Fin n → ℕ)
    (hsub : ∀ i, keep i ⊆ W)
    (hcap : ∀ i, (keep i).card ≤ cap i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (keep i) (keep j))
    (hroom : (∑ i, cap i) ≤ W.card) :
    ∃ chosen : Fin n → Finset α,
      (∀ i, keep i ⊆ chosen i ∧ chosen i ⊆ W ∧ (chosen i).card = cap i) ∧
      (∀ i j, i ≠ j → Disjoint (chosen i) (chosen j)) ∧
      (W \ Finset.univ.biUnion chosen).card + (∑ i, cap i) = W.card := by
  obtain ⟨chosen, hchosen, hpair⟩ :=
    exists_indexed_protected_allocation n W keep cap hsub hcap hdisj hroom
  have hsub' : Finset.univ.biUnion chosen ⊆ W := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact (hchosen i).2.1 hi
  have hpair' : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint chosen := by
    intro i _ j _ hij
    exact hpair i j hij
  have hcard : (Finset.univ.biUnion chosen).card = ∑ i, cap i := by
    rw [Finset.card_biUnion hpair']
    apply Finset.sum_congr rfl
    intro i _
    exact (hchosen i).2.2
  refine ⟨chosen, hchosen, hpair, ?_⟩
  rw [← hcard]
  exact Finset.card_sdiff_add_card_eq_card hsub'

/-- If all raw elements that remain eligible were protected, raw loss can
only come from outside the target or from the explicitly blocked set. -/
theorem raw_loss_le_missing_and_blocked (raw W blocked chosen : Finset α)
    (hkeep : raw ∩ (W \ blocked) ⊆ chosen) :
    (raw \ chosen).card ≤ (raw \ W).card + (raw ∩ blocked).card := by
  have hsub : raw \ chosen ⊆ (raw \ W) ∪ (raw ∩ blocked) := by
    intro x hx
    obtain ⟨hraw, hnot⟩ := Finset.mem_sdiff.mp hx
    by_cases hw : x ∈ W
    · apply Finset.mem_union_right
      refine Finset.mem_inter.mpr ⟨hraw, ?_⟩
      by_contra hblocked
      exact hnot (hkeep (Finset.mem_inter.mpr ⟨hraw, Finset.mem_sdiff.mpr ⟨hw, hblocked⟩⟩))
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hraw, hw⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

end EndpointFactor.Allocation
