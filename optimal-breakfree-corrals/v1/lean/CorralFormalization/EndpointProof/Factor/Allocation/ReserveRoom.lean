import CorralFormalization.EndpointProof.Factor.Allocation.ForcedFamily

/-! # Paying simultaneous special-layer capacity from the actual reserve -/

open scoped BigOperators Classical
namespace EndpointFactor.Allocation
variable {α : Type*} [DecidableEq α]

/-- The carrier contains all eligible special raw roles and all eligible
reserve points. Their actual disjointness turns their cardinals into room. -/
theorem forcedCarrier_room_of_disjoint_reserve (n : ℕ)
    (raw forced : Fin n → Finset α) (W reserve : Finset α) (cap : Fin n → ℕ)
    (hraw : ∀ i j, i ≠ j → Disjoint (raw i) (raw j))
    (hreserve : ∀ i, Disjoint (raw i) reserve)
    (hroom : (∑ i, cap i) ≤ (∑ i, (raw i ∩ W).card) + (reserve ∩ W).card) :
    (∑ i, cap i) ≤ (forcedCarrier raw forced W reserve).card := by
  have hpair : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun i => raw i ∩ W) := by
    intro i _ j _ hij
    exact (hraw i j hij).mono Finset.inter_subset_left Finset.inter_subset_left
  have hrawcard : (rawEligibleUnion raw W).card = ∑ i, (raw i ∩ W).card := by
    exact Finset.card_biUnion hpair
  have hsep : Disjoint (rawEligibleUnion raw W) (reserve ∩ W) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact Finset.disjoint_left.mp (hreserve i) (Finset.mem_inter.mp hi).1
      (Finset.mem_inter.mp hy).1
  have hunion : ((rawEligibleUnion raw W) ∪ (reserve ∩ W)).card =
      (∑ i, (raw i ∩ W).card) + (reserve ∩ W).card := by
    rw [Finset.card_union_of_disjoint hsep, hrawcard]
  have hsub : (rawEligibleUnion raw W ∪ (reserve ∩ W)) ⊆
      forcedCarrier raw forced W reserve := Finset.subset_union_left
  have hc := Finset.card_le_card hsub
  rw [hunion] at hc
  exact hroom.trans hc

/-- A uniform deficit `a` per special role is paid if the actual eligible
reserve contains at least `n*a` points. The inequalities use real numbers,
matching the manuscript's `s` and `d`; the conclusion is an exact integer
capacity inequality. -/
theorem special_capacity_from_deficits (n : ℕ) (raw : Fin n → Finset α)
    (W reserve : Finset α) (cap : Fin n → ℕ) (a : ℝ)
    (hdef : ∀ i, (cap i : ℝ) ≤ ((raw i ∩ W).card : ℝ) + a)
    (hreserve : (n : ℝ) * a ≤ ((reserve ∩ W).card : ℝ)) :
    (∑ i, cap i) ≤ (∑ i, (raw i ∩ W).card) + (reserve ∩ W).card := by
  have hsum : (∑ i, (cap i : ℝ)) ≤ ∑ i, (((raw i ∩ W).card : ℝ) + a) :=
    Finset.sum_le_sum (fun i _ => hdef i)
  have hreal : ((∑ i, cap i : ℕ) : ℝ) ≤
      ((∑ i, (raw i ∩ W).card : ℕ) : ℝ) + ((reserve ∩ W).card : ℝ) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul, Nat.cast_sum, Nat.cast_add] at hsum ⊢
    linarith
  exact_mod_cast hreal

/-- A raw class whose size is within `s` of `q n` loses at most `d`
outside `W`; an intended size `q n - q d` therefore has deficit at most
`d+s` inside `W`. -/
theorem special_deficit_bound (raw W : Finset α) (capacity : ℕ) (q N d s : ℝ)
    (hq : 0 ≤ q) (hd : 0 ≤ d)
    (hraw : |(raw.card : ℝ) - q*N| ≤ s)
    (hcap : (capacity : ℝ) = q*N - q*d)
    (hmissing : ((raw \ W).card : ℝ) ≤ d) :
    (capacity : ℝ) ≤ ((raw ∩ W).card : ℝ) + (d+s) := by
  have hsplitNat := Finset.card_sdiff_add_card_inter raw W
  have hsplit : ((raw \ W).card : ℝ) + ((raw ∩ W).card : ℝ) = raw.card := by
    exact_mod_cast hsplitNat
  have hb := abs_le.mp hraw
  have hqd := mul_nonneg hq hd
  nlinarith [hb.1]

/-- The real reserve-size event and the same missing-point budget supply
`r N - s - d` actual eligible reserve points. -/
theorem eligible_reserve_lower (reserve W : Finset α) (r N d s : ℝ)
    (hreserve : |(reserve.card : ℝ) - r*N| ≤ s)
    (hmissing : ((reserve \ W).card : ℝ) ≤ d) :
    r*N-s-d ≤ ((reserve ∩ W).card : ℝ) := by
  have hsplitNat := Finset.card_sdiff_add_card_inter reserve W
  have hsplit : ((reserve \ W).card : ℝ) + ((reserve ∩ W).card : ℝ) = reserve.card := by
    exact_mod_cast hsplitNat
  have hb := abs_le.mp hreserve
  linarith [hb.1]

end EndpointFactor.Allocation
