import CorralFormalization.EndpointProof.Factor.Allocation.Protected
import Mathlib.Data.Finset.SymmDiff

/-!
# Capped retention and reserve filling

An actual special class, or the closing colour bank, retains as much of its
raw inventory as its target size allows and fills only from the given reserve.
-/

open scoped symmDiff
namespace EndpointFactor.Allocation

variable {α : Type*} [DecidableEq α]

/-- Exact edit-count balance for any two finite inventories. -/
theorem symmDiff_card_balance (raw chosen : Finset α) :
    (raw ∆ chosen).card + 2*(raw ∩ chosen).card = raw.card + chosen.card := by
  have hs1 := Finset.card_sdiff_add_card_inter raw chosen
  have hs2 := Finset.card_sdiff_add_card_inter chosen raw
  have hd : Disjoint (raw \ chosen) (chosen \ raw) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  rw [Finset.inter_comm chosen raw] at hs2
  omega

/-- Retain `min |raw ∩ target| capacity` actual raw elements, then fill from
the supplied reserve. The displayed edit identity is exact, not an upper
bound on an assumed number of changes. -/
theorem exists_capped_retain_fill (raw target reserve : Finset α) (capacity : ℕ)
    (hroom : capacity ≤ ((raw ∩ target) ∪ (reserve ∩ target)).card) :
    ∃ chosen : Finset α,
      chosen ⊆ target ∧ chosen.card = capacity ∧
      chosen \ raw ⊆ reserve ∩ target ∧
      (raw ∩ chosen).card = min (raw ∩ target).card capacity ∧
      (raw ∆ chosen).card + 2 * min (raw ∩ target).card capacity = raw.card + capacity := by
  let available := raw ∩ target
  let space := available ∪ (reserve ∩ target)
  obtain ⟨kept, hkept, hkeptcard⟩ :=
    Finset.exists_subset_card_eq (Nat.min_le_left available.card capacity)
  have hkeptspace : kept ⊆ space := hkept.trans Finset.subset_union_left
  obtain ⟨chosen, hkeptchosen, hchosenspace, hchosencard⟩ :=
    Finset.exists_subsuperset_card_eq hkeptspace (by simpa [hkeptcard]) hroom
  have htarget : chosen ⊆ target := by
    intro x hx
    rcases Finset.mem_union.mp (hchosenspace hx) with h | h
    · exact (Finset.mem_inter.mp h).2
    · exact (Finset.mem_inter.mp h).2
  have hfilled : chosen \ raw ⊆ reserve ∩ target := by
    intro x hx
    obtain ⟨hxchosen, hxraw⟩ := Finset.mem_sdiff.mp hx
    rcases Finset.mem_union.mp (hchosenspace hxchosen) with h | h
    · exact (hxraw (Finset.mem_inter.mp h).1).elim
    · exact h
  have hintersection : raw ∩ chosen = kept := by
    by_cases hsmall : available.card ≤ capacity
    · have hkeptall : kept = available := by
        apply Finset.eq_of_subset_of_card_le hkept
        rw [hkeptcard, min_eq_left hsmall]
      ext x
      constructor
      · intro hx
        obtain ⟨hxraw, hxchosen⟩ := Finset.mem_inter.mp hx
        rw [hkeptall]
        exact Finset.mem_inter.mpr ⟨hxraw, htarget hxchosen⟩
      · intro hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hkept hx)).1, hkeptchosen hx⟩
    · have hfull : chosen = kept := by
        symm
        apply Finset.eq_of_subset_of_card_le hkeptchosen
        rw [hchosencard, hkeptcard, min_eq_right (le_of_not_ge hsmall)]
      rw [hfull]
      exact Finset.inter_eq_right.mpr (hkept.trans Finset.inter_subset_left)
  have hintercard : (raw ∩ chosen).card = min (raw ∩ target).card capacity := by
    rw [hintersection, hkeptcard]
  have hs1 := Finset.card_sdiff_add_card_inter raw chosen
  have hs2 := Finset.card_sdiff_add_card_inter chosen raw
  have hd : Disjoint (raw \ chosen) (chosen \ raw) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hsym : (raw ∆ chosen).card = (raw \ chosen).card + (chosen \ raw).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  refine ⟨chosen, htarget, hchosencard, hfilled, hintercard, ?_⟩
  rw [hsym]
  rw [Finset.inter_comm chosen raw, hintercard, hchosencard] at hs2
  rw [hintercard] at hs1
  omega

/-- Exact capped symmetric-difference formula. The natural subtraction in the
second term is deliberately performed after adding the missing-point cost. -/
theorem capped_symmDiff_eq_max (raw target chosen : Finset α) (capacity : ℕ)
    (hcard : chosen.card = capacity)
    (hinter : (raw ∩ chosen).card = min (raw ∩ target).card capacity) :
    (raw ∆ chosen).card =
      max (raw.card - capacity) (capacity + 2 * (raw \ target).card - raw.card) := by
  have hmissing := Finset.card_sdiff_add_card_inter raw target
  have hs1 := Finset.card_sdiff_add_card_inter raw chosen
  have hs2 := Finset.card_sdiff_add_card_inter chosen raw
  have hd : Disjoint (raw \ chosen) (chosen \ raw) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hsym : (raw ∆ chosen).card = (raw \ chosen).card + (chosen \ raw).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  rw [Finset.inter_comm chosen raw, hinter, hcard] at hs2
  rw [hinter] at hs1
  by_cases hsmall : (raw ∩ target).card ≤ capacity
  · rw [min_eq_left hsmall] at hs1 hs2
    have hmax : raw.card - capacity ≤ capacity + 2 * (raw \ target).card - raw.card := by omega
    rw [max_eq_right hmax, hsym]
    omega
  · have hlarge : capacity ≤ (raw ∩ target).card := le_of_not_ge hsmall
    rw [min_eq_right hlarge] at hs1 hs2
    have hmax : capacity + 2 * (raw \ target).card - raw.card ≤ raw.card - capacity := by omega
    rw [max_eq_left hmax, hsym]
    omega

/-- Paper-style special-class edit bound from actual capped retention.
The raw mean, its tolerance, the target layer size, and the missing-point
budget are explicit and can be supplied by the common size event. -/
theorem capped_symmDiff_explicit_bound (raw target chosen : Finset α) (capacity : ℕ)
    (q n d s : ℝ) (hq : 0 ≤ q) (hd : 0 ≤ d) (hs : 0 ≤ s)
    (hcard : chosen.card = capacity)
    (hinter : (raw ∩ chosen).card = min (raw ∩ target).card capacity)
    (hraw : |(raw.card : ℝ) - q*n| ≤ s)
    (hcapacity : (capacity : ℝ) = q*n - q*d)
    (hmissing : ((raw \ target).card : ℝ) ≤ d) :
    ((raw ∆ chosen).card : ℝ) ≤ (2+q)*d+s := by
  have hr := (abs_le.mp hraw)
  have hsumNat := Finset.card_sdiff_add_card_inter raw target
  have hsum : ((raw \ target).card : ℝ) + ((raw ∩ target).card : ℝ) = raw.card := by
    exact_mod_cast hsumNat
  have hformula := capped_symmDiff_eq_max raw target chosen capacity hcard hinter
  have hqd : 0 ≤ q*d := mul_nonneg hq hd
  by_cases hsmall : (raw ∩ target).card ≤ capacity
  · have hmax : raw.card - capacity ≤ capacity + 2 * (raw \ target).card - raw.card := by
      omega
    rw [max_eq_right hmax] at hformula
    by_cases hnonneg : raw.card ≤ capacity + 2*(raw \ target).card
    · have hreal : ((raw ∆ chosen).card : ℝ) =
          (capacity : ℝ) + 2 * ((raw \ target).card : ℝ) - (raw.card : ℝ) := by
        rw [hformula, Nat.cast_sub hnonneg]
        push_cast
        rfl
      nlinarith [hr.1, hr.2]
    · have hzero : capacity + 2*(raw \ target).card - raw.card = 0 := by omega
      rw [hzero] at hformula
      have hzero' : ((raw ∆ chosen).card : ℝ) = 0 := by exact_mod_cast hformula
      nlinarith
  · have hlarge : capacity ≤ (raw ∩ target).card := le_of_not_ge hsmall
    have hmax : capacity + 2 * (raw \ target).card - raw.card ≤ raw.card - capacity := by
      omega
    rw [max_eq_left hmax] at hformula
    have hcapraw : capacity ≤ raw.card := by omega
    have hreal : ((raw ∆ chosen).card : ℝ) = (raw.card : ℝ) - capacity := by
      rw [hformula, Nat.cast_sub hcapraw]
    nlinarith [hr.1, hr.2]

theorem exists_capped_retain_fill_max (raw target reserve : Finset α) (capacity : ℕ)
    (hroom : capacity ≤ ((raw ∩ target) ∪ (reserve ∩ target)).card) :
    ∃ chosen : Finset α,
      chosen ⊆ target ∧ chosen.card = capacity ∧
      chosen \ raw ⊆ reserve ∩ target ∧
      (raw ∩ chosen).card = min (raw ∩ target).card capacity ∧
      (raw ∆ chosen).card =
        max (raw.card - capacity) (capacity + 2 * (raw \ target).card - raw.card) := by
  obtain ⟨chosen, hW, hcard, hfill, hinter, _⟩ :=
    exists_capped_retain_fill raw target reserve capacity hroom
  exact ⟨chosen, hW, hcard, hfill, hinter,
    capped_symmDiff_eq_max raw target chosen capacity hcard hinter⟩

end EndpointFactor.Allocation
