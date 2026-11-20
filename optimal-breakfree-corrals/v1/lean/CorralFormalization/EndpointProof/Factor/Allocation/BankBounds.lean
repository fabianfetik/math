import CorralFormalization.EndpointProof.Factor.Allocation.CappedFamily

/-! # The actual closing-bank retention and edit inequalities -/

open scoped Classical symmDiff
namespace EndpointFactor.Allocation
noncomputable section
variable {α : Type*} [DecidableEq α]

/-- Bounds (6.5) from the literal capped-retention identity, including the
effect of leftover vertices and prescribed terminals on the bank capacity. -/
theorem capped_bank_explicit_bounds (raw D bank : Finset α) (capacity : ℕ)
    (q n d s w K : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hd : 0 ≤ d) (hs : 0 ≤ s) (hw : 0 ≤ w)
    (hbank : bank ⊆ D) (hcard : bank.card = capacity)
    (hinter : (raw ∩ bank).card = min (raw ∩ D).card capacity)
    (hraw : |(raw.card : ℝ) - q*n| ≤ s)
    (hcapacity : (capacity : ℝ) = q*n - q*d + w - K)
    (hmissing : ((raw \ D).card : ℝ) ≤ d-w+K) :
    ((raw \ bank).card : ℝ) ≤ d+s+K ∧
      ((raw ∆ bank).card : ℝ) ≤ (2+q)*d+s+K := by
  have hrawbounds := abs_le.mp hraw
  have hmiss0 : 0 ≤ ((raw \ D).card : ℝ) := Nat.cast_nonneg _
  have hsplitNat := Finset.card_sdiff_add_card_inter raw D
  have hsplit : ((raw \ D).card : ℝ) + ((raw ∩ D).card : ℝ) = raw.card := by
    exact_mod_cast hsplitNat
  have husedNat := Finset.card_sdiff_add_card_inter raw bank
  have hused : ((raw \ bank).card : ℝ) + ((raw ∩ bank).card : ℝ) = raw.card := by
    exact_mod_cast husedNat
  have hsymNat := symmDiff_card_balance raw bank
  have hsym : ((raw ∆ bank).card : ℝ) + 2*((raw ∩ bank).card : ℝ) =
      (raw.card : ℝ) + bank.card := by
    exact_mod_cast hsymNat
  have hqd : 0 ≤ q*d := mul_nonneg hq hd
  have hqdbound : q*d ≤ d := by nlinarith
  by_cases hsmall : (raw ∩ D).card ≤ capacity
  · rw [min_eq_left hsmall] at hinter
    have hintersection : ((raw ∩ bank).card : ℝ) = (raw ∩ D).card := by exact_mod_cast hinter
    have hbankcard : (bank.card : ℝ) = capacity := by exact_mod_cast hcard
    constructor <;> nlinarith [hrawbounds.1, hrawbounds.2]
  · have hlarge : capacity ≤ (raw ∩ D).card := le_of_not_ge hsmall
    rw [min_eq_right hlarge] at hinter
    have hintersection : ((raw ∩ bank).card : ℝ) = capacity := by exact_mod_cast hinter
    have hbankcard : (bank.card : ℝ) = capacity := by exact_mod_cast hcard
    constructor <;> nlinarith [hrawbounds.1, hrawbounds.2]

end
end EndpointFactor.Allocation
