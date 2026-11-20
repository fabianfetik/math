import CorralFormalization.Results.SwitchFamily.Counting.CyclicWords

/-!
# Exact Burnside formula for the abstract decorated layout action

The quotient in `cyclicOrbitCount` is the actual quotient of marked words by
phase translation.  No physical-partition injection or equivariance is
assumed or asserted here.
-/

namespace CorralFormalization.Results.SwitchFamily.Counting

open Finset

/-- A nondependent version of the positive-period count. Its value at zero
is unused in every divisor formula below. -/
noncomputable def C (j : ℕ) : ℕ := Nat.card (Layout j)

theorem C_eq_layoutCount (j : ℕ) [NeZero j] : C j = layoutCount j :=
  Nat.card_eq_fintype_card

@[simp] theorem C_one : C 1 = 0 := by rw [C_eq_layoutCount, layoutCount_one]
@[simp] theorem C_two : C 2 = 2 := by rw [C_eq_layoutCount, layoutCount_two]
@[simp] theorem C_three : C 3 = 3 := by rw [C_eq_layoutCount, layoutCount_three]
@[simp] theorem C_four : C 4 = 2 := by rw [C_eq_layoutCount, layoutCount_four]
@[simp] theorem C_five : C 5 = 5 := by rw [C_eq_layoutCount, layoutCount_five]

theorem decorated_natCard (h Q : ℕ) [NeZero h] :
    Nat.card (DecoratedLayout h Q) = C h * Q^h := by
  rw [Nat.card_eq_fintype_card, decorated_card, C_eq_layoutCount]

theorem decorated_fixed_natCard (h Q : ℕ) [NeZero h] (t : ZMod h) :
    Nat.card (AddAction.fixedBy (DecoratedLayout h Q) t) =
      C (Nat.gcd h t.val) * Q^(Nat.gcd h t.val) := by
  classical
  letI : NeZero (Nat.gcd h t.val) :=
    ⟨Nat.ne_of_gt (Nat.gcd_pos_of_pos_left t.val (NeZero.pos h))⟩
  have ht := decorated_fixed_card h Q t.val
  rw [ZMod.natCast_zmod_val] at ht
  change Nat.card {u : DecoratedLayout h Q // t +ᵥ u = u} = _
  rw [Nat.card_eq_fintype_card, C_eq_layoutCount]
  exact ht

/-- Exactly the genuine cyclic orbits, retaining all stabilizer sizes. -/
noncomputable def cyclicOrbitCount (h Q : ℕ) : ℕ :=
  Nat.card (Quotient (AddAction.orbitRel (ZMod h) (DecoratedLayout h Q)))

theorem burnside_gcd (h Q : ℕ) [NeZero h] :
    cyclicOrbitCount h Q * h =
      ∑ t : ZMod h, C (Nat.gcd h t.val) * Q^(Nat.gcd h t.val) := by
  rw [cyclicOrbitCount, LocalWord.orbit_card_mul]
  exact Finset.sum_congr rfl fun t _ => decorated_fixed_natCard h Q t

/-- The number of cycles of translation by t is gcd(h,t), equivalently
h divided by its additive order. -/
theorem gcd_eq_div_addOrderOf {h : ℕ} [NeZero h] (t : ZMod h) :
    Nat.gcd h t.val = h / addOrderOf t := by
  have ht : addOrderOf t = h / Nat.gcd h t.val := by
    simpa using ZMod.addOrderOf_coe t.val (NeZero.ne h)
  rw [ht, Nat.div_div_self (Nat.gcd_dvd_left h t.val) (NeZero.ne h)]

/-- A proved totient regrouping of the actual h rotations. -/
theorem rotation_sum_totient {h : ℕ} [NeZero h] (F : ℕ → ℕ) :
    (∑ t : ZMod h, F (Nat.gcd h t.val)) =
      ∑ d ∈ h.divisors, Nat.totient d * F (h/d) := by
  classical
  simp_rw [gcd_eq_div_addOrderOf]
  have hmap : ∀ t ∈ (Finset.univ : Finset (ZMod h)), addOrderOf t ∈ h.divisors := by
    intro t _
    apply Nat.mem_divisors.mpr
    exact ⟨by simpa using (addOrderOf_dvd_card (x := t)), NeZero.ne h⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun t : ZMod h => F (h / addOrderOf t))]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ Fintype.card (ZMod h) := by
    simpa using (Nat.mem_divisors.mp hd).1
  calc
    (∑ t ∈ Finset.univ with addOrderOf t = d, F (h / addOrderOf t)) =
        ∑ _t ∈ Finset.univ with addOrderOf _t = d, F (h/d) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(Finset.mem_filter.mp ht).2]
    _ = Nat.totient d * F (h/d) := by
      rw [Finset.sum_const, IsAddCyclic.card_addOrderOf_eq_totient hdvd, nsmul_eq_mul]
      simp

/-- Formula (A9) for the abstract decorated directed 2/3 layouts. -/
theorem burnside_totient_mul (h Q : ℕ) [NeZero h] :
    cyclicOrbitCount h Q * h =
      ∑ d ∈ h.divisors, Nat.totient d * C (h/d) * Q^(h/d) := by
  rw [burnside_gcd, rotation_sum_totient (fun j => C j * Q^j)]
  simp only [mul_assoc]

theorem burnside_totient (h Q : ℕ) [NeZero h] :
    cyclicOrbitCount h Q =
      (∑ d ∈ h.divisors, Nat.totient d * C (h/d) * Q^(h/d)) / h := by
  rw [← burnside_totient_mul]
  exact (Nat.mul_div_cancel _ (NeZero.pos h)).symm

/-- A fixed point count is zero for every rotation with gcd period one,
regardless of the decoration alphabet. -/
theorem no_fixed_of_coprime (h Q : ℕ) [NeZero h] (t : ZMod h)
    (ht : Nat.Coprime h t.val) :
    Nat.card (AddAction.fixedBy (DecoratedLayout h Q) t) = 0 := by
  rw [decorated_fixed_natCard, ht.gcd_eq_one, C_one, zero_mul]

end CorralFormalization.Results.SwitchFamily.Counting
