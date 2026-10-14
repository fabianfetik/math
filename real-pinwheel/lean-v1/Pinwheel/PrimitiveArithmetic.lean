import Pinwheel.RationalWindows
import Mathlib.Tactic

/-!
# R186: arithmetic of one primitive ordinary-window promotion

Locally checked after R186 review (2026-09-20); see the R186 review.
No source-existence theorem is assumed by this module. All parameters remain universally quantified.
-/

namespace RealPinwheel.PrimitivePromotion

set_option maxHeartbeats 400000
set_option maxRecDepth 2000

/-- The positive, oriented predecessor hypotheses in the supplied T255 context.
The determinant is expressed without truncated natural subtraction. -/
structure PrimitivePair (a b p q : ℕ) : Prop where
  a_pos : 0 < a
  a_lt_b : a < b
  b_lt_q : b < q
  p_pos : 0 < p
  p_lt_q : p < q
  determinant : p * b = a * q + 1

variable {a b p q : ℕ}

theorem PrimitivePair.b_pos (h : PrimitivePair a b p q) : 0 < b := by
  classical
  have := h.a_pos
  have := h.a_lt_b
  omega

theorem PrimitivePair.q_pos (h : PrimitivePair a b p q) : 0 < q := by
  classical
  have := h.b_pos
  have := h.b_lt_q
  omega

theorem PrimitivePair.rate_lt (h : PrimitivePair a b p q) :
    (a : ℝ) / b < (p : ℝ) / q := by
  classical
  apply (div_lt_div_iff₀ (by exact_mod_cast h.b_pos)
    (by exact_mod_cast h.q_pos)).mpr
  exact_mod_cast (show a * q < p * b by have := h.determinant; omega)

/-- Integer deficit of an actual half-open bilateral service window. -/
noncomputable def deficit {α : Type*} (S : ℤ → α) (i : α)
    (a b : ℕ) (t : ℤ) (L : ℕ) : ℤ :=
  (a : ℤ) * L - (b : ℤ) * (serviceCount S i t (L : ℤ) : ℤ)

@[simp] theorem deficit_zero {α : Type*} (S : ℤ → α) (i : α)
    (a b : ℕ) (t : ℤ) : deficit S i a b t 0 = 0 := by
  classical
  simp [deficit]

theorem deficit_add {α : Type*} (S : ℤ → α) (i : α)
    (a b : ℕ) (t : ℤ) (L K : ℕ) :
    deficit S i a b t (L + K) =
      deficit S i a b t L + deficit S i a b (t + L) K := by
  classical
  unfold deficit
  rw [serviceCount_nat_add]
  push_cast
  ring

/-- Exact strict/closed endpoint conversion: `< b` is `≤ b-1`, not `≤ b`. -/
theorem rational_quota_iff_deficit (a b L N : ℕ) (hb : 0 < b) :
    (L : ℝ) * ((a : ℝ) / b) < (N : ℝ) + 1 ↔
      (a : ℤ) * L - (b : ℤ) * N ≤ (b : ℤ) - 1 := by
  classical
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  constructor
  · intro h
    have hm := (div_lt_iff₀ hbR).mp
      (show (L : ℝ) * a / b < (N : ℝ) + 1 by
        simpa only [mul_div_assoc] using h)
    have hr : (a : ℝ) * L - (b : ℝ) * N < b := by nlinarith
    have hz : (a : ℤ) * L - (b : ℤ) * N < b := by exact_mod_cast hr
    omega
  · intro h
    have hz : (a : ℤ) * L - (b : ℤ) * N < b := by omega
    have hr : (a : ℝ) * L - (b : ℝ) * N < b := by exact_mod_cast hz
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hbR).mpr
    nlinarith

theorem rateWindows_iff_deficit {α : Type*} (S : ℤ → α) (i : α)
    (a b : ℕ) (hb : 0 < b) :
    RateWindows S i ((a : ℝ) / b) ↔
      ∀ (t : ℤ) (L : ℕ), deficit S i a b t L ≤ (b : ℤ) - 1 := by
  classical
  constructor
  · intro h t L
    exact (rational_quota_iff_deficit a b L _ hb).mp (h t L)
  · intro h t L
    exact (rational_quota_iff_deficit a b L _ hb).mpr (h t L)

/-- The project's strict-real interface is precisely the original floor bound. -/
theorem rateWindows_iff_floor {α : Type*} (S : ℤ → α) (i : α) (r : ℝ) :
    RateWindows S i r ↔ ∀ (t : ℤ) (L : ℕ),
      ⌊(L : ℝ) * r⌋₊ ≤ serviceCount S i t (L : ℤ) := by
  classical
  constructor
  · intro h t L
    apply Nat.le_of_lt_succ
    exact (Nat.floor_lt' (Nat.succ_ne_zero _)).mpr (by simpa using h t L)
  · intro h t L
    have hc : (⌊(L : ℝ) * r⌋₊ : ℝ) ≤ serviceCount S i t (L : ℤ) := by
      exact_mod_cast h t L
    have hf := Nat.lt_floor_add_one ((L : ℝ) * r)
    linarith

/-- The short-window arithmetic uses only positivity and the determinant.
In particular it does not assume a bound on either numerator. -/
theorem short_deficit_transfer {a b p q L N : ℕ}
    (hb : 0 < b) (hq : 0 < q) (hdet : p * b = a * q + 1)
    (hL : L < q)
    (hbase : (a : ℤ) * L - (b : ℤ) * N ≤ (b : ℤ) - 1) :
    (p : ℤ) * L - (q : ℤ) * N ≤ (q : ℤ) - 1 := by
  classical
  have hbZ : (0 : ℤ) < b := by exact_mod_cast hb
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hLZ : (L : ℤ) < q := by exact_mod_cast hL
  have hd : (p : ℤ) * b - (a : ℤ) * q = 1 := by
    have hd' : (p : ℤ) * b = (a : ℤ) * q + 1 := by exact_mod_cast hdet
    omega
  have hw : 1 ≤ (b : ℤ) * ((N : ℤ) + 1) - (a : ℤ) * L := by
    nlinarith
  by_contra hn
  have hu : 0 ≤ (p : ℤ) * L - (q : ℤ) * ((N : ℤ) + 1) := by
    nlinarith
  have hwq := mul_le_mul_of_nonneg_left hw hqZ.le
  have hub := mul_nonneg hbZ.le hu
  have hid :
      (b : ℤ) * ((p : ℤ) * L - (q : ℤ) * ((N : ℤ) + 1)) +
      (q : ℤ) * ((b : ℤ) * ((N : ℤ) + 1) - (a : ℤ) * L) = L := by
    calc
      _ = ((p : ℤ) * b - (a : ℤ) * q) * L := by ring
      _ = L := by rw [hd]; ring
  nlinarith

theorem short_floor_eq (h : PrimitivePair a b p q) {L : ℕ} (hL : L < q) :
    ⌊(L : ℝ) * ((a : ℝ) / b)⌋₊ = ⌊(L : ℝ) * ((p : ℝ) / q)⌋₊ := by
  classical
  apply le_antisymm
  · exact Nat.floor_mono
      (mul_le_mul_of_nonneg_left h.rate_lt.le (Nat.cast_nonneg L))
  · let N := ⌊(L : ℝ) * ((a : ℝ) / b)⌋₊
    have hbnd := (rational_quota_iff_deficit a b L N h.b_pos).mp
      (Nat.lt_floor_add_one ((L : ℝ) * ((a : ℝ) / b)))
    have htarget := (rational_quota_iff_deficit p q L N h.q_pos).mpr
      (short_deficit_transfer h.b_pos h.q_pos h.determinant hL hbnd)
    exact Nat.le_of_lt_succ
      ((Nat.floor_lt' (Nat.succ_ne_zero N)).mpr (by simpa using htarget))

theorem primitive_quota_of_rateWindows {α : Type*} (S : ℤ → α) (i : α)
    (p q : ℕ) (hq : 0 < q) (h : RateWindows S i ((p : ℝ) / q))
    (t : ℤ) : p ≤ serviceCount S i t (q : ℤ) := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have he : (q : ℝ) * ((p : ℝ) / q) = p := by field_simp
  have hh := h t q
  rw [he] at hh
  have hn : p < serviceCount S i t (q : ℤ) + 1 := by exact_mod_cast hh
  omega

/-- The final denominator window plus the original predecessor, at every start,
is enough for every original rational window. -/
theorem rateWindows_of_primitive {α : Type*} (S : ℤ → α) (i : α)
    (h : PrimitivePair a b p q)
    (hbase : RateWindows S i ((a : ℝ) / b))
    (hcritical : ∀ t : ℤ, p ≤ serviceCount S i t (q : ℤ)) :
    RateWindows S i ((p : ℝ) / q) := by
  classical
  apply rateWindows_of_denominator S i p q h.q_pos
  intro t L hL
  by_cases he : L = q
  · subst L
    have hqR : (0 : ℝ) < q := by exact_mod_cast h.q_pos
    have hprod : (q : ℝ) * ((p : ℝ) / q) = p := by field_simp
    rw [hprod]
    have hc : (p : ℝ) ≤ serviceCount S i t (q : ℤ) := by
      exact_mod_cast hcritical t
    linarith
  · apply (rational_quota_iff_deficit p q L _ h.q_pos).mpr
    apply short_deficit_transfer h.b_pos h.q_pos h.determinant (by omega)
    exact (rational_quota_iff_deficit a b L _ h.b_pos).mp (hbase t L)

theorem rateWindows_iff_predecessor_primitive {α : Type*} (S : ℤ → α) (i : α)
    (h : PrimitivePair a b p q) :
    RateWindows S i ((p : ℝ) / q) ↔
      RateWindows S i ((a : ℝ) / b) ∧
      ∀ t : ℤ, p ≤ serviceCount S i t (q : ℤ) := by
  classical
  constructor
  · intro ht
    refine ⟨?_, primitive_quota_of_rateWindows S i p q h.q_pos ht⟩
    intro t L
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left h.rate_lt.le (Nat.cast_nonneg L)) (ht t L)
  · rintro ⟨hb, hq⟩
    exact rateWindows_of_primitive S i h hb hq

theorem failed_count_add_one {α : Type*} (S : ℤ → α) (i : α)
    (h : PrimitivePair a b p q) (hbase : RateWindows S i ((a : ℝ) / b))
    (t : ℤ) (hfail : serviceCount S i t (q : ℤ) < p) :
    serviceCount S i t (q : ℤ) + 1 = p := by
  classical
  have hd := (rateWindows_iff_deficit S i a b h.b_pos).mp hbase t q
  unfold deficit at hd
  have hbZ : (0 : ℤ) < b := by exact_mod_cast h.b_pos
  have hdet : (p : ℤ) * b = (a : ℤ) * q + 1 := by exact_mod_cast h.determinant
  have hp : p ≤ serviceCount S i t (q : ℤ) + 1 := by
    by_contra hn
    have hh : (serviceCount S i t (q : ℤ) : ℤ) + 2 ≤ p := by omega
    have hm := mul_le_mul_of_nonneg_left hh hbZ.le
    nlinarith
  omega

theorem failed_deficit_eq {α : Type*} (S : ℤ → α) (i : α)
    (h : PrimitivePair a b p q) (hbase : RateWindows S i ((a : ℝ) / b))
    (t : ℤ) (hfail : serviceCount S i t (q : ℤ) < p) :
    deficit S i a b t q = (b : ℤ) - 1 := by
  classical
  have hc := failed_count_add_one S i h hbase t hfail
  have hcZ : (serviceCount S i t (q : ℤ) : ℤ) + 1 = p := by exact_mod_cast hc
  have hdet : (p : ℤ) * b = (a : ℤ) * q + 1 := by exact_mod_cast h.determinant
  unfold deficit
  nlinarith

/-- Number of necessarily occupied slots on either side of a saturated window. -/
def boundaryLength (a b : ℕ) : ℕ := (b - 1) / (b - a)

theorem boundaryLength_budget (ha : 0 < a) (hab : a < b) :
    ((b : ℤ) - a) * (boundaryLength a b : ℤ) ≤ (b : ℤ) - 1 := by
  classical
  have hn : boundaryLength a b * (b - a) ≤ b - 1 :=
    Nat.div_mul_le_self (b - 1) (b - a)
  have hz : (boundaryLength a b : ℤ) * ((b - a : ℕ) : ℤ) ≤ ((b - 1 : ℕ) : ℤ) := by
    exact_mod_cast hn
  rw [Nat.cast_sub hab.le, Nat.cast_sub (by omega : 1 ≤ b)] at hz
  norm_num only [Nat.cast_one] at hz
  nlinarith

theorem boundaryLength_le (ha : 0 < a) (hab : a < b) :
    boundaryLength a b ≤ b - 1 := by
  classical
  have hn : boundaryLength a b * (b - a) ≤ b - 1 :=
    Nat.div_mul_le_self (b - 1) (b - a)
  have hm := Nat.mul_le_mul_left (boundaryLength a b) (by omega : 1 ≤ b - a)
  omega

/-- The density-neutral helper `1/(q*b)` never meets this sufficient deadline
in the positive oriented domain. This is a source-cost fact, not infeasibility. -/
theorem canonical_deadline_gt (h : PrimitivePair a b p q) :
    q + 2 * boundaryLength a b < q * b := by
  classical
  have hc := boundaryLength_le h.a_pos h.a_lt_b
  have hb : 2 ≤ b := by have := h.a_pos; have := h.a_lt_b; omega
  have hq : 3 ≤ q := by have := h.b_lt_q; omega
  have hcZ : (boundaryLength a b : ℤ) ≤ (b : ℤ) - 1 := by omega
  have hm := mul_pos (show (0 : ℤ) < (q : ℤ) - 2 by omega)
    (show (0 : ℤ) < (b : ℤ) - 1 by omega)
  have hh : (q : ℤ) + 2 * (boundaryLength a b : ℤ) < (q : ℤ) * b := by
    nlinarith
  exact_mod_cast hh

end RealPinwheel.PrimitivePromotion
