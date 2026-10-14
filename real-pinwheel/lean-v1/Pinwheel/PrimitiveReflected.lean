import Pinwheel.PrimitiveArithmetic

/-!
# R186: canonical bilateral reflected deficits

Locally checked after R186 review (2026-09-20); see the R186 review.
The canonical maximum is over an actually finite set of ATTAINED integer
suffix deficits. The proof does not assume a periodic source or a past reset.
-/

namespace RealPinwheel.PrimitivePromotion

set_option maxHeartbeats 400000
set_option maxRecDepth 2000

open Finset

variable {α : Type*} {a b p q : ℕ}

noncomputable def serviceBit (S : ℤ → α) (i : α) (t : ℤ) : ℤ := by
  classical
  exact if S t = i then 1 else 0

theorem serviceBit_nonneg (S : ℤ → α) (i : α) (t : ℤ) : 0 ≤ serviceBit S i t := by
  classical
  by_cases h : S t = i <;> simp [serviceBit, h]

theorem deficit_one (S : ℤ → α) (i : α) (a b : ℕ) (t : ℤ) :
    deficit S i a b t 1 = (a : ℤ) - (b : ℤ) * serviceBit S i t := by
  classical
  by_cases h : S t = i <;> simp [deficit, serviceBit, serviceCount_one_length, h]

/-- A path on the ACTUAL service indicator; no independently chosen marks. -/
structure ReflectedPath (S : ℤ → α) (i : α) (a b : ℕ) (Z : ℤ → ℤ) : Prop where
  nonneg : ∀ t, 0 ≤ Z t
  upper : ∀ t, Z t ≤ (b : ℤ) - 1
  step : ∀ t, Z (t + 1) = max 0 (Z t + a - (b : ℤ) * serviceBit S i t)

noncomputable def surplus (S : ℤ → α) (i : α) (a b : ℕ) (Z : ℤ → ℤ) (t : ℤ) : ℤ :=
  max 0 ((b : ℤ) * serviceBit S i t - Z t - a)

noncomputable def surplusSum (S : ℤ → α) (i : α) (a b : ℕ) (Z : ℤ → ℤ)
    (t : ℤ) (L : ℕ) : ℤ :=
  (range L).sum fun k => surplus S i a b Z (t + k)

theorem surplus_nonneg (S : ℤ → α) (i : α) (a b : ℕ) (Z : ℤ → ℤ) (t : ℤ) :
    0 ≤ surplus S i a b Z t := le_max_left _ _

theorem surplusSum_nonneg (S : ℤ → α) (i : α) (a b : ℕ) (Z : ℤ → ℤ)
    (t : ℤ) (L : ℕ) : 0 ≤ surplusSum S i a b Z t L :=
  sum_nonneg fun k _ => surplus_nonneg S i a b Z (t + k)

@[simp] theorem surplusSum_zero (S : ℤ → α) (i : α) (a b : ℕ) (Z : ℤ → ℤ)
    (t : ℤ) : surplusSum S i a b Z t 0 = 0 := by simp [surplusSum]

theorem surplusSum_succ (S : ℤ → α) (i : α) (a b : ℕ) (Z : ℤ → ℤ)
    (t : ℤ) (L : ℕ) :
    surplusSum S i a b Z t (L + 1) =
      surplusSum S i a b Z t L + surplus S i a b Z (t + L) := by
  classical
  simp [surplusSum, sum_range_succ]

theorem reflection_balance (z x y : ℤ) :
    max 0 (z + x - y) = z + x - y + max 0 (y - z - x) := by
  classical
  by_cases h : 0 ≤ z + x - y
  · rw [max_eq_right h, max_eq_left (by omega)]
    omega
  · rw [max_eq_left (by omega), max_eq_right (by omega)]
    omega

theorem ReflectedPath.step_with_surplus {S : ℤ → α} {i : α} {Z : ℤ → ℤ}
    (h : ReflectedPath S i a b Z) (t : ℤ) :
    Z (t + 1) = Z t + a - (b : ℤ) * serviceBit S i t + surplus S i a b Z t := by
  classical
  rw [h.step, reflection_balance]
  rfl

theorem ReflectedPath.telescope {S : ℤ → α} {i : α} {Z : ℤ → ℤ}
    (h : ReflectedPath S i a b Z) (t : ℤ) (L : ℕ) :
    Z (t + L) - Z t = deficit S i a b t L + surplusSum S i a b Z t L := by
  classical
  induction L with
  | zero => simp
  | succ L ih =>
    have hs := h.step_with_surplus (t + L)
    have he : t + ((L + 1 : ℕ) : ℤ) = (t + L) + 1 := by omega
    rw [he, deficit_add, deficit_one, surplusSum_succ]
    omega

/-- Every legal reflected path supplies the ORIGINAL ordinary predecessor. -/
theorem ReflectedPath.ordinary {S : ℤ → α} {i : α} {Z : ℤ → ℤ}
    (h : ReflectedPath S i a b Z) (hb : 0 < b) : RateWindows S i ((a : ℝ) / b) := by
  classical
  apply (rateWindows_iff_deficit S i a b hb).mpr
  intro t L
  have ht := h.telescope t L
  have hlo := h.nonneg t
  have hhi := h.upper (t + L)
  have hs := surplusSum_nonneg S i a b Z t L
  omega

theorem surplusSum_eq_zero_iff (S : ℤ → α) (i : α) (a b : ℕ) (Z : ℤ → ℤ)
    (t : ℤ) (L : ℕ) :
    surplusSum S i a b Z t L = 0 ↔
      ∀ k : ℕ, k < L → surplus S i a b Z (t + k) = 0 := by
  classical
  induction L with
  | zero => simp
  | succ L ih =>
    rw [surplusSum_succ]
    constructor
    · intro he k hk
      have hs := surplusSum_nonneg S i a b Z t L
      have hl := surplus_nonneg S i a b Z (t + L)
      have heS : surplusSum S i a b Z t L = 0 := by omega
      have heL : surplus S i a b Z (t + L) = 0 := by omega
      by_cases hkL : k = L
      · subst k; exact heL
      · exact ih.mp heS k (by omega)
    · intro hz
      have heS := ih.mpr (fun k hk => hz k (by omega))
      have heL := hz L (by omega)
      omega

theorem ReflectedPath.positive_surplus_service_reset {S : ℤ → α} {i : α} {Z : ℤ → ℤ}
    (h : ReflectedPath S i a b Z) (t : ℤ) (hp : 0 < surplus S i a b Z t) :
    S t = i ∧ Z (t + 1) = 0 := by
  classical
  have harg : 0 < (b : ℤ) * serviceBit S i t - Z t - a := by
    by_contra hn
    have he : surplus S i a b Z t = 0 := max_eq_left (by omega)
    omega
  have hserved : S t = i := by
    by_contra hn
    have hb0 : serviceBit S i t = 0 := by simp [serviceBit, hn]
    rw [hb0, mul_zero] at harg
    have hz := h.nonneg t
    have ha : (0 : ℤ) ≤ a := Nat.cast_nonneg a
    omega
  refine ⟨hserved, ?_⟩
  rw [h.step, max_eq_left (by omega)]

/-- Extreme zero-surplus excursion, with all physical slots retained. -/
theorem ReflectedPath.failed_iff_extreme {S : ℤ → α} {i : α} {Z : ℤ → ℤ}
    (hp : PrimitivePair a b p q) (h : ReflectedPath S i a b Z) (t : ℤ) :
    serviceCount S i t (q : ℤ) < p ↔
      Z t = 0 ∧ Z (t + q) = (b : ℤ) - 1 ∧
      ∀ k : ℕ, k < q → surplus S i a b Z (t + k) = 0 := by
  classical
  have ht := h.telescope t q
  have hs := surplusSum_nonneg S i a b Z t q
  have hlo := h.nonneg t
  have hhi := h.upper (t + q)
  constructor
  · intro hf
    have hd := failed_deficit_eq S i hp (h.ordinary hp.b_pos) t hf
    have hz : Z t = 0 := by omega
    have he : Z (t + q) = (b : ℤ) - 1 := by omega
    have hsum : surplusSum S i a b Z t q = 0 := by omega
    exact ⟨hz, he, (surplusSum_eq_zero_iff S i a b Z t q).mp hsum⟩
  · rintro ⟨hz, he, hzero⟩
    have hsum := (surplusSum_eq_zero_iff S i a b Z t q).mpr hzero
    have hd : deficit S i a b t q = (b : ℤ) - 1 := by omega
    have hbZ : (0 : ℤ) < b := by exact_mod_cast hp.b_pos
    have hdet : (p : ℤ) * b = (a : ℤ) * q + 1 := by exact_mod_cast hp.determinant
    by_contra hn
    have hc : (p : ℤ) ≤ (serviceCount S i t (q : ℤ) : ℤ) := by omega
    have hm := mul_le_mul_of_nonneg_left hc hbZ.le
    unfold deficit at hd
    nlinarith

/-- A positive surplus is a strict event. Merely attaining state zero is not
substituted for it. The clock is on this same path. -/
theorem ReflectedPath.promotion_of_positive_clock {S : ℤ → α} {i : α} {Z : ℤ → ℤ}
    (hp : PrimitivePair a b p q) (h : ReflectedPath S i a b Z)
    (hclock : ∀ t : ℤ, ∃ k : ℕ, k < q ∧ 0 < surplus S i a b Z (t + k)) :
    RateWindows S i ((p : ℝ) / q) := by
  classical
  apply rateWindows_of_primitive S i hp (h.ordinary hp.b_pos)
  intro t
  by_contra hn
  have hf : serviceCount S i t (q : ℤ) < p := by omega
  obtain ⟨_, _, hz⟩ := (h.failed_iff_extreme hp t).mp hf
  obtain ⟨k, hk, hpos⟩ := hclock t
  have he := hz k hk
  omega

/-- All-window surplus lifting at arbitrary quota levels. The quantitative
surplus premise is an actual temporal bound, not a mean-rate bound. -/
theorem ReflectedPath.lift_of_surplus_windows {S : ℤ → α} {i : α} {Z : ℤ → ℤ}
    (h : ReflectedPath S i a b Z) (hb : 0 < b) (r : ℝ)
    (hclock : ∀ (t : ℤ) (L : ℕ),
      (⌊(L : ℝ) * r⌋₊ : ℤ) ≤ surplusSum S i a b Z t L) :
    RateWindows S i ((a : ℝ) / b + r / b) := by
  classical
  intro t L
  have ht := h.telescope t L
  have hlo := h.nonneg t
  have hhi := h.upper (t + L)
  have hc := hclock t L
  have hd : deficit S i a b t L + (⌊(L : ℝ) * r⌋₊ : ℤ) ≤ (b : ℤ) - 1 := by
    omega
  unfold deficit at hd
  have hdR : (a : ℝ) * L - (b : ℝ) * serviceCount S i t (L : ℤ) +
      (⌊(L : ℝ) * r⌋₊ : ℝ) ≤ (b : ℝ) - 1 := by exact_mod_cast hd
  have hf := Nat.lt_floor_add_one ((L : ℝ) * r)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [← add_div, ← mul_div_assoc]
  apply (div_lt_iff₀ hbR).mpr
  nlinarith

/-- Nonnegative attained suffix values suffice: zero is always an actual suffix,
and an ordinary source bounds every positive suffix by b-1. -/
noncomputable def pastStates (S : ℤ → α) (i : α) (a b : ℕ) (t : ℤ) : Finset ℤ := by
  classical
  exact (Icc 0 ((b : ℤ) - 1)).filter fun z =>
    ∃ L : ℕ, z = deficit S i a b (t - L) L

theorem zero_mem_pastStates (S : ℤ → α) (i : α) (a b : ℕ) (hb : 0 < b) (t : ℤ) :
    0 ∈ pastStates S i a b t := by
  classical
  apply mem_filter.mpr
  refine ⟨mem_Icc.mpr ⟨le_rfl, by omega⟩, 0, ?_⟩
  simp

noncomputable def canonical (S : ℤ → α) (i : α) (a b : ℕ) (hb : 0 < b)
    (t : ℤ) : ℤ :=
  (pastStates S i a b t).max' ⟨0, zero_mem_pastStates S i a b hb t⟩

theorem canonical_mem (S : ℤ → α) (i : α) (a b : ℕ) (hb : 0 < b) (t : ℤ) :
    canonical S i a b hb t ∈ pastStates S i a b t :=
  max'_mem _ _

theorem canonical_bounds (S : ℤ → α) (i : α) (a b : ℕ) (hb : 0 < b) (t : ℤ) :
    0 ≤ canonical S i a b hb t ∧ canonical S i a b hb t ≤ (b : ℤ) - 1 := by
  classical
  have hm := canonical_mem S i a b hb t
  exact mem_Icc.mp (mem_filter.mp hm).1

theorem canonical_witness (S : ℤ → α) (i : α) (a b : ℕ) (hb : 0 < b) (t : ℤ) :
    ∃ L : ℕ, canonical S i a b hb t = deficit S i a b (t - L) L := by
  classical
  have hm := canonical_mem S i a b hb t
  exact (mem_filter.mp hm).2

/-- Domination includes ALL suffixes, not just those in the finite definition. -/
theorem canonical_dominates (S : ℤ → α) (i : α) (a b : ℕ) (hb : 0 < b)
    (hbase : RateWindows S i ((a : ℝ) / b)) (t : ℤ) (L : ℕ) :
    deficit S i a b (t - L) L ≤ canonical S i a b hb t := by
  classical
  by_cases hn : 0 ≤ deficit S i a b (t - L) L
  · have hu := (rateWindows_iff_deficit S i a b hb).mp hbase (t - L) L
    have hm : deficit S i a b (t - L) L ∈ pastStates S i a b t :=
      mem_filter.mpr ⟨mem_Icc.mpr ⟨hn, hu⟩, L, rfl⟩
    exact le_max' _ _ hm
  · exact (le_of_lt (lt_of_not_ge hn)).trans (canonical_bounds S i a b hb t).1

/-- The same maximum, stated with arbitrary integer left endpoints u<=t. -/
theorem canonical_dominates_interval (S : ℤ → α) (i : α) (a b : ℕ) (hb : 0 < b)
    (hbase : RateWindows S i ((a : ℝ) / b)) (u t : ℤ) (hut : u ≤ t) :
    (a : ℤ) * (t - u) - (b : ℤ) * (serviceCount S i u (t - u) : ℤ) ≤
      canonical S i a b hb t := by
  classical
  have he : ((t - u).toNat : ℤ) = t - u := Int.toNat_of_nonneg (by omega)
  have hs : t - ((t - u).toNat : ℤ) = u := by omega
  have hd := canonical_dominates S i a b hb hbase t (t - u).toNat
  unfold deficit at hd
  rw [hs, he] at hd
  exact hd

/-- Empty suffix versus an appended nonempty suffix gives the reflected update. -/
theorem canonical_step (S : ℤ → α) (i : α) (a b : ℕ) (hb : 0 < b)
    (hbase : RateWindows S i ((a : ℝ) / b)) (t : ℤ) :
    canonical S i a b hb (t + 1) =
      max 0 (canonical S i a b hb t + a - (b : ℤ) * serviceBit S i t) := by
  classical
  have hlower : canonical S i a b hb t + a - (b : ℤ) * serviceBit S i t ≤
      canonical S i a b hb (t + 1) := by
    obtain ⟨L, hL⟩ := canonical_witness S i a b hb t
    have hd := canonical_dominates S i a b hb hbase (t + 1) (L + 1)
    have hs : (t + 1) - ((L + 1 : ℕ) : ℤ) = t - L := by omega
    rw [hs, deficit_add, deficit_one, sub_add_cancel] at hd
    omega
  apply le_antisymm
  · obtain ⟨L, hL⟩ := canonical_witness S i a b hb (t + 1)
    cases L with
    | zero =>
      simp only [Nat.cast_zero, sub_zero, deficit_zero] at hL
      rw [hL]
      exact le_max_left _ _
    | succ L =>
      have hs : (t + 1) - ((L + 1 : ℕ) : ℤ) = t - L := by omega
      rw [hs, deficit_add, deficit_one, sub_add_cancel] at hL
      have hd := canonical_dominates S i a b hb hbase t L
      have he : canonical S i a b hb (t + 1) ≤
          canonical S i a b hb t + a - (b : ℤ) * serviceBit S i t := by omega
      exact he.trans (le_max_right _ _)
  · exact max_le (canonical_bounds S i a b hb (t + 1)).1 hlower

theorem canonical_reflected (S : ℤ → α) (i : α) (a b : ℕ) (hb : 0 < b)
    (hbase : RateWindows S i ((a : ℝ) / b)) :
    ReflectedPath S i a b (canonical S i a b hb) :=
  ⟨fun t => (canonical_bounds S i a b hb t).1,
    fun t => (canonical_bounds S i a b hb t).2,
    canonical_step S i a b hb hbase⟩

theorem canonical_failed_iff (S : ℤ → α) (i : α)
    (h : PrimitivePair a b p q) (hbase : RateWindows S i ((a : ℝ) / b)) (t : ℤ) :
    serviceCount S i t (q : ℤ) < p ↔
      canonical S i a b h.b_pos t = 0 ∧
      canonical S i a b h.b_pos (t + q) = (b : ℤ) - 1 ∧
      ∀ k : ℕ, k < q → surplus S i a b (canonical S i a b h.b_pos) (t + k) = 0 :=
  (canonical_reflected S i a b h.b_pos hbase).failed_iff_extreme h t

end RealPinwheel.PrimitivePromotion
