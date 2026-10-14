import Pinwheel.FiniteWindows
import Pinwheel.CyclicSplitting
import Mathlib.Data.Rat.Floor

/-!
# Finite generators for rational ordinary service

All predicates use the original ordinary window convention, including equality
faces. The denominator gives a finite set of test lengths; the sharper
numerator-indexed generator theorem is proved below.
-/

namespace RealPinwheel

open Finset
open scoped BigOperators

/-- The original all-window condition for a single label in a schedule. -/
def RateWindows {α : Type*} (S : ℤ → α) (i : α) (r : ℝ) : Prop :=
  ∀ (m : ℤ) (L : ℕ), (L : ℝ) * r < (serviceCount S i m (L : ℤ) : ℝ) + 1

/-- It suffices to check the lengths up to a denominator. No reduction or
coprimality premise on the displayed fraction is needed. -/
theorem rateWindows_of_denominator {α : Type*} (S : ℤ → α) (i : α)
    (p q : ℕ) (hq : 0 < q)
    (h : ∀ (m : ℤ) (L : ℕ), L ≤ q →
      (L : ℝ) * ((p : ℝ) / q) < (serviceCount S i m (L : ℤ) : ℝ) + 1) :
    RateWindows S i ((p : ℝ) / q) := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hblock (m : ℤ) : p ≤ serviceCount S i m (q : ℤ) := by
    have hh := h m q le_rfl
    have he : (q : ℝ) * ((p : ℝ) / q) = p := by field_simp
    rw [he] at hh
    have : (p : ℝ) < (serviceCount S i m (q : ℤ) + 1 : ℕ) := by
      exact_mod_cast hh
    exact Nat.le_of_lt_succ (by exact_mod_cast this)
  intro m L
  induction L using Nat.strong_induction_on generalizing m with
  | h L ih =>
    by_cases hL : L ≤ q
    · exact h m L hL
    · have hsub : L - q < L := by omega
      have hrest := ih (L - q) hsub (m + q)
      have hsum : L = q + (L - q) := by omega
      have hc := hblock m
      rw [hsum, serviceCount_nat_add]
      push_cast
      have hqmul : (q : ℝ) * ((p : ℝ) / q) = p := by field_simp
      have hcR : (p : ℝ) ≤ serviceCount S i m (q : ℤ) := by exact_mod_cast hc
      nlinarith

/-- The reduced numerator is bounded whenever a positive fraction has a
bounded displayed numerator. -/
theorem reducedNumerator_div_le (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    ((p : ℚ) / q).num.natAbs ≤ p := by
  rw [Rat.natCast_div_eq_divInt]
  have hd := Rat.num_dvd (p : ℤ) (show (q : ℤ) ≠ 0 by omega)
  have hd' := Int.natAbs_dvd_natAbs.mpr hd
  simp only [Int.natAbs_natCast] at hd'
  exact Nat.le_of_dvd hp hd'

/-- A positive rational's canonical numerator is its natural absolute value. -/
theorem positive_rat_cast (r : ℚ) (hr : 0 < r) :
    (r : ℝ) = (r.num.natAbs : ℝ) / r.den := by
  rw [Rat.cast_def]
  have hn := (Rat.num_pos.mpr hr).le
  rw [show (r.num.natAbs : ℝ) = (r.num : ℝ) by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hn)]

/-- Rounding down a positive real rate preserves every quota up to M, at
once, and produces a rational with reduced numerator at most M. -/
theorem exists_boundedNumerator_minorant (r : ℝ) (hr : 0 < r)
    (M : ℕ) (hM : 0 < M) :
    ∃ s : ℚ, 0 < s ∧ (s : ℝ) ≤ r ∧ s.num.natAbs ≤ M ∧
      ∀ L : ℕ, ⌊(L : ℝ) * r⌋₊ ≤ M →
        ⌊(L : ℝ) * (s : ℝ)⌋₊ = ⌊(L : ℝ) * r⌋₊ := by
  classical
  let den (k : ℕ) := ⌈(k : ℝ) / r⌉₊
  let f (k : ℕ) : ℚ := (k : ℚ) / den k
  have hd {k : ℕ} (hk : 0 < k) : 0 < den k :=
    Nat.ceil_pos.mpr (div_pos (by exact_mod_cast hk) hr)
  have hf {k : ℕ} (hk : 0 < k) : 0 < f k :=
    div_pos (by exact_mod_cast hk) (by exact_mod_cast hd hk)
  have hfle {k : ℕ} (hk : 0 < k) : (f k : ℝ) ≤ r := by
    have hh := Nat.le_ceil ((k : ℝ) / r)
    have hmul : (k : ℝ) ≤ r * den k := by
      exact (div_le_iff₀ hr).mp hh |>.trans_eq (mul_comm _ _)
    simp only [f, Rat.cast_div, Rat.cast_natCast]
    exact (div_le_iff₀ (by exact_mod_cast hd hk)).mpr hmul
  obtain ⟨k, hk, hmax⟩ := (Icc 1 M).exists_max_image f
    (by exact ⟨1, mem_Icc.mpr ⟨le_rfl, hM⟩⟩)
  have hkpos : 0 < k := (mem_Icc.mp hk).1
  refine ⟨f k, hf hkpos, hfle hkpos,
    (reducedNumerator_div_le k (den k) hkpos (hd hkpos)).trans (mem_Icc.mp hk).2, ?_⟩
  intro L hL
  apply le_antisymm
  · exact Nat.floor_mono (mul_le_mul_of_nonneg_left (hfle hkpos) (Nat.cast_nonneg L))
  · let j := ⌊(L : ℝ) * r⌋₊
    by_cases hj : j = 0
    · change j ≤ _
      rw [hj]
      exact Nat.zero_le _
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hjmem : j ∈ Icc 1 M := mem_Icc.mpr ⟨hjpos, hL⟩
    have hden : den j ≤ L := by
      apply Nat.ceil_le.mpr
      exact (div_le_iff₀ hr).mpr (Nat.floor_le (mul_nonneg (Nat.cast_nonneg L) hr.le))
    have hmaxR : (f j : ℝ) ≤ (f k : ℝ) := by exact_mod_cast hmax j hjmem
    have hprod : (j : ℝ) ≤ (L : ℝ) * (f j : ℝ) := by
      have he : (den j : ℝ) * (f j : ℝ) = j := by
        simp only [f, Rat.cast_div, Rat.cast_natCast]
        have hdR : (den j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hd hjpos)
        field_simp
      rw [← he]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hden)
        (by exact_mod_cast (hf hjpos).le)
    exact Nat.le_floor (hprod.trans (mul_le_mul_of_nonneg_left hmaxR (Nat.cast_nonneg L)))

/-- A numerator p needs only the p critical lengths ceil(k q / p).
Each premise is an ordinary service quota on an actual translated window. -/
theorem rateWindows_of_generators {α : Type*} (S : ℤ → α) (i : α)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (h : ∀ (m : ℤ) (k : ℕ), 0 < k → k ≤ p →
      k ≤ serviceCount S i m (⌈(k : ℝ) * q / p⌉₊ : ℤ)) :
    RateWindows S i ((p : ℝ) / q) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply rateWindows_of_denominator S i p q hq
  intro m L hL
  let k := ⌊(L : ℝ) * ((p : ℝ) / q)⌋₊
  have hfloor : (k : ℝ) ≤ (L : ℝ) * ((p : ℝ) / q) :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hpR.le hqR.le))
  have hlt := Nat.lt_floor_add_one ((L : ℝ) * ((p : ℝ) / q))
  have hk : k ≤ p := by
    have hLR : (L : ℝ) ≤ q := by exact_mod_cast hL
    have hmul : (L : ℝ) * ((p : ℝ) / q) ≤ p := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hqR).mpr
      nlinarith
    have : (k : ℝ) ≤ p := hfloor.trans hmul
    exact_mod_cast this
  have hkcount : k ≤ serviceCount S i m (L : ℤ) := by
    by_cases hkzero : k = 0
    · rw [hkzero]
      exact Nat.zero_le _
    have hcrit : ⌈(k : ℝ) * q / p⌉₊ ≤ L := by
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ hpR).mpr
      have := (le_div_iff₀ hqR).mp (show (k : ℝ) ≤ (L : ℝ) * p / q by
        simpa only [mul_div_assoc] using hfloor)
      nlinarith
    exact (h m k (Nat.pos_of_ne_zero hkzero) hk).trans
      (serviceCount_mono_length S i m (by exact_mod_cast hcrit))
  have hcR : (k : ℝ) ≤ serviceCount S i m (L : ℤ) := by exact_mod_cast hkcount
  exact lt_of_lt_of_le hlt (by change (k : ℝ) + 1 ≤ _; linarith)

/-- For an integer period, the single unit-demand length implies all scales. -/
theorem rateWindows_of_unit {α : Type*} (S : ℤ → α) (i : α)
    (q : ℕ) (hq : 0 < q)
    (h : ∀ m : ℤ, 1 ≤ serviceCount S i m (q : ℤ)) :
    RateWindows S i (1 / (q : ℝ)) := by
  simpa only [Nat.cast_one] using
    rateWindows_of_generators S i 1 q (by omega) hq (by
      intro m k hk hk1
      have he : k = 1 := by omega
      subst k
      simpa using h m)

/-- Conversely, ordinary service meets each critical generator quota. -/
theorem generators_of_rateWindows {α : Type*} (S : ℤ → α) (i : α)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (h : RateWindows S i ((p : ℝ) / q)) :
    ∀ (m : ℤ) (k : ℕ), 0 < k → k ≤ p →
      k ≤ serviceCount S i m (⌈(k : ℝ) * q / p⌉₊ : ℤ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  intro m k _ _
  let L := ⌈(k : ℝ) * q / p⌉₊
  have hceil := Nat.le_ceil ((k : ℝ) * q / p)
  have hk : (k : ℝ) ≤ (L : ℝ) * ((p : ℝ) / q) := by
    have hh := (div_le_iff₀ hpR).mp hceil
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hqR).mpr hh
  have hh := lt_of_le_of_lt hk (h m L)
  have hnat : k < serviceCount S i m (L : ℤ) + 1 := by exact_mod_cast hh
  exact Nat.le_of_lt_succ hnat

/-- Exact numerator-indexed finite generation for any positive displayed
fraction. Coprimality is needed only when interpreting p as a reduced numerator. -/
theorem rateWindows_iff_generators {α : Type*} (S : ℤ → α) (i : α)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    RateWindows S i ((p : ℝ) / q) ↔
      ∀ (m : ℤ) (k : ℕ), 0 < k → k ≤ p →
        k ≤ serviceCount S i m (⌈(k : ℝ) * q / p⌉₊ : ℤ) :=
  ⟨generators_of_rateWindows S i p q hp hq, rateWindows_of_generators S i p q hp hq⟩

end RealPinwheel
