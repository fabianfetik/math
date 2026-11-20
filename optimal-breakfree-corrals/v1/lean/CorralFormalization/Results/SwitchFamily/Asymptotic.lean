import CorralFormalization.DiversityCompletion.OptimalCorralCensus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Exact switch radius and its logarithmic consequence

This module proves the arithmetic and analytic consequence of a supplied
finite switch-family bound. It does not supply the terrace, the physical
switch family, or an orbit-count lower bound.
-/

open CorralFormalization.PhysicalCensus

noncomputable section

namespace CorralFormalization.Results.SwitchFamily

/-- The natural value of the paper's nested-floor parameter, in its
eventual regime where the subtracted integer is nonnegative. -/
def switchMultiplicity (n : ℕ) : ℕ := (Nat.sqrt n - 8) / 5

theorem sqrt_nat_ge_eight {n : ℕ} (hn : 64 ≤ n) : 8 ≤ Nat.sqrt n := by
  apply Nat.le_sqrt.mpr
  omega

/-- The natural parameter is literally the printed integer floor once the
paper's standing large-size condition holds. -/
theorem switchMultiplicity_eq_explicit_floor {n : ℕ} (hn : 64 ≤ n) :
    (switchMultiplicity n : ℤ) =
      ⌊(((⌊Real.sqrt (n : ℝ)⌋ : ℤ) : ℝ) - 8) / 5⌋ := by
  have h8 := sqrt_nat_ge_eight hn
  rw [Real.floor_real_sqrt_eq_nat_sqrt]
  have he : (((Nat.sqrt n : ℤ) : ℝ) - 8) = ((Nat.sqrt n - 8 : ℕ) : ℝ) := by
    rw [Nat.cast_sub h8]
    push_cast
    ring
  rw [he]
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Int.floor_div_natCast, Int.floor_natCast]
  simp [switchMultiplicity, Int.natCast_ediv]

/-- The exact integer square root loses less than one, and dividing by five
loses at most four further units before scaling. -/
theorem switchMultiplicity_sqrt_lower {n : ℕ} (hn : 64 ≤ n) :
    (Real.sqrt (n : ℝ) - 13) / 5 ≤ (switchMultiplicity n : ℝ) := by
  have h8 := sqrt_nat_ge_eight hn
  have hsqrt := Nat.lt_floor_add_one (Real.sqrt (n : ℝ))
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt] at hsqrt
  have hdiv := Nat.mod_add_div (Nat.sqrt n - 8) 5
  have hdivR := congrArg (fun t : ℕ => (t : ℝ)) hdiv
  push_cast at hdivR
  rw [Nat.cast_sub h8] at hdivR
  have hmod : (((Nat.sqrt n - 8) % 5 : ℕ) : ℝ) ≤ 4 := by
    exact_mod_cast (show (Nat.sqrt n - 8) % 5 ≤ 4 from by have := Nat.mod_lt (Nat.sqrt n - 8) (by omega : 0 < 5); omega)
  change (Real.sqrt (n : ℝ) - 13) / 5 ≤ (((Nat.sqrt n - 8) / 5 : ℕ) : ℝ)
  nlinarith

/-- The integer-floor loss together with the replacement of `2h-1` by `2h`
costs at most 14/5 in the coefficient of h. -/
theorem switchMultiplicity_height_lower (h : ℕ) (hh : 33 ≤ h) :
    (Real.sqrt 2 / 5) * (h : ℝ) * Real.sqrt (h : ℝ) - (14 / 5) * (h : ℝ) ≤
      ((h * switchMultiplicity (2*h-1) : ℕ) : ℝ) := by
  have hn : 64 ≤ 2*h-1 := by omega
  have hroot := switchMultiplicity_sqrt_lower hn
  have hcast : ((2*h-1 : ℕ) : ℝ) = 2*(h : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*h)]
    push_cast
    ring
  rw [hcast] at hroot
  have hhn : 0 ≤ (h : ℝ) := by positivity
  have h2h : 0 ≤ 2*(h : ℝ) := by positivity
  have h2h1 : 0 ≤ 2*(h : ℝ)-1 := by
    have hhR : (1 : ℝ) ≤ 2*(h : ℝ) := by exact_mod_cast (show 1 ≤ 2*h by omega)
    linarith
  have ha := Real.sq_sqrt h2h
  have hb := Real.sq_sqrt h2h1
  have han := Real.sqrt_nonneg (2*(h : ℝ))
  have hbn := Real.sqrt_nonneg (2*(h : ℝ)-1)
  have hshift : Real.sqrt (2*(h : ℝ)) ≤ Real.sqrt (2*(h : ℝ)-1)+1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hroot hhn
  have hs : Real.sqrt (2*(h : ℝ)) = Real.sqrt 2 * Real.sqrt (h : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  rw [hs] at hshift
  push_cast
  nlinarith

/-- The paper's `h^(3/2)` is the same expression as `h*sqrt h`. -/
theorem rpow_three_halves_eq (h : ℕ) (hh : 0 < h) :
    (h : ℝ) ^ ((3 : ℝ)/2) = (h : ℝ) * Real.sqrt (h : ℝ) := by
  have hpos : 0 < (h : ℝ) := by exact_mod_cast hh
  rw [Real.sqrt_eq_rpow, show (3 : ℝ)/2 = 1 + 1/2 by norm_num,
    Real.rpow_add hpos, Real.rpow_one]

/-- The asymptotic inequality from A.2, for any actual census lower bound
already supplied by a separately proved physical switch construction. The
explicit error term `(14/5)h` is uniform. -/
theorem switch_log_lower_of_count (h : ℕ) (hh : 33 ≤ h)
    (hcount : 2^(h * switchMultiplicity (2*h-1)) ≤ A_h h (by omega)) :
    (Real.sqrt 2 / 5) * (h : ℝ)^((3 : ℝ)/2) - (14 / 5) * (h : ℝ) ≤
      Real.logb 2 (A_h h (by omega) : ℝ) := by
  have hp : (2 : ℝ)^(h * switchMultiplicity (2*h-1)) ≤
      (A_h h (by omega) : ℝ) := by exact_mod_cast hcount
  have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ)<2)
    (by positivity : (0 : ℝ)<2^(h * switchMultiplicity (2*h-1))) hp
  rw [Real.logb_pow,Real.logb_self_eq_one (by norm_num),mul_one] at hl
  rw [rpow_three_halves_eq h (by omega)]
  simpa [mul_assoc] using (switchMultiplicity_height_lower h hh).trans hl

end CorralFormalization.Results.SwitchFamily
end
