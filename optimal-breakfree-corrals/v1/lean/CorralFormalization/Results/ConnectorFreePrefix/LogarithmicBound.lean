import CorralFormalization.Results.ConnectorFreePrefix.Radius
import CorralFormalization.Results.LatinLogBound

/-!
# The ε/3 deduction from the connector-free floor

This file proves the analytic deduction in Section 8.5 with an explicit error
constant. It deliberately takes the physical census inequality at the NEW
floor as a theorem argument. The maintained earlier connector construction
does not prove this argument. Neither the new physical Latin-family injection
nor the endpoint completion theorem is established here. The cited labelled
Latin-square estimate `LatinSquareFactorialBound` is also an explicit input.
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix

open LatinTransfer LatinPrefix LatinPrefixSupply CorralLatinTailMarker PhysicalCensus
  Asymptotic

/-- An explicit Oε(h²) constant for the stronger floor. -/
noncomputable def radiusErrorConstant (ε : ℝ) : ℝ :=
  5 + ((-Real.log (ε / 12) / 2) + 2) * (2 * ε / 3)

/-- Real-variable rounding estimates for the literal stronger radicand.
The `34 ≤ ε*h` threshold is sufficient, with no optimized first height. -/
theorem radius_growth_bounds {h ε s r : ℝ}
    (hh : 1 ≤ h) (he0 : 0 < ε) (he1 : ε ≤ 1 / 100)
    (hbig : 34 ≤ ε * h) (hs : 2 ≤ s)
    (hsq : s^2 = (ε * (2 * h - 1) - 7) / 3)
    (hrlo : s - 1 ≤ r) (hrhi : r ≤ s) :
    2 * ε * h / 3 - 5 * Real.sqrt h ≤ r^2 ∧
      r^2 ≤ 2 * ε * h / 3 ∧ ε * h / 12 ≤ r^2 := by
  have hroot : 1 ≤ Real.sqrt h := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hroot2 : (Real.sqrt h)^2 = h := Real.sq_sqrt (by linarith)
  have hmul := mul_le_mul_of_nonneg_right he1 (show 0 ≤ h by linarith)
  have hs_le : s ≤ Real.sqrt h := by nlinarith
  have hrpos : 0 ≤ r := by linarith
  have hrsq : r^2 ≤ s^2 := (sq_le_sq₀ hrpos (by linarith)).mpr hrhi
  have hsminus : 0 ≤ s - 1 := by linarith
  have hlowsq : (s - 1)^2 ≤ r^2 := (sq_le_sq₀ hsminus hrpos).mpr hrlo
  have hhalf : s / 2 ≤ r := by linarith
  have hhalfsq : (s / 2)^2 ≤ r^2 := (sq_le_sq₀ (by linarith) hrpos).mpr hhalf
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The square and logarithm estimates used in the new leading coefficient.
These concern the new floor independently of any physical corral count. -/
theorem radius_leading_conditions {ε : ℝ} {h : ℕ}
    (hh : 1 ≤ h) (he0 : 0 < ε) (he1 : ε ≤ 1 / 100)
    (hbig : 34 ≤ ε * (h : ℝ)) :
    let r := radius ε (2 * h - 1)
    0 ≤ -Real.log (ε / 12) / 2 ∧
      2 * ε * (h : ℝ) / 3 - 5 * Real.sqrt (h : ℝ) ≤ (r : ℝ)^2 ∧
      (r : ℝ)^2 ≤ 2 * ε * (h : ℝ) / 3 ∧
      Real.log (h : ℝ) / 2 - (-Real.log (ε / 12) / 2) ≤ Real.log (r : ℝ) := by
  let n := 2 * h - 1
  let s := Real.sqrt ((ε * (n : ℝ) - 7) / 3)
  let r := radius ε n
  have hncast : (n : ℝ) = 2 * (h : ℝ) - 1 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * h)]
    push_cast
    ring
  have hnh : (h : ℝ) ≤ (n : ℝ) := by
    rw [hncast]
    have hhr : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hnbig : 34 ≤ ε * (n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hnh (le_of_lt he0)]
  have hrad : 0 ≤ (ε * (n : ℝ) - 7) / 3 := by linarith
  have hs : 2 ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsq : s^2 = (ε * (2 * (h : ℝ) - 1) - 7) / 3 := by
    dsimp [s]
    rw [Real.sq_sqrt hrad, hncast]
  have hrlo : s - 1 ≤ (r : ℝ) := (radius_sqrt_sub_one_lt ε n).le
  have hrhi : (r : ℝ) ≤ s := radius_le_sqrt ε n
  have hhreal : (1 : ℝ) ≤ h := by exact_mod_cast hh
  obtain ⟨hlow, hup, hsquare⟩ :=
    radius_growth_bounds hhreal he0 he1 hbig hs hsq hrlo hrhi
  have hc : 0 ≤ -Real.log (ε / 12) / 2 := by
    have hl : Real.log (ε / 12) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
    linarith
  have hlog := log_lower_from_square (by positivity : 0 < (h : ℝ))
    (by positivity : 0 < ε / 12)
    (by nlinarith : (ε / 12) * (h : ℝ) ≤ (r : ℝ)^2)
  exact ⟨hc, hlow, hup, hlog⟩

/-- The exact ε/3 logarithmic coefficient follows from a census lower bound
at the NEW radius. That census inequality and the cited Latin-square bound
are explicit arguments; this is not an unconditional Theorem 10. -/
theorem radius_log_lower_of_count
    (HLatin : LatinSquareFactorialBound) {ε : ℝ} {h : ℕ}
    (hh : 2 ≤ h) (hεpos : 0 < ε) (hε : ε ≤ 1 / 100)
    (hbig : 34 ≤ ε * (h : ℝ))
    (hcount : latinSquareCount (radius ε (2 * h - 1)) ^ h ≤ A_h h hh) :
    (ε / 3) * (h : ℝ)^2 * Real.log (h : ℝ) -
        radiusErrorConstant ε * (h : ℝ)^2 ≤ Real.log (A_h h hh : ℝ) := by
  let n := 2 * h - 1
  let r := radius ε n
  have hnh : (h : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show h ≤ n by dsimp [n]; omega)
  have hnbig : 34 ≤ ε * (n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hnh hεpos.le]
  have hr : 3 ≤ r := (radius_bounds hε hnbig).1
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hc, hlow, hup, hlog⟩ :=
    radius_leading_conditions (by omega : 1 ≤ h) hεpos hε hbig
  have hscaled := latin_family_leading_lower HLatin h r hh (by omega)
    (4 * ε / 3) 5 (-Real.log (ε / 12) / 2) (by norm_num) hc
    (by convert hlow using 1; ring)
    (by convert hup using 1; ring) hlog hcount
  convert hscaled using 1
  dsimp [radiusErrorConstant]
  ring

/-- Eventual form: an eventual physical count at the stronger floor implies
the printed ε/3 bound, with an explicit Oε(h²) constant. No endpoint or
physical-family existence statement is inferred from this implication. -/
theorem radius_eventual_log_lower_of_count
    (HLatin : LatinSquareFactorialBound) {ε : ℝ}
    (hεpos : 0 < ε) (hε : ε ≤ 1 / 100)
    (Hcount : ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
      latinSquareCount (radius ε (2 * h - 1)) ^ h ≤ A_h h (hh0.trans hh)) :
    ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
      (ε / 3) * (h : ℝ)^2 * Real.log (h : ℝ) -
          radiusErrorConstant ε * (h : ℝ)^2 ≤
        Real.log (A_h h (hh0.trans hh) : ℝ) := by
  obtain ⟨h0, hh0, Hcount⟩ := Hcount
  refine ⟨max h0 ⌈34 / ε⌉₊, by omega, ?_⟩
  intro h hh
  have hc : 34 / ε ≤ (⌈34 / ε⌉₊ : ℝ) := Nat.le_ceil _
  have hNh : (⌈34 / ε⌉₊ : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast (show ⌈34 / ε⌉₊ ≤ h by omega)
  have hbig : 34 ≤ ε * (h : ℝ) := by
    have ht := (div_le_iff₀ hεpos).mp (hc.trans hNh)
    nlinarith
  exact radius_log_lower_of_count HLatin (by omega) hεpos hε hbig
    (Hcount h (by omega))

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix
