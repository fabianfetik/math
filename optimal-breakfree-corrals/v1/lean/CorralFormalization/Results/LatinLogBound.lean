import CorralFormalization.DiversityCompletion.CyclicEndpointConnectorOrbits
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
The paper's logarithmic deduction from its cited Latin-square lower bound.
The McKay--Wanless bound is an explicit premise: it is not introduced as a
Lean axiom or claimed to have been proved by this file.
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.Asymptotic

open LatinTransfer LatinPrefix LatinPrefixSupply CorralLatinTailMarker
  PhysicalCensus

/-- The externally cited labelled Latin-square estimate, written for the
actual `latinSquareCount` used by the corral construction. -/
def LatinSquareFactorialBound : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    ((r.factorial : ℝ) ^ (2*r)) / ((r : ℝ) ^ (r*r)) ≤ (latinSquareCount r : ℝ)

theorem latinSquareCount_pos (r : ℕ) [NeZero r] : 0 < latinSquareCount r := by
  let : Nonempty (LatinSquare r) := ⟨cyclicLatinSquare r⟩
  exact Fintype.card_pos

/-- The cited factorial bound implies the exact logarithmic estimate used
in the paper. The factorial bound remains a visible theorem argument. -/
theorem latin_log_lower (H : LatinSquareFactorialBound) (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ)^2 * Real.log (r : ℝ) - 2*(r : ℝ)^2 ≤
      Real.log (latinSquareCount r : ℝ) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hfact0 : 0 < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hquot0 : 0 < ((r.factorial : ℝ) ^ (2*r)) / ((r : ℝ) ^ (r*r)) := by positivity
  have hlog := Real.log_le_log hquot0 (H r hr)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have hlnr : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast hr)
  have hlnpi : 0 ≤ Real.log (2*Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hstir := Stirling.le_log_factorial_stirling (n := r) (by omega)
  have hfac : (r : ℝ)*Real.log (r : ℝ) - (r : ℝ) ≤
      Real.log (r.factorial : ℝ) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hfac (show 0 ≤ (2 : ℝ)*(r : ℝ) by positivity)
  push_cast at hlog
  nlinarith

/-- Passing from a counted Latin family to logarithmic growth. -/
theorem latin_family_log_lower (H : LatinSquareFactorialBound)
    (h r : ℕ) (hh : 2 ≤ h) [NeZero r] (hr : 1 ≤ r)
    (hcount : latinSquareCount r ^ h ≤ A_h h hh) :
    (h : ℝ) * ((r : ℝ)^2 * Real.log (r : ℝ) - 2*(r : ℝ)^2) ≤
      Real.log (A_h h hh : ℝ) := by
  have hp : 0 < (latinSquareCount r : ℝ) := by
    exact_mod_cast latinSquareCount_pos r
  have hpow : 0 < (latinSquareCount r : ℝ)^h := pow_pos hp _
  have hcount' : (latinSquareCount r : ℝ)^h ≤ (A_h h hh : ℝ) := by exact_mod_cast hcount
  have hl := Real.log_le_log hpow hcount'
  rw [Real.log_pow] at hl
  have hm := mul_le_mul_of_nonneg_left (latin_log_lower H r hr) (show 0 ≤ (h : ℝ) by positivity)
  nlinarith

/-- A concrete substitute for the paper's O(h²) bookkeeping: if the
radius has the displayed square-root-size estimates, all rounding losses
are absorbed in one explicitly shown multiple of h². -/
theorem leading_term_from_radius {h r ε b c : ℝ}
    (hh : 1 ≤ h) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hlower : ε*h/2 - b*Real.sqrt h ≤ r^2)
    (hupper : r^2 ≤ ε*h/2)
    (hlog : Real.log h/2-c ≤ Real.log r) :
    (ε/4)*h^2*Real.log h - (b+(c+2)*ε/2)*h^2 ≤
      h*(r^2*Real.log r-2*r^2) := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt (by linarith)
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg hh
  have hl : Real.log h ≤ 2*Real.sqrt h := by
    have hlogmul := Real.log_mul (ne_of_gt hs) (ne_of_gt hs)
    rw [hsq] at hlogmul
    have hlogsqrt := Real.log_le_self (le_of_lt hs)
    linarith
  have hm1 := mul_le_mul_of_nonneg_left hlog (sq_nonneg r)
  have hm2 := mul_le_mul_of_nonneg_right hlower (show 0 ≤ Real.log h/2 by positivity)
  have hm3 := mul_le_mul_of_nonneg_left hupper (show 0 ≤ c+2 by linarith)
  have hm4 := mul_le_mul_of_nonneg_left hl (show 0 ≤ b*Real.sqrt h/2 by positivity)
  have hrootloss : b*Real.sqrt h*(Real.log h/2) ≤ b*h := by nlinarith [hsq]
  have hinner : (ε/4)*h*Real.log h - (b+(c+2)*ε/2)*h ≤
      r^2*Real.log r-2*r^2 := by nlinarith [hrootloss]
  have hfinal := mul_le_mul_of_nonneg_left hinner (show 0 ≤ h by linarith)
  nlinarith

theorem latin_family_leading_lower (H : LatinSquareFactorialBound)
    (h r : ℕ) (hh : 2 ≤ h) [NeZero r] (hr : 1 ≤ r)
    (ε b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hlower : ε*(h : ℝ)/2 - b*Real.sqrt (h : ℝ) ≤ (r : ℝ)^2)
    (hupper : (r : ℝ)^2 ≤ ε*(h : ℝ)/2)
    (hlog : Real.log (h : ℝ)/2-c ≤ Real.log (r : ℝ))
    (hcount : latinSquareCount r ^ h ≤ A_h h hh) :
    (ε/4)*(h : ℝ)^2*Real.log (h : ℝ) -
        (b+(c+2)*ε/2)*(h : ℝ)^2 ≤ Real.log (A_h h hh : ℝ) := by
  exact (leading_term_from_radius (by exact_mod_cast (show 1 ≤ h by omega))
    hb hc hlower hupper hlog).trans (latin_family_log_lower H h r hh hr hcount)

/-- Elementary estimates for the floor of the square root appearing in the
paper. The actual floor supplies the two inequalities on r. -/
theorem radius_growth_bounds {h ε s r : ℝ}
    (hh : 1 ≤ h) (he0 : 0 < ε) (he1 : ε ≤ 1/100)
    (hbig : 16 ≤ ε*h) (hs : 2 ≤ s)
    (hsq : s^2 = ε*(2*h-1)/4-2)
    (hrlo : s-1 ≤ r) (hrhi : r ≤ s) :
    ε*h/2-5*Real.sqrt h ≤ r^2 ∧ r^2 ≤ ε*h/2 ∧ ε*h/32 ≤ r^2 := by
  have hroot : 1 ≤ Real.sqrt h := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hroot2 : (Real.sqrt h)^2 = h := Real.sq_sqrt (by linarith)
  have hmul := mul_le_mul_of_nonneg_right he1 (show 0 ≤ h by linarith)
  have hs_le : s ≤ Real.sqrt h := by nlinarith
  have hrpos : 0 ≤ r := by linarith
  have hrsq : r^2 ≤ s^2 := (sq_le_sq₀ hrpos (by linarith)).mpr hrhi
  have hsminus : 0 ≤ s-1 := by linarith
  have hlowsq : (s-1)^2 ≤ r^2 := (sq_le_sq₀ hsminus hrpos).mpr hrlo
  have hhalf : s/2 ≤ r := by linarith
  have hhalfsq : (s/2)^2 ≤ r^2 := (sq_le_sq₀ (by linarith) hrpos).mpr hhalf
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- A positive square lower bound yields the corresponding logarithmic
lower bound, with the coefficient 1/2 kept exact. -/
theorem log_lower_from_square {h r a : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hsq : a*h ≤ r^2) :
    Real.log h/2 - (-Real.log a/2) ≤ Real.log r := by
  have hl := Real.log_le_log (show 0 < a*h by positivity) hsq
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hh), Real.log_pow] at hl
  norm_num at hl
  linarith

end CorralFormalization.LatinCompletion.TerraceCompletion.Asymptotic
