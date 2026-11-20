import CorralFormalization.EndpointProof.Probability.RateBudget
import Mathlib.Algebra.Order.Floor.Ring

/-!
Numerical prerequisites for the four-orbit selector family. The probability
and the actual packing are provided elsewhere and are not asserted here.
-/

namespace CorralFormalization.EndpointProof.RateBudget

noncomputable section

/-- The floor of the paired cover construction's larger primitive forbidden-support allowance. -/
def selectorBudget (p : ℝ) (n : ℕ) : ℕ :=
  ⌊p^4 * (n : ℝ) / 10^10⌋₊

/-- With `floor(n/1000)` candidates and success probability `p⁴`, a
half-mean Hoeffding deviation pays paired cover construction's `C_{P,0}` budget and has exponent
at least `n p⁸/32000`. This does not itself prove any probability bound. -/
theorem selector_mean_and_exponent (p : ℝ) (n : ℕ)
    (hp : 0 < p) (hn : 2000 ≤ n) :
    let M := n / 1000
    let t := (M : ℝ) * p^4 / 2
    (selectorBudget p n : ℝ) ≤ (M : ℝ) * p^4 - t ∧
      (p^8 / 32000) * n ≤ t^2 / (2 * (M : ℝ) * (1/4)) := by
  dsimp only
  have hMnat : 0 < n / 1000 := by omega
  have hM : (0 : ℝ) < (n / 1000 : ℕ) := by exact_mod_cast hMnat
  have hcountNat : n ≤ (n / 1000) * 2000 := by omega
  have hcount : (n : ℝ) ≤ ((n / 1000 : ℕ) : ℝ) * 2000 := by exact_mod_cast hcountNat
  have hp4 : 0 ≤ p^4 := by positivity
  have hp8 : 0 ≤ p^8 := by positivity
  have hmul4 := mul_le_mul_of_nonneg_right hcount hp4
  have hmul8 := mul_le_mul_of_nonneg_right hcount hp8
  have hfloor : (selectorBudget p n : ℝ) ≤ p^4 * (n : ℝ) / 10^10 := by
    unfold selectorBudget
    exact Nat.floor_le (by positivity)
  have htail : ((((n / 1000 : ℕ) : ℝ) * p^4 / 2)^2) /
      (2 * ((n / 1000 : ℕ) : ℝ) * (1/4)) =
        ((n / 1000 : ℕ) : ℝ) * p^8 / 2 := by
    field_simp [ne_of_gt hM]
    ring
  rw [htail]
  constructor <;> nlinarith

end
end CorralFormalization.EndpointProof.RateBudget
