import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Comparison of the final exact-matching failure rate with weaker fixed-density tails.
This is only a deterministic parameter inequality. It does not construct a
sample, prove a tail estimate, or supply candidate packings.
-/

namespace CorralFormalization.EndpointProof.RateBudget

open Filter Topology

/-- A fixed polynomial number of queries can be absorbed by any strictly
smaller positive exponential rate. The result is eventual in `n`; no
numerical threshold is extracted. -/
theorem polynomial_union_absorbed (C a b : ℝ) (k : ℕ) (hab : b < a) :
    ∃ N : ℕ, ∀ n ≥ N,
      C * (n : ℝ)^k * Real.exp (-a * n) ≤ Real.exp (-b * n) := by
  have hreal : Tendsto (fun x : ℝ => x^k * Real.exp (-(a-b) * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) (a-b) (by linarith)
  have hrealC : Tendsto (fun x : ℝ => C * (x^k * Real.exp (-(a-b) * x)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hreal
  have hnat := hrealC.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in atTop,
      C * ((n : ℝ)^k * Real.exp (-(a-b) * n)) < 1 :=
    (tendsto_order.1 hnat).2 1 (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨N, ?_⟩
  intro n hn
  have hexp : Real.exp (-a * n) =
      Real.exp (-b * n) * Real.exp (-(a-b) * n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  calc
    C * (n : ℝ)^k * (Real.exp (-b * n) * Real.exp (-(a-b) * n)) =
        Real.exp (-b * n) * (C * ((n : ℝ)^k * Real.exp (-(a-b) * n))) := by ring
    _ ≤ Real.exp (-b * n) * 1 :=
      mul_le_mul_of_nonneg_left (le_of_lt (hN n hn)) (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-b * n) := mul_one _

/-- If `ξ = 10⁻³⁶ τ⁹ r`, then the final coefficient `ξ⁴/10⁶` is
strictly smaller than either candidate coefficient `τ¹⁸/32000` or
`p⁸/32000`, for the actual parameter order `0 < τ ≤ p ≤ 1`, `0 ≤ r ≤ 1`.
Thus the two weaker positive fixed-density rates have room to pay the final
rate. Actual tail and polynomial-union arguments remain separate obligations. -/
theorem final_rate_lt_weaker_tail_rates (p τ r ξ : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hτ : 0 < τ) (hτp : τ ≤ p)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hξ : ξ = (1 / (10 : ℝ)^36) * τ^9 * r) :
    ξ^4 / 10^6 < τ^18 / 32000 ∧ ξ^4 / 10^6 < p^8 / 32000 := by
  have ht0 : 0 ≤ τ := le_of_lt hτ
  have ht1 : τ ≤ 1 := hτp.trans hp1
  have hc0 : 0 ≤ (1 : ℝ) / 10^36 := by positivity
  have hc1 : (1 : ℝ) / 10^36 ≤ 1 := by norm_num
  have ht9 : 0 ≤ τ^9 := pow_nonneg ht0 _
  have hfirst : (1 / (10 : ℝ)^36) * τ^9 ≤ τ^9 := by
    simpa using mul_le_mul_of_nonneg_right hc1 ht9
  have hx0 : 0 ≤ ξ := by rw [hξ]; positivity
  have hx : ξ ≤ τ^9 := by
    rw [hξ]
    calc
      (1 / (10 : ℝ)^36) * τ^9 * r ≤ τ^9 * 1 :=
        mul_le_mul hfirst hr1 hr0 ht9
      _ = τ^9 := by ring
  have hx4 : ξ^4 ≤ τ^36 := by
    calc
      ξ^4 ≤ (τ^9)^4 := pow_le_pow_left₀ hx0 hx 4
      _ = τ^36 := by rw [← pow_mul]
  have ht36 : τ^36 ≤ τ^18 :=
    pow_le_pow_of_le_one ht0 ht1 (by norm_num : 18 ≤ 36)
  have htp : τ^36 ≤ p^8 := by
    calc
      τ^36 ≤ τ^8 := pow_le_pow_of_le_one ht0 ht1 (by norm_num : 8 ≤ 36)
      _ ≤ p^8 := pow_le_pow_left₀ ht0 hτp 8
  have htpos : 0 < τ^18 := pow_pos hτ _
  have hppos : 0 < p^8 := pow_pos hp _
  constructor <;> nlinarith

/-- If individual query failures have either displayed weaker tail rate,
then any fixed polynomial union of them is eventually bounded by the uniform exact-matching theorem
final exponential. This is a numerical implication only: it neither
establishes those probability bounds nor supplies the queries. -/
theorem weaker_tails_pay_final_polynomial_union
    (p τ r ξ C : ℝ) (k : ℕ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hτ : 0 < τ) (hτp : τ ≤ p)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hξ : ξ = (1 / (10 : ℝ)^36) * τ^9 * r) :
    ∃ N : ℕ, ∀ n ≥ N,
      C * (n : ℝ)^k * Real.exp (-(τ^18 / 32000) * n) ≤
          Real.exp (-(ξ^4 / 10^6) * n) ∧
      C * (n : ℝ)^k * Real.exp (-(p^8 / 32000) * n) ≤
          Real.exp (-(ξ^4 / 10^6) * n) := by
  obtain ⟨hτrate, hprate⟩ := final_rate_lt_weaker_tail_rates p τ r ξ
    hp hp1 hτ hτp hr0 hr1 hξ
  obtain ⟨Nτ, hNτ⟩ := polynomial_union_absorbed C (τ^18 / 32000) (ξ^4 / 10^6) k hτrate
  obtain ⟨Np, hNp⟩ := polynomial_union_absorbed C (p^8 / 32000) (ξ^4 / 10^6) k hprate
  refine ⟨max Nτ Np, fun n hn => ?_⟩
  exact ⟨hNτ n ((le_max_left _ _).trans hn), hNp n ((le_max_right _ _).trans hn)⟩

namespace SamplingConstants

noncomputable section

def eta : ℝ := 1 / 10^4
def rho (q : ℝ) : ℝ := (eta * q)^2 / 9
def p (q : ℝ) : ℝ := rho q / 4
def tau (q : ℝ) : ℝ := (1 / 10^30) * (p q)^4
def r0 (q : ℝ) : ℝ := eta * q / 2
def kappa (q : ℝ) : ℝ := (1 / 10^30) * (tau q)^9
def xi (q : ℝ) : ℝ := kappa q * r0 q / 10^6

/-- The preceding asymptotic rate comparison applies to the literal exact-matching
parameter definitions, for the paper's complete range `0 < q ≤ 1/2`.
This is still only a comparison of hypothetical tail bounds, not exact-matching. -/
theorem sampling_rates_pay_polynomial_union (q C : ℝ) (k : ℕ)
    (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ n ≥ N,
      C * (n : ℝ)^k * Real.exp (-(tau q^18 / 32000) * n) ≤
          Real.exp (-(xi q^4 / 10^6) * n) ∧
      C * (n : ℝ)^k * Real.exp (-(p q^8 / 32000) * n) ≤
          Real.exp (-(xi q^4 / 10^6) * n) := by
  have hη : 0 < eta := by norm_num [eta]
  have hηq0 : 0 < eta * q := mul_pos hη hq0
  have hηq1 : eta * q ≤ 1 := by norm_num [eta] at *; nlinarith
  have hρ0 : 0 < rho q := by unfold rho; positivity
  have hp0 : 0 < p q := by unfold p; positivity
  have hsq : (eta*q)^2 ≤ 1 := pow_le_one₀ (le_of_lt hηq0) hηq1
  have hp1 : p q ≤ 1 := by unfold p rho; nlinarith
  have ht0 : 0 < tau q := by unfold tau; positivity
  have hp4 : (p q)^4 ≤ p q := pow_le_of_le_one (le_of_lt hp0) hp1 (by norm_num)
  have ht1 : tau q ≤ p q := by unfold tau; nlinarith
  have hr0 : 0 ≤ r0 q := by unfold r0; positivity
  have hr1 : r0 q ≤ 1 := by unfold r0; nlinarith
  have hxi : xi q = (1 / (10 : ℝ)^36) * (tau q)^9 * r0 q := by
    unfold xi kappa
    ring
  exact weaker_tails_pay_final_polynomial_union (p q) (tau q) (r0 q) (xi q) C k
    hp0 hp1 ht0 ht1 hr0 hr1 hxi

end

end SamplingConstants

end CorralFormalization.EndpointProof.RateBudget
