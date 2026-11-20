import CorralFormalization.EndpointProof.Matching.UniversalCore.CoreFractionalRate
import Mathlib.Analysis.Complex.ExponentialBounds

open Filter Asymptotics
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
open scoped Classical
namespace EndpointMatching.UniversalCore
noncomputable section

/-- Every square-root/polylogarithmic remainder is eventually smaller than
half any specified positive linear capacity. The threshold depends only on
its two displayed constants. -/
theorem sqrt_log_remainder_eventually_sublinear (C α : ℝ)
    (hC : 0 ≤ C) (hα : 0 < α) :
    ∃ N : ℕ, ∀ n ≥ N,
      C * Real.sqrt n * (Real.log (Real.exp 1 * n))^(3/2 : ℝ) ≤
        (α / 2) * n := by
  let δ : ℝ := α / (4 * (C+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall := (isLittleO_log_rpow_rpow_atTop (3/2 : ℝ)
    (s := (1/2 : ℝ)) (by norm_num)).bound hδ
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.1 hsmall
  obtain ⟨N,hN⟩ := exists_nat_gt (max R 1)
  refine ⟨N, ?_⟩
  intro n hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : R ≤ (n : ℝ) := by linarith [le_max_left R (1 : ℝ)]
  have hn1 : (1 : ℝ) ≤ n := by linarith [le_max_right R (1 : ℝ)]
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have he0 : 0 < Real.exp 1 := Real.exp_pos _
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_two]
  have hx : R ≤ Real.exp 1 * n := by nlinarith
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * n) := by
    apply Real.log_nonneg
    nlinarith
  have hp0 : 0 ≤ (Real.log (Real.exp 1 * n))^(3/2 : ℝ) := Real.rpow_nonneg hlog0 _
  have hroot0 : 0 ≤ (Real.exp 1 * n)^(1/2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hlog := hR (Real.exp 1 * n) hx
  rw [Real.norm_of_nonneg hp0, Real.norm_of_nonneg hroot0] at hlog
  rw [← Real.sqrt_eq_rpow] at hlog
  have he4 : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_three]
  have hse : Real.sqrt (Real.exp 1) ≤ 2 := by
    have heq := Real.sq_sqrt (le_of_lt he0)
    have hnneg := Real.sqrt_nonneg (Real.exp 1)
    nlinarith
  have hroot : Real.sqrt (Real.exp 1 * n) ≤ 2 * Real.sqrt n := by
    rw [Real.sqrt_mul (le_of_lt he0)]
    exact mul_le_mul_of_nonneg_right hse (Real.sqrt_nonneg _)
  have hlog' : (Real.log (Real.exp 1 * n))^(3/2 : ℝ) ≤ δ * (2 * Real.sqrt n) :=
    hlog.trans (mul_le_mul_of_nonneg_left hroot (le_of_lt hδ))
  have hcoeff : 2 * C * δ ≤ α / 2 := by
    dsimp [δ]
    have hden : 0 < 4 * (C+1) := by positivity
    have haux : (2 * C * α) / (4 * (C+1)) ≤ α / 2 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    convert haux using 1
    all_goals ring
  have hsquare : (Real.sqrt (n : ℝ))^2 = n := Real.sq_sqrt hn0
  calc
    C * Real.sqrt n * (Real.log (Real.exp 1 * n))^(3/2 : ℝ) ≤
        C * Real.sqrt n * (δ * (2 * Real.sqrt n)) :=
      mul_le_mul_of_nonneg_left hlog' (mul_nonneg hC (Real.sqrt_nonneg _))
    _ = (2 * C * δ) * (Real.sqrt (n : ℝ))^2 := by ring
    _ = (2 * C * δ) * n := by rw [hsquare]
    _ ≤ (α / 2) * n := mul_le_mul_of_nonneg_right hcoeff hn0

/-- Integer residuals bounded by the above analytic error fit the literal
floor capacity for all large orders. -/
theorem sqrt_log_remainder_fits_floor (C α : ℝ) (hC : 0 ≤ C) (hα : 0 < α) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ,
      (k : ℝ) ≤ C * Real.sqrt n * (Real.log (Real.exp 1 * n))^(3/2 : ℝ) →
      k ≤ ⌊α * (n : ℝ)⌋₊ := by
  obtain ⟨N,hN⟩ := sqrt_log_remainder_eventually_sublinear C α hC hα
  refine ⟨N, ?_⟩
  intro n hn k hk
  apply Nat.le_floor
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hbound := hN n hn
  nlinarith

/-- One group-independent threshold simultaneously pays the core receiver,
the fractional deletion allowance, the external AKS degree threshold and
the actual residual's integer core capacity. -/
theorem exact_receiver_thresholds (q C : ℝ) (Dstar : ℕ) (hq : 0 < q) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ n ≥ N,
      (2 : ℝ) ≤ kappa q * n ∧
      (60000 : ℝ) ≤ q^2 * n ∧
      6 * (Dstar : ℝ) ≤ q^2 * n ∧
      ∀ k : ℕ, (k : ℝ) ≤ C * Real.sqrt n *
        (Real.log (Real.exp 1 * n))^(3/2 : ℝ) →
        k ≤ ⌊kappa q * (n : ℝ)⌋₊ := by
  have hκ : 0 < kappa q := by unfold kappa tau p rho eta; positivity
  have hq2 : 0 < q^2 := pow_pos hq _
  obtain ⟨Ncap,hNcap⟩ := sqrt_log_remainder_fits_floor C (kappa q) hC hκ
  obtain ⟨Nκ,hNκ⟩ := exists_nat_gt (2 / kappa q)
  obtain ⟨Nq,hNq⟩ := exists_nat_gt (60000 / q^2)
  obtain ⟨Nstar,hNstar⟩ := exists_nat_gt (6 * (Dstar : ℝ) / q^2)
  refine ⟨max Ncap (max Nκ (max Nq Nstar)), ?_⟩
  intro n hn
  have hcap : Ncap ≤ n := by omega
  have hk : Nκ ≤ n := by omega
  have hq' : Nq ≤ n := by omega
  have hs : Nstar ≤ n := by omega
  have hk' : (Nκ : ℝ) ≤ n := by exact_mod_cast hk
  have hq'' : (Nq : ℝ) ≤ n := by exact_mod_cast hq'
  have hs' : (Nstar : ℝ) ≤ n := by exact_mod_cast hs
  have hκn := (div_lt_iff₀ hκ).mp hNκ
  have hqn := (div_lt_iff₀ hq2).mp hNq
  have hsn := (div_lt_iff₀ hq2).mp hNstar
  refine ⟨?_,?_,?_,hNcap n hcap⟩
  · nlinarith [mul_nonneg (le_of_lt hκ) (sub_nonneg.mpr hk')]
  · nlinarith [mul_nonneg (le_of_lt hq2) (sub_nonneg.mpr hq'')]
  · nlinarith [mul_nonneg (le_of_lt hq2) (sub_nonneg.mpr hs')]

end
end EndpointMatching.UniversalCore
