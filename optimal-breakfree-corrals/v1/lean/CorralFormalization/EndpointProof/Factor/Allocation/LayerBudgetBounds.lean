import CorralFormalization.EndpointProof.Factor.Allocation.GenericLayers

/-!
# Paper constants pay the actual layer estimates

These are deterministic inequalities; the lower-order tolerance and deficit
still have to be supplied for the actual target at a uniform large order.
-/

namespace EndpointFactor.Allocation
open EndpointLayeredSample
noncomputable section

/-- The fixed paper constants pay special-reserve room, fitting of both
generic raw roles, the terminal capacity, and all one-sided ordinary-transition edit budgets. -/
theorem explicit_layer_numeric_bounds
    (q r ε η n d s K ℓ a c : ℝ)
    (hq : 0 < q) (hq3 : q ≤ 1/3) (hr : 0 < r) (hr10 : r ≤ 1/10)
    (hε : 0 < ε) (hη : 0 < η) (hn : 0 < n)
    (hd0 : 0 ≤ d) (hs0 : 0 ≤ s) (hK0 : 0 ≤ K)
    (hεrq : ε ≤ r*q/10^8) (hεη : ε ≤ η/10000)
    (hd : d ≤ 2*ε*n) (hs : s ≤ ε*n) (hK : K ≤ ε*n)
    (hℓ : ℓ = q*n-q*d)
    (ha : a ≤ (1-r/2)*q) (hc : c ≤ (1-r/2)*q) :
    4*(d+s) ≤ r*n ∧
    K ≤ ℓ ∧ 0 < ℓ ∧
    a*n+s ≤ ℓ ∧ c*n+s ≤ ℓ ∧
    |ℓ-q*n| ≤ η*n ∧
    (2+q)*d+s+4*K ≤ η*n ∧
    d+2*K ≤ η*n ∧ d+K ≤ η*n := by
  have hr1 : r ≤ 1 := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hrq0 : 0 ≤ r*q := mul_nonneg hr.le hq.le
  have hepsq : ε ≤ q/10^8 := by
    have h := mul_le_mul_of_nonneg_right hr1 hq.le
    nlinarith only [h, hεrq]
  have hepsr : ε ≤ r/10^8 := by
    have h := mul_le_mul_of_nonneg_left hq1 hr.le
    nlinarith only [h, hεrq]
  have hepsq4 : ε ≤ q/4 := by linarith only [hepsq, hq]
  have hηeps : 16*ε ≤ η := by linarith only [hεη, hε]
  have hεn : 0 ≤ ε*n := mul_nonneg hε.le hn.le
  have hηn : 0 ≤ η*n := mul_nonneg hη.le hn.le
  have hqen : q*(ε*n) ≤ ε*n := by
    have h := mul_nonneg (sub_nonneg.mpr hq1) hεn
    nlinarith only [h]
  have hqd : q*d ≤ 2*(ε*n) := by
    have h := mul_le_mul_of_nonneg_left hd hq.le
    nlinarith only [h, hqen]
  have hqd0 : 0 ≤ q*d := mul_nonneg hq.le hd0
  have hqnn : 0 < q*n := mul_pos hq hn
  have hreserveScale := mul_le_mul_of_nonneg_right hepsr hn.le
  have hrn : 0 ≤ r*n := mul_nonneg hr.le hn.le
  have hreserve : 4*(d+s) ≤ r*n := by nlinarith only [hd, hs, hreserveScale, hrn]
  have hqScale := mul_le_mul_of_nonneg_right hepsq4 hn.le
  have hpositive : 0 < ℓ := by nlinarith only [hℓ, hqd, hqScale, hqnn]
  have hterminal : K ≤ ℓ := by nlinarith only [hℓ, hqd, hqScale, hK, hεn]
  have hrqscale := mul_le_mul_of_nonneg_right hεrq hn.le
  have hrqn : 0 ≤ r*q*n := mul_nonneg hrq0 hn.le
  have hroom : 3*(ε*n) ≤ (r*q*n)/2 := by nlinarith only [hrqscale, hrqn]
  have hascale := mul_le_mul_of_nonneg_right ha hn.le
  have hcscale := mul_le_mul_of_nonneg_right hc hn.le
  have hafit : a*n+s ≤ ℓ := by nlinarith only [hascale, hs, hqd, hℓ, hroom]
  have hcfit : c*n+s ≤ ℓ := by nlinarith only [hcscale, hs, hqd, hℓ, hroom]
  have hηscale := mul_le_mul_of_nonneg_right hηeps hn.le
  have hsmall : q*d ≤ η*n := by nlinarith only [hqd, hηscale, hεn]
  have hclose : |ℓ-q*n| ≤ η*n := by
    rw [abs_le]
    constructor <;> linarith only [hℓ, hqd0, hsmall, hηn]
  have hspecial : (2+q)*d+s+4*K ≤ η*n := by
    have hqd' : q*d ≤ d := by
      have h := mul_nonneg (sub_nonneg.mpr hq1) hd0
      nlinarith only [h]
    nlinarith only [hqd', hd, hs, hK, hηscale, hεn]
  refine ⟨hreserve, hterminal, hpositive, hafit, hcfit, hclose, hspecial, ?_, ?_⟩ <;>
    nlinarith only [hd, hK, hηscale, hεn]

/-- The number of ordinary transitions is at most the paper's `J`, so the
sum of their `θ n` losses fits the displayed `Δ n/10000` budget. -/
theorem ordinary_total_deficit_budget (q : ℝ) (m : ℕ) (n : ℝ)
    (hq : 0 < q) (hq3 : q ≤ 1/3) (hn : 0 ≤ n) :
    ((m+1 : ℕ) : ℝ) * (explicitTheta q m*n) ≤ explicitDelta q*n/10000 := by
  have hθ : 0 < explicitTheta q m := (explicitTheta_bounds q m hq hq3).1
  have hden : (m : ℝ)+3 ≠ 0 := by positivity
  have heq : ((m : ℝ)+3)*explicitTheta q m = explicitDelta q/10000 := by
    unfold explicitTheta
    field_simp
    <;> ring
  have hmul : ((m : ℝ)+1)*explicitTheta q m ≤ ((m : ℝ)+3)*explicitTheta q m :=
    mul_le_mul_of_nonneg_right (by linarith) hθ.le
  have hscaled := mul_le_mul_of_nonneg_right hmul hn
  have heqscaled := congrArg (fun x : ℝ => x*n) heq
  push_cast
  nlinarith only [hscaled, heqscaled]

/-- The actual donor-loss expression used by `OrdinaryFragments.Outcome`
is strictly below the available pair supply under the paper constants. -/
theorem donor_budget_numeric (q ε Δ n d s K h w : ℝ)
    (hq : 0 < q) (hq3 : q ≤ 1/3) (hε : 0 < ε) (hn : 0 < n)
    (hd0 : 0 ≤ d) (hΔq : Δ ≤ q^2) (hεΔ : ε ≤ Δ/100000)
    (hd : d ≤ 2*ε*n) (hs : s ≤ ε*n) (hK : K ≤ ε*n)
    (hw : w ≤ ε*n) (hh : h ≤ Δ*n/10000) :
    ((2+q)*d+s+4*K)+K+(d+s+K)+3*h+2*w < q^2*n/2 := by
  have hq1 : q ≤ 1 := by linarith
  have hqd : q*d ≤ d := by
    have h := mul_nonneg (sub_nonneg.mpr hq1) hd0
    nlinarith only [h]
  have hΔ0 : 0 < Δ := by linarith
  have hΔn : 0 < Δ*n := mul_pos hΔ0 hn
  have hεscale := mul_le_mul_of_nonneg_right hεΔ hn.le
  have hΔscale := mul_le_mul_of_nonneg_right hΔq hn.le
  nlinarith only [hqd, hd, hs, hK, hw, hh, hεscale, hΔscale, hΔn]

end
end EndpointFactor.Allocation
