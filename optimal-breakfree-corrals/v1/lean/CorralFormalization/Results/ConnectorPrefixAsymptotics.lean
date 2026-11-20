import CorralFormalization.Results.ConnectorPrefixFloor
import CorralFormalization.Results.LatinLogBound
import CorralFormalization.Results.CorralCountUpper
import Mathlib.Analysis.Asymptotics.Theta

/-! The connector-prefix floor and logarithmic lower order. The endpoint
hypothesis and the cited Latin-square lower bound remain explicit inputs. -/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.Asymptotic

open CorralLatinTailMarker PhysicalCensus

noncomputable def radiusErrorConstant (ε : ℝ) : ℝ :=
  5 + ((-Real.log (ε/32)/2)+2)*ε/2

/-- A harmless total extension at h<2 of the manuscript's log A_h. -/
noncomputable def logAsymmetricCount (h : ℕ) : ℝ :=
  if hh : 2 ≤ h then Real.log (A_h h hh : ℝ) else 0

noncomputable def entropyScale (h : ℕ) : ℝ := (h : ℝ)^2 * Real.log (h : ℝ)

theorem radius_leading_conditions {ε : ℝ} {h : ℕ}
    (hh : 1 ≤ h) (he0 : 0 < ε) (he1 : ε ≤ 1/100)
    (hbig : 24 ≤ ε*(h : ℝ)) :
    let r := connectorPrefixRadius ε (2*h-1)
    0 ≤ -Real.log (ε/32)/2 ∧
      ε*(h : ℝ)/2-5*Real.sqrt (h : ℝ) ≤ (r : ℝ)^2 ∧
      (r : ℝ)^2 ≤ ε*(h : ℝ)/2 ∧
      Real.log (h : ℝ)/2-(-Real.log (ε/32)/2) ≤ Real.log (r : ℝ) := by
  let n := 2*h-1
  let s := Real.sqrt (ε*(n : ℝ)/4-2)
  let r := connectorPrefixRadius ε n
  have hncast : (n : ℝ) = 2*(h : ℝ)-1 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega : 1 ≤ 2*h)]
    push_cast
    ring
  have hnh : (h : ℝ) ≤ (n : ℝ) := by
    rw [hncast]
    have hhr : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hnbig : 24 ≤ ε*(n : ℝ) := by nlinarith [mul_le_mul_of_nonneg_left hnh (le_of_lt he0)]
  have hrad : 0 ≤ ε*(n : ℝ)/4-2 := by linarith
  have hs : 2 ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hsq : s^2 = ε*(2*(h : ℝ)-1)/4-2 := by
    dsimp [s]
    rw [Real.sq_sqrt hrad, hncast]
  have hrlo : s-1 ≤ (r : ℝ) := by
    exact (connectorPrefixRadius_sqrt_sub_one_lt ε n).le
  have hrhi : (r : ℝ) ≤ s := by
    exact Nat.floor_le (Real.sqrt_nonneg _)
  have hhreal : (1 : ℝ) ≤ h := by exact_mod_cast hh
  obtain ⟨hlow,hup,hsquare⟩ := radius_growth_bounds hhreal he0 he1 (by linarith : 16 ≤ ε*(h : ℝ)) hs hsq hrlo hrhi
  have hc : 0 ≤ -Real.log (ε/32)/2 := by
    have hl : Real.log (ε/32) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
    linarith
  have hlog := log_lower_from_square (by positivity : 0 < (h : ℝ))
    (by positivity : 0 < ε/32) (by nlinarith : (ε/32)*(h : ℝ) ≤ (r : ℝ)^2)
  exact ⟨hc,hlow,hup,hlog⟩

/-- Exact floor and explicit O(h²) lower bound, assuming the cyclic endpoint
hypothesis and its cited factorial lower bound for labelled Latin squares. -/
theorem oddCyclicEndpointCompletion_floor_log_lower
    (H9 : OddCyclicRainbowEndpointCompletion) (HLatin : LatinSquareFactorialBound) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          (ε/4)*(h : ℝ)^2*Real.log (h : ℝ) -
            radiusErrorConstant ε*(h : ℝ)^2 ≤
              Real.log (A_h h (hh0.trans hh) : ℝ) := by
  obtain ⟨ε0,he0,n0,H0,_⟩ := oddCyclicEndpointCompletion_floor_total_lower H9
  refine ⟨ε0,he0,n0,H0,?_⟩
  intro ε hε0 hε1
  obtain ⟨h0,hh0,Hcount⟩ := oddCyclicEndpointCompletionAt_floor_total_lower H0 hε0 hε1
  obtain ⟨N,hN⟩ := exists_nat_ge (24/ε)
  refine ⟨max h0 N, by omega, ?_⟩
  intro h hh
  have hh2 : 2 ≤ h := by omega
  have hnh : h ≤ 2*h-1 := by omega
  have h24 : 24 ≤ ε*(h : ℝ) := by
    have hNh : (N : ℝ) ≤ (h : ℝ) := by exact_mod_cast (show N ≤ h by omega)
    have ht : 24 ≤ (N : ℝ)*ε := (div_le_iff₀ hε0).mp hN
    nlinarith
  have hen : 24 ≤ ε*((2*h-1 : ℕ) : ℝ) := by
    have hhn : (h : ℝ) ≤ ((2*h-1 : ℕ) : ℝ) := by exact_mod_cast hnh
    nlinarith [mul_le_mul_of_nonneg_left hhn (le_of_lt hε0)]
  let r := connectorPrefixRadius ε (2*h-1)
  have hr : 2 ≤ r := (connectorPrefixRadius_bounds (hε1.trans (min_le_right _ _)) hen).1
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hc,hlow,hup,hlog⟩ := radius_leading_conditions (by omega : 1 ≤ h)
    hε0 (hε1.trans (min_le_right _ _)) h24
  have hcount : latinSquareCount r ^ h ≤ A_h h hh2 := Hcount h (by omega)
  simpa only [radiusErrorConstant] using
    latin_family_leading_lower HLatin h r hh2 (by omega) ε 5 (-Real.log (ε/32)/2)
      (by norm_num) hc hlow hup hlog hcount

/-- An explicit two-sided eventual bound, hence the asymptotic Θ(h² log h)
order, with the same endpoint and cited Latin-square premises. -/
theorem oddCyclicEndpointCompletion_floor_log_two_sided
    (H9 : OddCyclicRainbowEndpointCompletion) (HLatin : LatinSquareFactorialBound) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          (ε/8)*(h : ℝ)^2*Real.log (h : ℝ) ≤
              Real.log (A_h h (hh0.trans hh) : ℝ) ∧
          Real.log (A_h h (hh0.trans hh) : ℝ) ≤
              2*(h : ℝ)^2*Real.log (h : ℝ) := by
  obtain ⟨ε0,he0,n0,H0,Hbound⟩ := oddCyclicEndpointCompletion_floor_log_lower H9 HLatin
  refine ⟨ε0,he0,n0,H0,?_⟩
  intro ε hε0 hε1
  obtain ⟨h0,hh0,Hlower⟩ := Hbound ε hε0 hε1
  obtain ⟨N,hN⟩ := exists_nat_ge (Real.exp (8*radiusErrorConstant ε/ε))
  refine ⟨max h0 N, by omega, ?_⟩
  intro h hh
  have hh2 : 2 ≤ h := by omega
  have hNh : (N : ℝ) ≤ (h : ℝ) := by exact_mod_cast (show N ≤ h by omega)
  have hexp : Real.exp (8*radiusErrorConstant ε/ε) ≤ (h : ℝ) := hN.trans hNh
  have hlog : 8*radiusErrorConstant ε/ε ≤ Real.log (h : ℝ) :=
    (Real.le_log_iff_exp_le (by positivity : 0 < (h : ℝ))).2 hexp
  have hC : radiusErrorConstant ε ≤ (ε/8)*Real.log (h : ℝ) := by
    have ht := (div_le_iff₀ hε0).mp hlog
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hC (sq_nonneg (h : ℝ))
  have hlower := Hlower h (by omega)
  refine ⟨?_, A_h_log_upper h hh2⟩
  nlinarith

/-- The literal asymptotic Theta conclusion. The explicit endpoint and
published Latin-square premises are exactly those of the lower bound. -/
theorem oddCyclicEndpointCompletion_log_isTheta
    (H9 : OddCyclicRainbowEndpointCompletion) (HLatin : LatinSquareFactorialBound) :
    Asymptotics.IsTheta Filter.atTop logAsymmetricCount entropyScale := by
  obtain ⟨ε0,he0,n0,H0,Hbounds⟩ := oddCyclicEndpointCompletion_floor_log_two_sided H9 HLatin
  let ε : ℝ := min ε0 ((1 : ℝ)/100)/2
  have hmin : 0 < min ε0 ((1 : ℝ)/100) := lt_min he0 (by norm_num)
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ min ε0 ((1 : ℝ)/100) := by dsimp [ε]; linarith
  obtain ⟨h0,hh0,Hbound⟩ := Hbounds ε hε0 hε1
  have hnonneg (h : ℕ) (hh : h0 ≤ h) :
      0 ≤ entropyScale h ∧ 0 ≤ logAsymmetricCount h := by
    have hh2 : 2 ≤ h := hh0.trans hh
    have hlog : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ h by omega))
    have hs : 0 ≤ entropyScale h := mul_nonneg (sq_nonneg _) hlog
    have hlower := (Hbound h hh).1
    have hc : 0 ≤ (ε/8)*entropyScale h := mul_nonneg (by positivity) hs
    constructor
    · exact hs
    · rw [logAsymmetricCount, dif_pos hh2]
      dsimp [entropyScale] at hc
      nlinarith
  constructor
  · apply Asymptotics.IsBigO.of_bound 2
    apply Filter.eventually_atTop.2
    refine ⟨h0, ?_⟩
    intro h hh
    have hh2 : 2 ≤ h := hh0.trans hh
    obtain ⟨hs,hc⟩ := hnonneg h hh
    rw [Real.norm_eq_abs, abs_of_nonneg hc, Real.norm_eq_abs, abs_of_nonneg hs]
    rw [logAsymmetricCount, dif_pos hh2]
    simpa only [entropyScale, mul_assoc] using (Hbound h hh).2
  · apply Asymptotics.IsBigO.of_bound (8/ε)
    apply Filter.eventually_atTop.2
    refine ⟨h0, ?_⟩
    intro h hh
    have hh2 : 2 ≤ h := hh0.trans hh
    obtain ⟨hs,hc⟩ := hnonneg h hh
    rw [Real.norm_eq_abs, abs_of_nonneg hs, Real.norm_eq_abs, abs_of_nonneg hc]
    have hlower := (Hbound h hh).1
    have hd : entropyScale h ≤ (logAsymmetricCount h)/(ε/8) := by
      apply (le_div_iff₀ (by positivity : 0 < ε/8)).2
      rw [logAsymmetricCount, dif_pos hh2]
      dsimp [entropyScale]
      nlinarith
    calc
      entropyScale h ≤ (logAsymmetricCount h)/(ε/8) := hd
      _ = (8/ε)*logAsymmetricCount h := by field_simp

end CorralFormalization.LatinCompletion.TerraceCompletion.Asymptotic
