import CorralFormalization.EndpointProof.Probability.LayeredSample.Joint

/-! The actual `s = n^(2/3)` tolerance and one group-uniform good sample. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointMatching.Fractional.Rounding
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section
universe u

def explicitSizeTolerance (n : ℕ) : ℝ := (n : ℝ)^((2 : ℝ) / 3)

theorem explicitSizeTolerance_nonneg (n : ℕ) : 0 ≤ explicitSizeTolerance n :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem explicitSizeExponent {x : ℝ} (hx : 0 < x) :
    -(x^((2 : ℝ)/3))^2 / (2 * (x/4)) = -2 * x^((1 : ℝ)/3) := by
  have hp : (x^((2 : ℝ)/3))^2 = x^((4 : ℝ)/3) := by
    rw [← Real.rpow_mul_natCast hx.le]
    norm_num
  rw [hp]
  calc
    -x^((4 : ℝ)/3) / (2 * (x/4)) = -2 * (x^((4 : ℝ)/3) / x) := by ring
    _ = -2 * x^((1 : ℝ)/3) := by
      rw [← Real.rpow_sub_one hx.ne']
      norm_num

def explicitFailureBound {m : ℕ} (d : Densities m) (n : ℕ) : ℝ :=
  Real.exp (-((xi d.q)^4 / 10^6) * (n : ℝ)) +
  (n : ℝ) * Real.exp (-(d.q^4 / 8) * (n : ℝ)) +
  (2 * (2 * m + 7 : ℕ) : ℝ) * Real.exp (-2 * (n : ℝ)^((1 : ℝ)/3))

theorem failureBound_explicitSizeTolerance {m : ℕ} (d : Densities m)
    (n : ℕ) (hn : 0 < n) :
    failureBound d (explicitSizeTolerance n) n = explicitFailureBound d n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold failureBound explicitFailureBound explicitSizeTolerance
  rw [explicitSizeExponent hnreal]
  rw [show -d.q^4 * (n : ℝ) / 8 = -(d.q^4 / 8) * (n : ℝ) by ring]

/-- The displayed common failure bound tends to zero at the manuscript's
`n^(2/3)` size tolerance.  This is a numerical fact independent of group
type, vertex/colour query or later target. -/
theorem explicitFailureBound_tendsto_zero {m : ℕ} (d : Densities m) (hq0 : 0 < d.q) :
    Tendsto (explicitFailureBound d) atTop (𝓝 0) := by
  have hxi : 0 < xi d.q := by
    unfold xi kappa tau p rho r0 eta
    positivity
  have hE : Tendsto (fun n : ℕ => Real.exp (-((xi d.q)^4 / 10^6) * (n : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      0 ((xi d.q)^4 / 10^6) (by positivity)).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Real.rpow_zero, one_mul] using h
  have hP : Tendsto (fun n : ℕ =>
      (n : ℝ) * Real.exp (-(d.q^4 / 8) * (n : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      1 (d.q^4 / 8) (by positivity)).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Real.rpow_one] using h
  have hpow : Tendsto (fun n : ℕ => (n : ℝ)^((1 : ℝ)/3)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp tendsto_natCast_atTop_atTop
  have hS : Tendsto (fun n : ℕ => Real.exp (-2 * (n : ℝ)^((1 : ℝ)/3)))
      atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) hpow)
    simpa only [Function.comp_def, neg_mul] using h
  have hC : Tendsto (fun _n : ℕ => (2 * (2 * m + 7 : ℕ) : ℝ)) atTop
      (𝓝 (2 * (2 * m + 7 : ℕ) : ℝ)) := tendsto_const_nhds
  have hsum := (hE.add hP).add (hC.mul hS)
  simp only [add_zero, mul_zero] at hsum
  refine Tendsto.congr ?_ hsum
  intro n
  simp only [explicitFailureBound, Nat.cast_mul, Nat.cast_ofNat]

/-- The categorical sample may be fixed once, before every later query,
with exact-matching, all pair banks and every raw role size simultaneously good.
The threshold is independent of the finite odd abelian group type. -/
theorem exists_goodSample_explicitTolerance
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    {m : ℕ} (d : Densities m) (hq0 : 0 < d.q) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      ∃ s : Sample G m, GoodSample d (explicitSizeTolerance (Fintype.card G)) s := by
  obtain ⟨N, hN⟩ := goodSample_failure_probability hAKS d hq0
  have hsmall : ∀ᶠ n : ℕ in atTop, explicitFailureBound d n < 1 :=
    (tendsto_order.1 (explicitFailureBound_tendsto_zero d hq0)).2 1 (by norm_num)
  obtain ⟨Nsmall, hNsmall⟩ := eventually_atTop.1 hsmall
  refine ⟨max N (max Nsmall 1), ?_⟩
  intro G _ _ hodd hn
  let n := Fintype.card G
  have hn0 : 0 < n := by dsimp [n]; omega
  have hp := hN G hodd (by omega) (explicitSizeTolerance n) (explicitSizeTolerance_nonneg n)
  rw [failureBound_explicitSizeTolerance d n hn0] at hp
  have hs : explicitFailureBound d n < 1 := hNsmall n (by dsimp [n]; omega)
  by_contra hnone
  have heq : {s : Sample G m | ¬ GoodSample d (explicitSizeTolerance n) s} = Set.univ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact fun h => hnone ⟨s, h⟩
  rw [heq, probReal_univ] at hp
  linarith

end
end EndpointLayeredSample
