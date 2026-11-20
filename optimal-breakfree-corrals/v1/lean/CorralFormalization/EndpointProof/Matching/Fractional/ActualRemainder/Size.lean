import CorralFormalization.EndpointProof.Matching.Fractional.RoundingAKSBounds

/-!
# The actual square-root/logarithmic remainder bill

This is a finite, explicit comparison.  The input size and integer degree
inequalities are visible; no asymptotic target-size estimate is assumed
silently.  They are the inequalities used with `D = floor (2qm/3)` for the quantitative remainder estimate.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.ActualRemainder

open EndpointMatching.Fractional.Rounding

noncomputable section

/-- The paper's per-role square-root/logarithmic size profile. -/
def remainderProfile (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * (Real.log (Real.exp 1 * (n : ℝ))) ^ (3 / 2 : ℝ)

/-- The literal integer scale used in the manuscript. -/
def explicitDegree (q : ℝ) (m : ℕ) : ℕ := ⌊2 * q * (m : ℝ) / 3⌋₊

/-- The floor loses less than one; once `qm ≥ 3`, its scale is at least
`qm/3`.  Both bounds concern the actual, unpadded role size `m`. -/
theorem explicitDegree_scale (q : ℝ) (m : ℕ) (hd : 3 ≤ q * (m : ℝ)) :
    q * (m : ℝ) ≤ 3 * (explicitDegree q m : ℝ) ∧
      (explicitDegree q m : ℝ) ≤ 2 * q * (m : ℝ) / 3 := by
  have hnonneg : 0 ≤ 2 * q * (m : ℝ) / 3 := by linarith
  have hupper := Nat.floor_le hnonneg
  have hlower := Nat.lt_floor_add_one (2 * q * (m : ℝ) / 3)
  dsimp [explicitDegree]
  constructor
  · linarith
  · exact hupper

/-- Explicit scale/threshold payment from the usual raw-size collar.
This isolates the only sufficiently-large-order requirement needed for
the degree choice, apart from the separately proved remainder capacity. -/
theorem explicitDegree_conditions (q : ℝ) (n m Dstar : ℕ)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hstar : 3 ≤ Dstar)
    (hlower : q * (n : ℝ) / 2 ≤ (m : ℝ))
    (hupper : (m : ℝ) ≤ 2 * q * (n : ℝ))
    (hlarge : 6 * (Dstar : ℝ) ≤ q ^ 2 * (n : ℝ)) :
    Dstar ≤ explicitDegree q m ∧ q * (m : ℝ) ≤ 3 * (explicitDegree q m : ℝ) ∧
      explicitDegree q m ≤ n := by
  have hstar' : (3 : ℝ) ≤ Dstar := by exact_mod_cast hstar
  have hqm : 3 * (Dstar : ℝ) ≤ q * (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlower hq.le
    nlinarith
  have hd : 3 ≤ q * (m : ℝ) := by linarith
  have hscale := explicitDegree_scale q m hd
  have hDstar : Dstar ≤ explicitDegree q m := by
    apply Nat.le_floor
    nlinarith
  refine ⟨hDstar, hscale.1, ?_⟩
  apply Nat.floor_le_of_le
  have hq2 : q * q ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
    mul_le_mul hqhalf hqhalf hq.le (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hupper hq.le
  have hq2n := mul_le_mul_of_nonneg_right hq2 (Nat.cast_nonneg n)
  nlinarith

/-- The numerator comparison is paid independently of the degree choice. -/
theorem log_sqrt_le_log_rpow {D n : ℝ} (hD : 1 ≤ D) (hDn : D ≤ n) :
    Real.log (Real.exp 1 * D) * Real.sqrt (Real.log (Real.exp 1 * D)) ≤
      (Real.log (Real.exp 1 * n)) ^ (3 / 2 : ℝ) := by
  have hDpos : 0 < D := by linarith
  have hnpos : 0 < n := hDpos.trans_le hDn
  have hlogD : 0 < Real.log (Real.exp 1 * D) := by
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hDpos), Real.log_exp]
    linarith [Real.log_nonneg hD]
  have hlog : Real.log (Real.exp 1 * D) ≤ Real.log (Real.exp 1 * n) :=
    Real.log_le_log (mul_pos (Real.exp_pos 1) hDpos)
      (mul_le_mul_of_nonneg_left hDn (Real.exp_pos 1).le)
  have hlogn : 0 < Real.log (Real.exp 1 * n) := hlogD.trans_le hlog
  calc
    _ ≤ Real.log (Real.exp 1 * n) * Real.sqrt (Real.log (Real.exp 1 * n)) :=
      mul_le_mul hlog (Real.sqrt_le_sqrt hlog) (Real.sqrt_nonneg _) hlogn.le
    _ = _ := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
        Real.rpow_add hlogn, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- The precise finite comparison producing `C₀ = sqrt 6 * Cstar`.
All three scale hypotheses are explicit. -/
theorem diffuse_role_bound_le_profile (C q : ℝ) (n m D : ℕ)
    (hC : 0 ≤ C) (_hq : 0 < q) (hD : 1 ≤ D)
    (hm : (m : ℝ) ≤ 2 * q * (n : ℝ))
    (hdegree : q * (m : ℝ) ≤ 3 * (D : ℝ)) (hDn : D ≤ n) :
    C * (m : ℝ) * diffuseRate D ≤ Real.sqrt 6 * C * remainderProfile n := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hDn' : (D : ℝ) ≤ n := by exact_mod_cast hDn
  have hn : (0 : ℝ) < n := hDpos.trans_le hDn'
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDroot : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.2 hDpos
  have hm2 : (m : ℝ) ^ 2 ≤ 6 * (n : ℝ) * (D : ℝ) := by
    have hm' := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg m)
    have hd' := mul_le_mul_of_nonneg_left hdegree (show 0 ≤ 2 * (n : ℝ) by positivity)
    nlinarith
  have hroot : (m : ℝ) / Real.sqrt (D : ℝ) ≤ Real.sqrt 6 * Real.sqrt (n : ℝ) := by
    apply (div_le_iff₀ hDroot).mpr
    have hsix : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
    have hnsq := Real.sq_sqrt hn.le
    have hDsq := Real.sq_sqrt hDpos.le
    have hnonneg : 0 ≤ Real.sqrt 6 * Real.sqrt (n : ℝ) * Real.sqrt (D : ℝ) := by positivity
    have hsq : (Real.sqrt 6 * Real.sqrt (n : ℝ) * Real.sqrt (D : ℝ)) ^ 2 =
        6 * (n : ℝ) * (D : ℝ) := by
      rw [mul_pow, mul_pow, hsix, hnsq, hDsq]
    nlinarith [sq_nonneg ((m : ℝ) - Real.sqrt 6 * Real.sqrt (n : ℝ) * Real.sqrt (D : ℝ))]
  have hnum := log_sqrt_le_log_rpow hD1 hDn'
  have hlognonneg : 0 ≤ Real.log (Real.exp 1 * (n : ℝ)) := by
    have hOne : (1 : ℝ) ≤ n := le_trans hD1 hDn'
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hn), Real.log_exp]
    linarith [Real.log_nonneg hOne]
  have hlogpow : 0 ≤ (Real.log (Real.exp 1 * (n : ℝ))) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hlognonneg _
  have hlogDnonneg : 0 ≤ Real.log (Real.exp 1 * (D : ℝ)) := by
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hDpos), Real.log_exp]
    linarith [Real.log_nonneg hD1]
  rw [diffuseRate_eq_log_exp _ hDpos]
  calc
    _ = C * ((m : ℝ) / Real.sqrt (D : ℝ)) *
        (Real.log (Real.exp 1 * (D : ℝ)) * Real.sqrt (Real.log (Real.exp 1 * (D : ℝ)))) := by ring
    _ ≤ C * (Real.sqrt 6 * Real.sqrt (n : ℝ)) *
        (Real.log (Real.exp 1 * (n : ℝ))) ^ (3 / 2 : ℝ) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hroot hC
      · exact hnum
      · positivity
      · positivity
    _ = Real.sqrt 6 * C * remainderProfile n := by unfold remainderProfile; ring

end
end EndpointMatching.Fractional.ActualRemainder
