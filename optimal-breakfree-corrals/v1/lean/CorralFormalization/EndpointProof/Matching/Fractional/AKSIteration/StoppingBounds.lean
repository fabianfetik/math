import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.WasteBounds
import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.DegreeVertexRatio
/-!
# Stopping after the last large-degree step

The displayed AKS bite theorem gives an upper contraction but not, by itself,
a lower bound on the final degree. We count the last step by looking at the
last *preterminal* degree instead. These are numerical lemmas on a supplied
finite sequence, not an existence theorem for graph bites.
-/

open scoped BigOperators

namespace AKSStoppingBounds
noncomputable section

/-- Upper geometric contraction and a lower bound before each step suffice
for a logarithmic step count, including a final degree below one or zero. -/
theorem step_count_from_preterminal (d : ℕ → ℝ) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (m : ℕ) (hstart : 1 ≤ d 0)
    (hstep : ∀ i < m, d (i+1) ≤ θ*d i)
    (hbefore : ∀ i < m, 1 ≤ d i) :
    (m : ℝ) ≤ 1 + Real.log (d 0) / (- Real.log θ) := by
  cases m with
  | zero =>
    have hlog : 0 ≤ Real.log (d 0) := Real.log_nonneg hstart
    have hden : 0 < - Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
    have hdiv : 0 ≤ Real.log (d 0) / (- Real.log θ) := div_nonneg hlog hden.le
    simp only [Nat.cast_zero]
    linarith
  | succ j =>
    have hshort : ∀ i < j, d (i+1) ≤ θ*d i := by
      intro i hi
      exact hstep i (by omega)
    have hlast : 1 ≤ d j := hbefore j (Nat.lt_succ_self j)
    have hcount := AKSNumericalIteration.step_count_le_log d θ hθ0 hθ1 j hshort hlast
    push_cast
    linarith

/-- Summing bounds against the initial logarithmic scale needs no lower
bound on the final degree. -/
theorem total_waste_from_preterminal (d w : ℕ → ℝ) (θ B : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hB : 0 ≤ B) (m : ℕ)
    (hstart : 1 ≤ d 0) (hstep : ∀ i < m, d (i+1) ≤ θ*d i)
    (hbefore : ∀ i < m, 1 ≤ d i)
    (hw : ∀ i < m, w i ≤ B * Real.sqrt (Real.log (d 0))) :
    (∑ i ∈ Finset.range m, w i) ≤
      B * (1 + Real.log (d 0) / (- Real.log θ)) * Real.sqrt (Real.log (d 0)) := by
  have hcount := step_count_from_preterminal d θ hθ0 hθ1 m hstart hstep hbefore
  have hweight : 0 ≤ B * Real.sqrt (Real.log (d 0)) :=
    mul_nonneg hB (Real.sqrt_nonneg _)
  calc
    (∑ i ∈ Finset.range m, w i) ≤
        ∑ _i ∈ Finset.range m, B * Real.sqrt (Real.log (d 0)) := by
      exact Finset.sum_le_sum fun i hi => hw i (Finset.mem_range.mp hi)
    _ = (m : ℝ) * (B * Real.sqrt (Real.log (d 0))) := by simp
    _ ≤ (1 + Real.log (d 0) / (- Real.log θ)) *
        (B * Real.sqrt (Real.log (d 0))) := mul_le_mul_of_nonneg_right hcount hweight
    _ = B * (1 + Real.log (d 0) / (- Real.log θ)) * Real.sqrt (Real.log (d 0)) := by ring

/-- The earlier ratio theorem applies to every preterminal index, even if
the terminal degree itself is zero. -/
theorem source_ratio_before_stopping (d n err u : ℕ → ℝ) (m : ℕ)
    (θ a C L : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hC : 0 ≤ C) (hL : 0 < L)
    (hn : ∀ i ≤ m, 0 ≤ n i) (hu : ∀ i < m, 0 ≤ u i)
    (hstep : ∀ i < m, d (i+1) ≤ θ*d i)
    (hbefore : ∀ i < m, L ≤ d i)
    (herr : ∀ i < m, u i ≤ C/(d i)^a)
    (hbudget : (C/L^a)/(1-θ^a) ≤ 1/2)
    (hsource : ∀ i < m, d (i+1)*n i^2 = d i*n (i+1)^2*(1+err i))
    (herrabs : ∀ i < m, |err i| ≤ u i) :
    ∀ j < m, n j / Real.sqrt (d j) ≤ 2 * (n 0 / Real.sqrt (d 0)) := by
  intro j hj
  have hpositive : ∀ i ≤ j, 0 < d i := by
    intro i hi
    exact lt_of_lt_of_le hL (hbefore i (by omega))
  have h := AKSDegreeVertexRatio.degree_vertex_ratio_from_source_relation
    d n err u j θ a C L hθ0 hθ1 ha hC hL hpositive
    (fun i hi => hn i (by omega)) (fun i hi => hu i (by omega))
    (fun i hi => hstep i (by omega)) (fun i hi => hbefore i (by omega))
    (fun i hi => herr i (by omega)) hbudget
    (fun i hi => hsource i (by omega)) (fun i hi => herrabs i (by omega))
  exact h j le_rfl

/-- Combining the source-shaped ratio relation with the preterminal count
gives the waste-sum bound without a final-degree lower bound. -/
theorem source_waste_before_stopping (d n w err u : ℕ → ℝ) (m : ℕ)
    (θ a C L K : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hK : 0 ≤ K) (hstart : 1 ≤ d 0)
    (hn : ∀ i ≤ m, 0 ≤ n i) (hu : ∀ i < m, 0 ≤ u i)
    (hstep : ∀ i < m, d (i+1) ≤ θ*d i) (hbefore : ∀ i < m, L ≤ d i)
    (herr : ∀ i < m, u i ≤ C/(d i)^a)
    (hbudget : (C/L^a)/(1-θ^a) ≤ 1/2)
    (hsource : ∀ i < m, d (i+1)*n i^2 = d i*n (i+1)^2*(1+err i))
    (herrabs : ∀ i < m, |err i| ≤ u i)
    (hw : ∀ i < m, w i ≤ K*(n i / Real.sqrt (d i))*Real.sqrt (Real.log (d i))) :
    (∑ i ∈ Finset.range m, w i) ≤
      (K*(2*(n 0/Real.sqrt (d 0)))) *
        (1 + Real.log (d 0)/(-Real.log θ)) * Real.sqrt (Real.log (d 0)) := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hscale := source_ratio_before_stopping d n err u m θ a C L hθ0 hθ1 ha
    hC hLpos hn hu hstep hbefore herr hbudget hsource herrabs
  have hB : 0 ≤ K*(2*(n 0/Real.sqrt (d 0))) := by
    have := hn 0 (Nat.zero_le m)
    positivity
  apply total_waste_from_preterminal d w θ (K*(2*(n 0/Real.sqrt (d 0))))
    hθ0 hθ1 hB m hstart hstep (fun i hi => hL.trans (hbefore i hi))
  intro i hi
  have hdi : 0 < d i := lt_of_lt_of_le hLpos (hbefore i hi)
  have hgeo := AKSNumericalIteration.iterate_le_geometric d θ hθ0.le i
    (fun j hj => hstep j (by omega))
  have hpow : θ^i ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
  have hd0 : 0 ≤ d 0 := by linarith
  have hdi0 : d i ≤ d 0 := by nlinarith
  have hlog : Real.log (d i) ≤ Real.log (d 0) := Real.log_le_log hdi hdi0
  have hsqrt := Real.sqrt_le_sqrt hlog
  calc
    w i ≤ K*(n i / Real.sqrt (d i))*Real.sqrt (Real.log (d i)) := hw i hi
    _ ≤ (K*(2*(n 0/Real.sqrt (d 0))))*Real.sqrt (Real.log (d 0)) := by
      gcongr
      exact hscale i hi

/-- The existing error budget makes every preterminal relative degree
error larger than -1; no independent positive-factor assumption is needed. -/
theorem error_gt_neg_one_from_budget (θ a C L d u err : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a) (_hC : 0 ≤ C)
    (hL : 0 < L) (hLd : L ≤ d)
    (hbudget : (C/L^a)/(1-θ^a) ≤ 1/2)
    (hu : u ≤ C/d^a) (herr : |err| ≤ u) : -1 < err := by
  have hθpow0 : 0 ≤ θ^a := (Real.rpow_pos_of_pos hθ0 a).le
  have hθpow1 : θ^a < 1 := Real.rpow_lt_one hθ0.le hθ1 ha
  have hden : 0 < 1-θ^a := by linarith
  have hLp : 0 < L^a := Real.rpow_pos_of_pos hL a
  have hd : 0 < d := lt_of_lt_of_le hL hLd
  have hdp : 0 < d^a := Real.rpow_pos_of_pos hd a
  have hpower : L^a ≤ d^a := Real.rpow_le_rpow hL.le hLd ha.le
  have hb := (div_le_iff₀ hden).1 hbudget
  have hsmallL : C/L^a ≤ 1/2 := by nlinarith
  have hCbound := (div_le_iff₀ hLp).1 hsmallL
  have hsmalld : C/d^a ≤ 1/2 := by
    apply (div_le_iff₀ hdp).2
    nlinarith
  have habs : |err| ≤ (1:ℝ)/2 := herr.trans (hu.trans hsmalld)
  have hlo := (abs_le.mp habs).1
  linarith

/-- The terminal inventory bound also covers a zero terminal degree.
In that case the source relation and its already-paid error budget force
the terminal vertex count to vanish. -/
theorem source_terminal_allow_zero (d n err u : ℕ → ℝ) (m : ℕ)
    (θ a C L : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hC : 0 ≤ C) (hL : 0 < L) (hd0 : 0 < d 0)
    (hdend : 0 ≤ d m) (hstop : d m ≤ L)
    (hn : ∀ i ≤ m, 0 ≤ n i) (hu : ∀ i < m, 0 ≤ u i)
    (hstep : ∀ i < m, d (i+1) ≤ θ*d i) (hbefore : ∀ i < m, L ≤ d i)
    (herr : ∀ i < m, u i ≤ C/(d i)^a)
    (hbudget : (C/L^a)/(1-θ^a) ≤ 1/2)
    (hsource : ∀ i < m, d (i+1)*n i^2 = d i*n (i+1)^2*(1+err i))
    (herrabs : ∀ i < m, |err i| ≤ u i) :
    n m ≤ (2*(n 0/Real.sqrt (d 0)))*Real.sqrt L := by
  by_cases hpositive : 0 < d m
  · have hd : ∀ i ≤ m, 0 < d i := by
      intro i hi
      by_cases heq : i = m
      · simpa [heq] using hpositive
      · exact lt_of_lt_of_le hL (hbefore i (by omega))
    have hratio := AKSDegreeVertexRatio.degree_vertex_ratio_from_source_relation
      d n err u m θ a C L hθ0 hθ1 ha hC hL hd hn hu hstep hbefore herr
      hbudget hsource herrabs m le_rfl
    exact AKSDegreeVertexRatio.terminal_inventory_from_ratio d n m L hpositive
      (hn 0 (Nat.zero_le m)) (hn m le_rfl) hd0 hstop hratio
  · have hzero : d m = 0 := le_antisymm (le_of_not_gt hpositive) hdend
    cases m with
    | zero =>
      linarith
    | succ j =>
      have hj : j < j+1 := Nat.lt_succ_self j
      have hDj : 0 < d j := lt_of_lt_of_le hL (hbefore j hj)
      have herrgt := error_gt_neg_one_from_budget θ a C L (d j) (u j) (err j)
        hθ0 hθ1 ha hC hL (hbefore j hj) hbudget (herr j hj) (herrabs j hj)
      have hfactor : 0 < 1+err j := by linarith
      have hprod : d j*n (j+1)^2*(1+err j) = 0 := by
        simpa [hzero] using (hsource j hj).symm
      have hsquare : n (j+1)^2 = 0 := by
        rcases mul_eq_zero.mp hprod with h | h
        · exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hDj)
        · exact False.elim ((ne_of_gt hfactor) h)
      have hnzero : n (j+1) = 0 := sq_eq_zero_iff.mp hsquare
      rw [hnzero]
      have hn0 := hn 0 (Nat.zero_le _)
      positivity

/-- Total numerical waste plus terminal inventory has the AKS three-uniform
rate under the source-shaped step assumptions, without any lower bound on
the final degree. The constants are explicit in `θ`, `L` and `K`. -/
theorem source_total_without_terminal_lower (d n w err u : ℕ → ℝ) (m : ℕ)
    (θ a C L K : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hK : 0 ≤ K)
    (hstart : Real.exp 1 ≤ d 0) (hdend : 0 ≤ d m) (hstop : d m ≤ L)
    (hn : ∀ i ≤ m, 0 ≤ n i) (hu : ∀ i < m, 0 ≤ u i)
    (hstep : ∀ i < m, d (i+1) ≤ θ*d i) (hbefore : ∀ i < m, L ≤ d i)
    (herr : ∀ i < m, u i ≤ C/(d i)^a)
    (hbudget : (C/L^a)/(1-θ^a) ≤ 1/2)
    (hsource : ∀ i < m, d (i+1)*n i^2 = d i*n (i+1)^2*(1+err i))
    (herrabs : ∀ i < m, |err i| ≤ u i)
    (hw : ∀ i < m, w i ≤ K*(n i/Real.sqrt (d i))*Real.sqrt (Real.log (d i))) :
    (∑ i ∈ Finset.range m, w i) + n m ≤
      (2*(n 0/Real.sqrt (d 0))) * (K*(1+1/(-Real.log θ))+Real.sqrt L) *
        (Real.log (d 0)*Real.sqrt (Real.log (d 0))) := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hd0 : 0 < d 0 := lt_of_lt_of_le (Real.exp_pos 1) hstart
  have hstart1 : 1 ≤ d 0 := by
    have he : (1:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    exact he.trans hstart
  have hwaste := source_waste_before_stopping d n w err u m θ a C L K
    hθ0 hθ1 ha hC hL hK hstart1 hn hu hstep hbefore herr hbudget hsource herrabs hw
  have hterminal := source_terminal_allow_zero d n err u m θ a C L
    hθ0 hθ1 ha hC hLpos hd0 hdend hstop hn hu hstep hbefore herr hbudget hsource herrabs
  have hlog : 1 ≤ Real.log (d 0) := by
    have h := Real.log_le_log (Real.exp_pos 1) hstart
    simpa using h
  have hsqrt : 1 ≤ Real.sqrt (Real.log (d 0)) := by
    have h := Real.sqrt_le_sqrt hlog
    simpa using h
  have hscale : 1 ≤ Real.log (d 0)*Real.sqrt (Real.log (d 0)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (sub_nonneg.mpr hsqrt)]
  have hB : 0 ≤ 2*(n 0/Real.sqrt (d 0)) := by
    have h := hn 0 (Nat.zero_le m)
    positivity
  have hterm0 : 0 ≤ (2*(n 0/Real.sqrt (d 0)))*Real.sqrt L :=
    mul_nonneg hB (Real.sqrt_nonneg _)
  have hterm : (2*(n 0/Real.sqrt (d 0)))*Real.sqrt L ≤
      ((2*(n 0/Real.sqrt (d 0)))*Real.sqrt L) *
        (Real.log (d 0)*Real.sqrt (Real.log (d 0))) := by
    have h := mul_le_mul_of_nonneg_left hscale hterm0
    simpa only [mul_one] using h
  have hfactor : 1 + Real.log (d 0)/(-Real.log θ) ≤
      (1+1/(-Real.log θ))*Real.log (d 0) := by
    calc
      _ ≤ Real.log (d 0) + Real.log (d 0)/(-Real.log θ) := by linarith
      _ = _ := by ring
  have hwaste' : (K*(2*(n 0/Real.sqrt (d 0)))) *
          (1 + Real.log (d 0)/(-Real.log θ)) * Real.sqrt (Real.log (d 0)) ≤
      (K*(2*(n 0/Real.sqrt (d 0)))) *
          ((1+1/(-Real.log θ))*Real.log (d 0)) * Real.sqrt (Real.log (d 0)) := by
    gcongr
  calc
    _ ≤ (K*(2*(n 0/Real.sqrt (d 0)))) *
          (1 + Real.log (d 0)/(-Real.log θ)) * Real.sqrt (Real.log (d 0)) +
        (2*(n 0/Real.sqrt (d 0)))*Real.sqrt L := add_le_add hwaste hterminal
    _ ≤ (K*(2*(n 0/Real.sqrt (d 0)))) *
          ((1+1/(-Real.log θ))*Real.log (d 0)) * Real.sqrt (Real.log (d 0)) +
        ((2*(n 0/Real.sqrt (d 0)))*Real.sqrt L) *
          (Real.log (d 0)*Real.sqrt (Real.log (d 0))) := add_le_add hwaste' hterm
    _ = _ := by ring

end
end AKSStoppingBounds
