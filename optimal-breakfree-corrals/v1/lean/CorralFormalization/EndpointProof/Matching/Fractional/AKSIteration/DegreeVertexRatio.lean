import Mathlib

/-!
A bounded-product step for the deterministic AKS iteration. The theorem
below proves a uniform ratio bound from an explicit relative-error budget.
It does not assert the existence of AKS bites or that the paper's source
automatically supplies the quantified budget.
-/

open scoped BigOperators
open Filter

namespace AKSDegreeVertexRatio
noncomputable section

/-- A nonnegative sequence satisfying the squared one-step ratio relation
remains uniformly bounded whenever the total relative error is at most 1/2. -/
theorem ratio_bound_from_error_sum (r u : ℕ → ℝ) (m : ℕ)
    (hr : ∀ i ≤ m, 0 ≤ r i)
    (hu : ∀ i < m, 0 ≤ u i)
    (hsum : (∑ i ∈ Finset.range m, u i) ≤ 1/2)
    (hstep : ∀ i < m, (r (i+1))^2 * (1-u i) ≤ (r i)^2) :
    ∀ j ≤ m, r j ≤ 2 * r 0 := by
  have hprefix (j : ℕ) (hj : j ≤ m) :
      (∑ i ∈ Finset.range j, u i) ≤ 1/2 := by
    have hs : Finset.range j ⊆ Finset.range m := Finset.range_mono hj
    have hm := Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun i hi _ => hu i (Finset.mem_range.mp hi))
    exact hm.trans hsum
  have hinvariant : ∀ j ≤ m,
      (1 - ∑ i ∈ Finset.range j, u i) * (r j)^2 ≤ (r 0)^2 := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hjm : j < m := by omega
      have hprev := ih (by omega)
      have hnonneg : 0 ≤ ∑ i ∈ Finset.range j, u i := by
        apply Finset.sum_nonneg
        intro i hi
        exact hu i (by have := Finset.mem_range.mp hi; omega)
      have hcoef : 0 ≤ 1 - ∑ i ∈ Finset.range j, u i := by
        have := hprefix j (by omega)
        linarith
      have hmul := mul_le_mul_of_nonneg_left (hstep j hjm) hcoef
      have hprod : 0 ≤ (∑ i ∈ Finset.range j, u i) * u j * (r (j+1))^2 := by
        exact mul_nonneg (mul_nonneg hnonneg (hu j hjm)) (sq_nonneg _)
      rw [Finset.sum_range_succ]
      nlinarith
  intro j hj
  have hprev := hinvariant j hj
  have hsum' := hprefix j hj
  have hsquare : (r j)^2 ≤ 2*(r 0)^2 := by nlinarith [sq_nonneg (r j)]
  by_contra hnot
  have hgt : 2*r 0 < r j := lt_of_not_ge hnot
  have hr0 : 0 ≤ r 0 := hr 0 (Nat.zero_le m)
  have hsq : (2*r 0)^2 < (r j)^2 :=
    (sq_lt_sq₀ (mul_nonneg (by norm_num) hr0) (hr j hj)).2 hgt
  nlinarith [sq_nonneg (r 0)]

/-- Source-shaped version: the cross-multiplied one-step `D`/`N` relation
and the error-sum budget imply `N_j / sqrt(D_j) <= 2 N_0 / sqrt(D_0)`.
The positivity and error budget are explicit inputs. -/
theorem degree_vertex_ratio_bound (d n u : ℕ → ℝ) (m : ℕ)
    (hd : ∀ i ≤ m, 0 < d i) (hn : ∀ i ≤ m, 0 ≤ n i)
    (hu : ∀ i < m, 0 ≤ u i)
    (hsum : (∑ i ∈ Finset.range m, u i) ≤ 1/2)
    (hcross : ∀ i < m,
      (1-u i) * d i * (n (i+1))^2 ≤ d (i+1) * (n i)^2) :
    ∀ j ≤ m, n j / Real.sqrt (d j) ≤ 2 * (n 0 / Real.sqrt (d 0)) := by
  let r := fun i => n i / Real.sqrt (d i)
  have hr : ∀ i ≤ m, 0 ≤ r i := by
    intro i hi
    exact div_nonneg (hn i hi) (Real.sqrt_nonneg _)
  have hstep : ∀ i < m, (r (i+1))^2 * (1-u i) ≤ (r i)^2 := by
    intro i hi
    have hdi := hd i (by omega)
    have hdnext := hd (i+1) (by omega)
    dsimp [r]
    calc
      _ = ((n (i+1))^2 * (1-u i)) / d (i+1) := by
        rw [div_pow, Real.sq_sqrt (le_of_lt hdnext)]
        ring
      _ ≤ (n i)^2 / d i := by
        apply (div_le_div_iff₀ hdnext hdi).2
        nlinarith [hcross i hi]
      _ = (n i / Real.sqrt (d i))^2 := by
        rw [div_pow, Real.sq_sqrt (le_of_lt hdi)]
  exact ratio_bound_from_error_sum r u m hr hu hsum hstep

/-- A reversed geometric error envelope has a total cost bounded
independently of the number of rounds. -/
theorem reversed_geometric_error_sum (u : ℕ → ℝ) (m : ℕ) (c ρ : ℝ)
    (hc : 0 ≤ c) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (henv : ∀ i < m, u i ≤ c * ρ ^ (m-1-i)) :
    (∑ i ∈ Finset.range m, u i) ≤ c / (1-ρ) := by
  have hgeom : (∑ i ∈ Finset.range m, ρ ^ i) ≤ 1 / (1-ρ) := by
    have hident := geom_sum_mul_neg ρ m
    have hpow : 0 ≤ ρ ^ m := pow_nonneg hρ0 _
    apply (le_div_iff₀ (by linarith : 0 < 1-ρ)).2
    nlinarith [hident]
  calc
    (∑ i ∈ Finset.range m, u i) ≤
        ∑ i ∈ Finset.range m, c * ρ ^ (m-1-i) := by
      exact Finset.sum_le_sum fun i hi => henv i (Finset.mem_range.mp hi)
    _ = ∑ i ∈ Finset.range m, c * ρ ^ i :=
      Finset.sum_range_reflect (fun i => c * ρ ^ i) m
    _ = c * ∑ i ∈ Finset.range m, ρ ^ i := by rw [Finset.mul_sum]
    _ ≤ c * (1 / (1-ρ)) := mul_le_mul_of_nonneg_left hgeom hc
    _ = c / (1-ρ) := by ring

/-- The source-shaped ratio remains uniformly bounded if the relative
errors have a sufficiently small reverse-geometric envelope. -/
theorem degree_vertex_ratio_from_geometric_errors (d n u : ℕ → ℝ) (m : ℕ)
    (c ρ : ℝ) (hc : 0 ≤ c) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hd : ∀ i ≤ m, 0 < d i) (hn : ∀ i ≤ m, 0 ≤ n i)
    (hu : ∀ i < m, 0 ≤ u i)
    (henv : ∀ i < m, u i ≤ c * ρ ^ (m-1-i))
    (hbudget : c / (1-ρ) ≤ 1/2)
    (hcross : ∀ i < m,
      (1-u i) * d i * (n (i+1))^2 ≤ d (i+1) * (n i)^2) :
    ∀ j ≤ m, n j / Real.sqrt (d j) ≤ 2 * (n 0 / Real.sqrt (d 0)) := by
  apply degree_vertex_ratio_bound d n u m hd hn hu
    ((reversed_geometric_error_sum u m c ρ hc hρ0 hρ1 henv).trans hbudget) hcross

/-- Shifted version of the geometric degree contraction. -/
theorem degree_at_shift_le (d : ℕ → ℝ) (θ : ℝ) (m i k : ℕ)
    (hθ : 0 ≤ θ) (hik : i+k ≤ m)
    (hstep : ∀ j < m, d (j+1) ≤ θ * d j) :
    d (i+k) ≤ d i * θ^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hi : i+k < m := by omega
    have hprev := ih (by omega)
    have hs := hstep (i+k) hi
    have hm := mul_le_mul_of_nonneg_left hprev hθ
    rw [pow_succ]
    have hid : i + (k+1) = i+k+1 := by omega
    rw [hid]
    nlinarith

/-- In a geometrically shrinking sequence, an error of order `d_i^(-a)`
has a reverse-geometric envelope determined by the terminal step degree. -/
theorem degree_error_envelope (d u : ℕ → ℝ) (m : ℕ) (θ a C L : ℝ)
    (hθ0 : 0 < θ) (ha : 0 ≤ a) (hC : 0 ≤ C) (hL : 0 < L)
    (hd : ∀ i < m, 0 < d i)
    (hstep : ∀ i < m, d (i+1) ≤ θ * d i)
    (hterminal : ∀ i < m, L ≤ d i)
    (herr : ∀ i < m, u i ≤ C / (d i)^a) :
    ∀ i < m, u i ≤ (C / L^a) * (θ^a)^(m-1-i) := by
  intro i hi
  let k := m-1-i
  have hk : i+k = m-1 := by dsimp [k]; omega
  have hm1 : m-1 < m := by omega
  have hshift := degree_at_shift_le d θ m i k hθ0.le (by omega) hstep
  rw [hk] at hshift
  have hLle : L ≤ d i * θ^k := (hterminal (m-1) hm1).trans hshift
  have hpowpos : 0 < θ^k := pow_pos hθ0 k
  have hdpos : 0 < d i := hd i hi
  have hpow : (θ^k)^a = (θ^a)^k := by
    rw [← Real.rpow_natCast θ k, ← Real.rpow_mul hθ0.le,
      mul_comm, Real.rpow_mul hθ0.le, Real.rpow_natCast]
  have hLr := Real.rpow_le_rpow hL.le hLle ha
  rw [Real.mul_rpow hdpos.le hpowpos.le, hpow] at hLr
  have hLapos : 0 < L^a := Real.rpow_pos_of_pos hL a
  have hdiapos : 0 < (d i)^a := Real.rpow_pos_of_pos hdpos a
  have hmul := mul_le_mul_of_nonneg_left hLr hC
  have hfrac : C / (d i)^a ≤ (C * (θ^a)^k) / L^a := by
    apply (div_le_div_iff₀ hdiapos hLapos).2
    nlinarith
  have hfinal : (C * (θ^a)^k) / L^a = (C / L^a) * (θ^a)^k := by ring
  exact (herr i hi).trans (by rw [hfinal] at hfrac; simpa [k] using hfrac)

/-- From geometrically decreasing positive degrees, source-shaped errors
`u_i <= C D_i^(-a)`, and an explicit terminal threshold, obtain the
uniform `N_i / sqrt(D_i)` estimate without assuming that estimate. -/
theorem degree_vertex_ratio_from_power_errors (d n u : ℕ → ℝ) (m : ℕ)
    (θ a C L : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hC : 0 ≤ C) (hL : 0 < L)
    (hd : ∀ i ≤ m, 0 < d i) (hn : ∀ i ≤ m, 0 ≤ n i)
    (hu : ∀ i < m, 0 ≤ u i)
    (hstep : ∀ i < m, d (i+1) ≤ θ * d i)
    (hterminal : ∀ i < m, L ≤ d i)
    (herr : ∀ i < m, u i ≤ C / (d i)^a)
    (hbudget : (C / L^a) / (1-θ^a) ≤ 1/2)
    (hcross : ∀ i < m,
      (1-u i) * d i * (n (i+1))^2 ≤ d (i+1) * (n i)^2) :
    ∀ j ≤ m, n j / Real.sqrt (d j) ≤ 2 * (n 0 / Real.sqrt (d 0)) := by
  have hρ0 : 0 ≤ θ^a := (Real.rpow_pos_of_pos hθ0 a).le
  have hρ1 : θ^a < 1 := Real.rpow_lt_one hθ0.le hθ1 ha
  have hc : 0 ≤ C / L^a := div_nonneg hC (Real.rpow_pos_of_pos hL a).le
  have henv := degree_error_envelope d u m θ a C L hθ0 ha.le hC hL
    (fun i hi => hd i (by omega)) hstep hterminal herr
  exact degree_vertex_ratio_from_geometric_errors d n u m (C / L^a) (θ^a)
    hc hρ0 hρ1 hd hn hu henv hbudget hcross

/-- The exact cross-multiplied AKS step relation with a two-sided relative
error yields the preceding uniform ratio bound. Positivity, geometric
contraction, the power-error envelope and the threshold budget are explicit. -/
theorem degree_vertex_ratio_from_source_relation (d n err u : ℕ → ℝ) (m : ℕ)
    (θ a C L : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hC : 0 ≤ C) (hL : 0 < L)
    (hd : ∀ i ≤ m, 0 < d i) (hn : ∀ i ≤ m, 0 ≤ n i)
    (hu : ∀ i < m, 0 ≤ u i)
    (hstep : ∀ i < m, d (i+1) ≤ θ * d i)
    (hterminal : ∀ i < m, L ≤ d i)
    (herr : ∀ i < m, u i ≤ C / (d i)^a)
    (hbudget : (C / L^a) / (1-θ^a) ≤ 1/2)
    (hsource : ∀ i < m,
      d (i+1) * (n i)^2 = d i * (n (i+1))^2 * (1+err i))
    (herrabs : ∀ i < m, |err i| ≤ u i) :
    ∀ j ≤ m, n j / Real.sqrt (d j) ≤ 2 * (n 0 / Real.sqrt (d 0)) := by
  apply degree_vertex_ratio_from_power_errors d n u m θ a C L hθ0 hθ1 ha
    hC hL hd hn hu hstep hterminal herr hbudget
  intro i hi
  have hlo : -u i ≤ err i := (abs_le.mp (herrabs i hi)).1
  have hnonneg : 0 ≤ d i * (n (i+1))^2 * (err i + u i) :=
    mul_nonneg (mul_nonneg (hd i (by omega)).le (sq_nonneg _)) (by linarith)
  nlinarith [hsource i hi]

/-- For fixed source constants the terminal threshold can be chosen large
enough to pay the accumulated relative-error budget. -/
theorem exists_terminal_threshold (θ a C : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a) (hC : 0 ≤ C) :
    ∃ L : ℝ, 1 ≤ L ∧ (C / L^a) / (1-θ^a) ≤ 1/2 := by
  have hden : 0 < 1-θ^a := by
    have := Real.rpow_lt_one hθ0.le hθ1 ha
    linarith
  obtain ⟨x, hx⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop ha))
    (2*C/(1-θ^a))
  let L : ℝ := max x 1
  have hL : 1 ≤ L := le_max_right _ _
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hp : 0 < L^a := Real.rpow_pos_of_pos hLpos a
  have hlarge : 2*C/(1-θ^a) ≤ L^a := hx L (le_max_left _ _)
  refine ⟨L,hL,?_⟩
  apply (div_le_iff₀ hden).2
  apply (div_le_iff₀ hp).2
  have h := (div_le_iff₀ hden).1 hlarge
  nlinarith

/-- The bound on the ratio also bounds the terminal inventory once the
terminal degree falls below the chosen threshold. -/
theorem terminal_inventory_from_ratio (d n : ℕ → ℝ) (m : ℕ) (L : ℝ)
    (hd : 0 < d m) (hn0 : 0 ≤ n 0) (hnm : 0 ≤ n m)
    (hd0 : 0 < d 0) (hL : d m ≤ L)
    (hratio : n m / Real.sqrt (d m) ≤ 2 * (n 0 / Real.sqrt (d 0))) :
    n m ≤ (2 * (n 0 / Real.sqrt (d 0))) * Real.sqrt L := by
  have hsqrt : Real.sqrt (d m) ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
  have hdroot : 0 < Real.sqrt (d m) := Real.sqrt_pos.2 hd
  have hb : 0 ≤ 2 * (n 0 / Real.sqrt (d 0)) := by positivity
  calc
    n m = (n m / Real.sqrt (d m)) * Real.sqrt (d m) := by
      field_simp
    _ ≤ (2 * (n 0 / Real.sqrt (d 0))) * Real.sqrt (d m) :=
      mul_le_mul_of_nonneg_right hratio hdroot.le
    _ ≤ (2 * (n 0 / Real.sqrt (d 0))) * Real.sqrt L :=
      mul_le_mul_of_nonneg_left hsqrt hb

/-- One terminal threshold depends only on the source constants and works
uniformly for all finite sequences satisfying the source-shaped relation. -/
theorem source_ratio_uniform_threshold (θ a C : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a) (hC : 0 ≤ C) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (m : ℕ) (d n err u : ℕ → ℝ),
      (∀ i ≤ m, 0 < d i) → (∀ i ≤ m, 0 ≤ n i) →
      (∀ i < m, 0 ≤ u i) →
      (∀ i < m, d (i+1) ≤ θ * d i) →
      (∀ i < m, L ≤ d i) →
      (∀ i < m, u i ≤ C / (d i)^a) →
      (∀ i < m, d (i+1) * (n i)^2 = d i * (n (i+1))^2 * (1+err i)) →
      (∀ i < m, |err i| ≤ u i) →
      ∀ j ≤ m, n j / Real.sqrt (d j) ≤ 2 * (n 0 / Real.sqrt (d 0)) := by
  obtain ⟨L,hL,hbudget⟩ := exists_terminal_threshold θ a C hθ0 hθ1 ha hC
  refine ⟨L,hL,?_⟩
  intro m d n err u hd hn hu hstep hterminal herr hsource herrabs
  exact degree_vertex_ratio_from_source_relation d n err u m θ a C L hθ0 hθ1 ha
    hC (lt_of_lt_of_le (by norm_num) hL) hd hn hu hstep hterminal herr hbudget hsource herrabs

end
end AKSDegreeVertexRatio
