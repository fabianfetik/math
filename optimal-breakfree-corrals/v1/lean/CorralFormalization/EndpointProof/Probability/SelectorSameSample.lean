import CorralFormalization.EndpointProof.Selector.Assembly.ColoredSelectorAvailability
import CorralFormalization.EndpointProof.Flow.AbelianTransport.CompatibleRing
import CorralFormalization.EndpointProof.Flow.AbelianTransport.AdditiveModel

/-!
# Native selectors on the same augmented sample

The four verified primitive tails give the complete P-selector event under
`parameterizedFullMeasure`. The compatible-ring step preserves the caller's
additive structure and the same `FullSample` throughout; no original-sample
projection or independently selected augmentation is used.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

namespace EndpointFlow.AbelianTransport

open EndpointFullProduct

noncomputable section

/-- Copy the concrete ring selectors, including their actual finite
interiors and matchings, into the purely additive interface on the same ω. -/
theorem colouredSelectors_of_ring_same_sample
    {G : Type*} [Fintype G] [CommRing G] (ω : FullSample G) (C : ℕ)
    (hselectors : EndpointSelector.Assembly.ColouredSelectors ω C) :
    ColouredSelectors ω C := by
  intro part R hne hk hlegal F hF
  obtain ⟨S, hsize, havoid, hsupport⟩ := hselectors part R hne hk hlegal F hF
  exact ⟨selectorOfRing S, hsize, havoid, hsupport⟩

end

end EndpointFlow.AbelianTransport

namespace EndpointFullProduct

open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

/-- Four primitive tails, assembled before every later selector query, on
the actual augmented law. The only reserve is the deterministic 3996-point
support margin required by the existing selector compiler. -/
theorem selector_same_sample_full_error_ring
    {G : Type*} [CommRing G] [Fintype G]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (C : ℕ) (hmargin : C + 3996 ≤ selectorBudget (p q) (Fintype.card G)) :
    (parameterizedFullMeasure G q hq0 hq1).real
      {ω : FullSample G | ¬ EndpointFlow.AbelianTransport.ColouredSelectors ω C} ≤
      6 * ((Fintype.card G : ℝ) ^ 3 + 2 * (Fintype.card G : ℝ) ^ 2 + Fintype.card G) *
        Real.exp (-((p q) ^ 8 / 32000) * (Fintype.card G : ℝ)) := by
  let μ := parameterizedFullMeasure G q hq0 hq1
  have : IsProbabilityMeasure μ := by
    dsimp [μ, parameterizedFullMeasure]
    infer_instance
  let events := EndpointSelector.selectorPrimitiveEvents hodd (by omega)
    (selectorBudget (p q) (Fintype.card G))
  have herror (i : Fin 4) : μ.real {ω | ¬ events i ω} ≤
      6 * (Fintype.card G : ℝ) ^ (![2,1,2,3] : Fin 4 → ℕ) i *
        Real.exp (-((p q) ^ 8 / 32000) * (Fintype.card G : ℝ)) :=
    EndpointSelector.selector_primitive_full_error q hq0 hq1 hodd hn i
  calc
    _ ≤ μ.real (⋃ i : Fin 4, {ω | ¬ events i ω}) := by
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hbad
      by_contra hnot
      have hall : ∀ i, events i ω := by
        intro i
        by_contra hi
        exact hnot (Set.mem_iUnion.mpr ⟨i, hi⟩)
      exact hbad (EndpointFlow.AbelianTransport.colouredSelectors_of_ring_same_sample ω C
        (EndpointSelector.Assembly.coloured_selectors_of_primitives hodd (by omega)
          (selectorBudget (p q) (Fintype.card G)) C hmargin ω hall))
    _ ≤ ∑ i : Fin 4, μ.real {ω | ¬ events i ω} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin 4,
        6 * (Fintype.card G : ℝ) ^ (![2,1,2,3] : Fin 4 → ℕ) i *
          Real.exp (-((p q) ^ 8 / 32000) * (Fintype.card G : ℝ)) :=
      Finset.sum_le_sum (fun i _ => herror i)
    _ = _ := by simp [Fin.sum_univ_four]; ring

/-- The same full-sample bound on the AddCommGroup given by the caller.
The auxiliary ring is internal and its entire additive structure is equal
to the existing one; in particular every ω and the augmented law coincide. -/
theorem selector_same_sample_full_error_abelian
    {G : Type*} [Fintype G] [A : AddCommGroup G]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (C : ℕ) (hmargin : C + 3996 ≤ selectorBudget (p q) (Fintype.card G)) :
    (parameterizedFullMeasure G q hq0 hq1).real
      {ω : FullSample G | ¬ EndpointFlow.AbelianTransport.ColouredSelectors ω C} ≤
      6 * ((Fintype.card G : ℝ) ^ 3 + 2 * (Fintype.card G : ℝ) ^ 2 + Fintype.card G) *
        Real.exp (-((p q) ^ 8 / 32000) * (Fintype.card G : ℝ)) := by
  obtain ⟨ring, hcompat⟩ := EndpointFlow.AbelianTransport.exists_compatible_commRing G
  cases hcompat
  let : CommRing G := ring
  exact selector_same_sample_full_error_ring q hq0 hq1 hodd hn C hmargin

/-- The requested external-budget event on the unchanged native sample.
Its explicit error is convenient for joining further events by a union bound. -/
theorem selector_same_sample_external_error
    {G : Type*} [Fintype G] [AddCommGroup G]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (hmargin : selectorExternalBudget (p q) (Fintype.card G) + 3996 ≤
      selectorBudget (p q) (Fintype.card G)) :
    (parameterizedFullMeasure G q hq0 hq1).real
      {ω : FullSample G | ¬ EndpointFlow.AbelianTransport.ColouredSelectors ω
        (selectorExternalBudget (p q) (Fintype.card G))} ≤
      24 * (Fintype.card G : ℝ) ^ 3 *
        Real.exp (-((p q) ^ 8 / 32000) * (Fintype.card G : ℝ)) := by
  apply (selector_same_sample_full_error_abelian q hq0 hq1 hodd hn
    (selectorExternalBudget (p q) (Fintype.card G)) hmargin).trans
  have hn1 : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast (show 1 ≤ Fintype.card G by omega)
  have hn0 : (0 : ℝ) ≤ Fintype.card G := Nat.cast_nonneg _
  have h21 : (Fintype.card G : ℝ) ≤ (Fintype.card G : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hn1)]
  have h32 : (Fintype.card G : ℝ) ^ 2 ≤ (Fintype.card G : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (Fintype.card G : ℝ)) (sub_nonneg.mpr hn1)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  nlinarith

/-- Positive difference between the primitive and external real budgets. -/
def selectorSameSampleSlackGap (q : ℝ) : ℝ :=
  (p q) ^ 4 / 10 ^ 10 - (p q) ^ 4 / 10 ^ 12

/-- An explicit cardinality threshold paying both the primitive theorem
and the exact 3996-point deterministic selector margin. -/
def selectorSameSampleThreshold (q : ℝ) : ℕ :=
  max 2000 ⌈3996 / selectorSameSampleSlackGap q⌉₊

theorem selectorSameSampleSlackGap_pos (q : ℝ) (hq0 : 0 < q) :
    0 < selectorSameSampleSlackGap q := by
  have hp : 0 < p q := by unfold p rho eta; positivity
  have hp4 := pow_pos hp 4
  unfold selectorSameSampleSlackGap
  nlinarith

theorem selectorSameSampleThreshold_pays_slack (q : ℝ) (hq0 : 0 < q)
    (n : ℕ) (hn : selectorSameSampleThreshold q ≤ n) :
    2000 ≤ n ∧ selectorExternalBudget (p q) n + 3996 ≤ selectorBudget (p q) n := by
  have hgap := selectorSameSampleSlackGap_pos q hq0
  have hnceil : ⌈3996 / selectorSameSampleSlackGap q⌉₊ ≤ n :=
    (le_max_right _ _).trans hn
  have hsize : 3996 / selectorSameSampleSlackGap q ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnceil)
  have hgapn : 3996 ≤ selectorSameSampleSlackGap q * n := by
    simpa only [mul_comm] using (div_le_iff₀ hgap).mp hsize
  refine ⟨(le_max_left _ _).trans hn, ?_⟩
  have hsmall : (selectorExternalBudget (p q) n : ℝ) ≤ (p q) ^ 4 * n / 10 ^ 12 := by
    unfold selectorExternalBudget
    exact Nat.floor_le (by positivity)
  unfold selectorBudget
  apply Nat.le_floor
  push_cast
  dsimp [selectorSameSampleSlackGap] at hgapn
  nlinarith

/-- Full native selector availability above a concrete q-dependent size.
No budget-slack condition or compatible-ring choice is a caller premise. -/
theorem selector_same_sample_external_error_of_threshold
    {G : Type*} [Fintype G] [AddCommGroup G]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (hodd : Odd (Fintype.card G)) (hn : selectorSameSampleThreshold q ≤ Fintype.card G) :
    (parameterizedFullMeasure G q hq0 hq1).real
      {ω : FullSample G | ¬ EndpointFlow.AbelianTransport.ColouredSelectors ω
        (selectorExternalBudget (p q) (Fintype.card G))} ≤
      24 * (Fintype.card G : ℝ) ^ 3 *
        Real.exp (-((p q) ^ 8 / 32000) * (Fintype.card G : ℝ)) := by
  obtain ⟨hn2000, hmargin⟩ := selectorSameSampleThreshold_pays_slack q hq0 _ hn
  exact selector_same_sample_external_error q hq0 hq1 hodd hn2000 hmargin

/-- Any strictly smaller exponential coefficient can absorb the polynomial
factor, on the same augmented law and with one group-uniform threshold. -/
theorem selector_same_sample_external_error_at_smaller_rate
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (c : ℝ)
    (hc : c < (p q) ^ 8 / 32000) :
    ∃ N : ℕ, ∀ (G : Type*) [Fintype G] [AddCommGroup G]
      (_hodd : Odd (Fintype.card G)) (_hn : N ≤ Fintype.card G),
      (parameterizedFullMeasure G q hq0 hq1).real
        {ω : FullSample G | ¬ EndpointFlow.AbelianTransport.ColouredSelectors ω
          (selectorExternalBudget (p q) (Fintype.card G))} ≤
        Real.exp (-c * (Fintype.card G : ℝ)) := by
  obtain ⟨N, hN⟩ := polynomial_union_absorbed 24 ((p q) ^ 8 / 32000) c 3 hc
  refine ⟨max N (selectorSameSampleThreshold q), ?_⟩
  intro G _ _ hodd hn
  exact (selector_same_sample_external_error_of_threshold q hq0 hq1 hodd (by omega)).trans
    (hN (Fintype.card G) (by omega))

/-- The existing final exact-matching exponential scale is also available directly
under the augmented law, with no projection to original samples. -/
theorem selector_same_sample_external_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) :
    ∃ N : ℕ, ∀ (G : Type*) [Fintype G] [AddCommGroup G]
      (_hodd : Odd (Fintype.card G)) (_hn : N ≤ Fintype.card G),
      (parameterizedFullMeasure G q hq0 hq1).real
        {ω : FullSample G | ¬ EndpointFlow.AbelianTransport.ColouredSelectors ω
          (selectorExternalBudget (p q) (Fintype.card G))} ≤
        Real.exp (-((xi q) ^ 4 / 10 ^ 6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N, hN⟩ := sampling_rates_pay_polynomial_union q 24 3 hq0 hq1
  refine ⟨max N (selectorSameSampleThreshold q), ?_⟩
  intro G _ _ hodd hn
  exact (selector_same_sample_external_error_of_threshold q hq0 hq1 hodd (by omega)).trans
    (hN (Fintype.card G) (by omega)).2

end

end EndpointFullProduct
