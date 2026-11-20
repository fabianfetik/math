import CorralFormalization.EndpointProof.Flow.AbelianTransport.Theorem

/-!
Retain strict exponential-rate reserve when adjoining further events to
the existing original-law selector, six-root, and paired-cover theorem.

The final statement is reconstructed from the proved primitive P/Q tails,
not inferred from a weaker end-rate bound. It does not construct a universal
absorbing core, a fractional perfect matching, or an exact target matching.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace CorralFormalization.EndpointProof.Probability.ExponentialMargin

open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
open EndpointFullProduct

noncomputable section

/-- A factor of two in the final rate is still strictly below both
existing P/Q primitive rates. The hypothesis on ξ is a numerical bound,
independent of any probability event. -/
theorem doubled_rate_lt_primitive_rates (p τ ξ : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hτ : 0 < τ) (hτp : τ ≤ p)
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ τ^9) :
    2 * ξ^4 / 10^6 < τ^18 / 32000 ∧
      2 * ξ^4 / 10^6 < p^8 / 32000 := by
  have hτ0 := le_of_lt hτ
  have hτ1 := hτp.trans hp1
  have hξ4 : ξ^4 ≤ τ^36 := by
    calc
      ξ^4 ≤ (τ^9)^4 := pow_le_pow_left₀ hξ0 hξ 4
      _ = τ^36 := by rw [← pow_mul]
  have h18 : τ^36 ≤ τ^18 :=
    pow_le_pow_of_le_one hτ0 hτ1 (by norm_num : 18 ≤ 36)
  have h8 : τ^36 ≤ p^8 := by
    calc
      τ^36 ≤ τ^8 := pow_le_pow_of_le_one hτ0 hτ1 (by norm_num : 8 ≤ 36)
      _ ≤ p^8 := pow_le_pow_left₀ hτ0 hτp 8
  have hτ18 : 0 < τ^18 := pow_pos hτ _
  have hp8 : 0 < p^8 := pow_pos hp _
  constructor <;> nlinarith

/-- The actual paper parameters satisfy the strict doubled-rate reserve. -/
theorem sampling_doubled_rate_lt (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    2 * (xi q)^4 / 10^6 < (tau q)^18 / 32000 ∧
      2 * (xi q)^4 / 10^6 < (p q)^8 / 32000 := by
  have hη : 0 < eta := by norm_num [eta]
  have hηq0 : 0 < eta * q := mul_pos hη hq0
  have hηq1 : eta * q ≤ 1 := by norm_num [eta] at *; nlinarith
  have hρ0 : 0 < rho q := by unfold rho; positivity
  have hp0 : 0 < p q := by unfold p; positivity
  have hsq : (eta*q)^2 ≤ 1 := pow_le_one₀ (le_of_lt hηq0) hηq1
  have hp1 : p q ≤ 1 := by unfold p rho; nlinarith
  have hp4 : (p q)^4 ≤ p q := pow_le_of_le_one (le_of_lt hp0) hp1 (by norm_num)
  have hτ0 : 0 < tau q := by unfold tau; positivity
  have hτp : tau q ≤ p q := by unfold tau; nlinarith
  have hr0 : 0 ≤ r0 q := by unfold r0; positivity
  have hr1 : r0 q ≤ 1 := by unfold r0; nlinarith
  have hξ0 : 0 ≤ xi q := by unfold xi kappa; positivity
  have hξ : xi q ≤ (tau q)^9 := by
    have hc : (1 : ℝ) / 10^36 ≤ 1 := by norm_num
    have hτ9 : 0 ≤ (tau q)^9 := pow_nonneg (le_of_lt hτ0) _
    have hfirst : (1 / (10 : ℝ)^36) * (tau q)^9 ≤ (tau q)^9 := by
      simpa using mul_le_mul_of_nonneg_right hc hτ9
    have heq : xi q = (1 / (10 : ℝ)^36) * (tau q)^9 * r0 q := by
      unfold xi kappa
      ring
    rw [heq]
    simpa using mul_le_mul hfirst hr1 hr0 hτ9
  exact doubled_rate_lt_primitive_rates (p q) (tau q) (xi q)
    hp0 hp1 hτ0 hτp hξ0 hξ

/-- A finite collection of polynomial tails pays any rate strictly below
each of its input rates. This exposes the reserve instead of fixing the
conclusion to the older end rate. -/
theorem finite_polynomial_tails_absorbed {T : Type*} [Fintype T]
    (C a : T → ℝ) (k : T → ℕ) (b : ℝ) (hab : ∀ i, b < a i) :
    ∃ N : ℕ, ∀ n ≥ N,
      (∑ i, C i * (n : ℝ)^(k i) * Real.exp (-(a i) * n)) ≤ Real.exp (-b * n) := by
  let B : ℝ := (Fintype.card T : ℝ) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have heach : ∀ i : T, ∃ N : ℕ, ∀ n ≥ N,
      (B * C i) * (n : ℝ)^(k i) * Real.exp (-(a i) * n) ≤ Real.exp (-b * n) := by
    intro i
    exact polynomial_union_absorbed (B*C i) (a i) b (k i) (hab i)
  choose Ni hNi using heach
  let N := Finset.univ.sup Ni
  refine ⟨N, ?_⟩
  intro n hn
  have hi : ∀ i : T,
      C i * (n : ℝ)^(k i) * Real.exp (-(a i) * n) ≤ Real.exp (-b * n) / B := by
    intro i
    have hNiN : Ni i ≤ N := Finset.le_sup (Finset.mem_univ i)
    apply (le_div_iff₀ hB).2
    calc
      (C i * (n : ℝ)^(k i) * Real.exp (-(a i) * n)) * B =
        (B*C i) * (n : ℝ)^(k i) * Real.exp (-(a i) * n) := by ring
      _ ≤ Real.exp (-b * n) := hNi i n (hNiN.trans hn)
  have hnonneg : 0 ≤ Real.exp (-b * n) / B := by positivity
  have hcard : (Fintype.card T : ℝ) ≤ B := by dsimp [B]; linarith
  calc
    (∑ i, C i * (n : ℝ)^(k i) * Real.exp (-(a i) * n)) ≤
        ∑ _ : T, Real.exp (-b * n) / B := Finset.sum_le_sum (fun i _ ↦ hi i)
    _ = (Fintype.card T : ℝ) * (Real.exp (-b * n) / B) := by simp
    _ ≤ B * (Real.exp (-b * n) / B) :=
      mul_le_mul_of_nonneg_right hcard hnonneg
    _ = Real.exp (-b * n) := by field_simp [ne_of_gt hB]

/-- Retain a doubled final rate when combining the true P/Q primitive
tail estimates on one augmentation of the original sample. -/
theorem original_finite_events_probability_with_margin {T : Type*} [Fintype T]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (C : T → ℝ) (k : T → ℕ) (isP : T → Bool) :
    ∃ N : ℕ, ∀ (G : Type*) [Fintype G] [AddCommGroup G]
      (_hn : N ≤ Fintype.card G) (events : T → FullSample G → Prop),
      (∀ i, (parameterizedFullMeasure G q hq0 hq1).real {ω | ¬ events i ω} ≤
        C i * (Fintype.card G : ℝ)^(k i) *
          Real.exp (-(pqTailRate q (isP i)) * (Fintype.card G : ℝ))) →
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ OriginalAdmitsEvents events s} ≤
      Real.exp (-(2 * (xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  have hrates : ∀ i, 2 * (xi q)^4 / 10^6 < pqTailRate q (isP i) := by
    intro i
    obtain ⟨hQ, hP⟩ := sampling_doubled_rate_lt q hq0 hq1
    cases hb : isP i with
    | false => simpa only [pqTailRate, hb, Bool.false_eq_true, ↓reduceIte] using hQ
    | true => simpa only [pqTailRate, hb, ↓reduceIte] using hP
  obtain ⟨N, hN⟩ := finite_polynomial_tails_absorbed C (fun i ↦ pqTailRate q (isP i))
    k (2 * (xi q)^4 / 10^6) hrates
  refine ⟨N, ?_⟩
  intro G _ _ hn events herror
  obtain ⟨hη0,hη1,ha,hb,hab,_,_,_,_⟩ := samplingParameters_admissible q hq0 hq1
  have herror' : ∀ i,
      (fullMeasure q eta (1/4) (tau q / SamplingConstants.rho q)
        (le_of_lt hq0) hq1 hη0 hη1 ha hb hab).real {ω | ¬ events i ω} ≤
        C i * (Fintype.card G : ℝ)^(k i) *
          Real.exp (-(pqTailRate q (isP i)) * (Fintype.card G : ℝ)) := by
    intro i
    simpa only [parameterizedFullMeasure] using herror i
  have hjoint := original_sample_admits_finite_events q eta (1/4)
    (tau q / SamplingConstants.rho q) (le_of_lt hq0) hq1 hη0 hη1 ha hb hab
    events (fun i ↦ C i * (Fintype.card G : ℝ)^(k i) *
      Real.exp (-(pqTailRate q (isP i)) * (Fintype.card G : ℝ))) herror'
  exact hjoint.trans (hN (Fintype.card G) hn)

/-- The genuine existing selector, six-root, and paired-cover outputs,
reconstructed with doubled exponential rate from their proved primitive
tails. No desired core or matching conclusion is assumed as an event. -/
theorem original_selectors_sixRoots_and_covers_probability_with_margin
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [CommRing G] [Fintype G]
      (_hodd : Odd (Fintype.card G)) (_hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ OriginalAdmitsSelectorsSixRootsAndCovers
          (selectorExternalBudget (p q) (Fintype.card G))
          (flowBudget (tau q) (Fintype.card G)) s} ≤
        Real.exp (-(2 * (xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N1, hN1⟩ := original_finite_events_probability_with_margin (T := Fin 5)
    q hq0 hq1 (![6,6,6,6,18] : Fin 5 → ℝ) (![2,1,2,3,6] : Fin 5 → ℕ)
    (![true,true,true,true,false] : Fin 5 → Bool)
  obtain ⟨N2, hN2⟩ := selector_external_budget_slack q hq0
  refine ⟨max N1 N2, ?_⟩
  intro G _ _ hodd hn
  have hn2000 : 2000 ≤ Fintype.card G := (le_max_right _ _).trans hn
  have hnN1 : N1 ≤ Fintype.card G := by omega
  have hmargin : selectorExternalBudget (p q) (Fintype.card G) + 3996 ≤
      selectorBudget (p q) (Fintype.card G) := by
    have h := hN2 (Fintype.card G) (by omega)
    omega
  have hbound := hN1 G hnN1
    (selectorAndAffineFlowEvents hodd (by omega)
      (selectorBudget (p q) (Fintype.card G)) (flowBudget (tau q) (Fintype.card G)))
  have hP0 := EndpointSelector.selector_primitive_full_error q hq0 hq1 hodd hn2000 0
  have hP1 := EndpointSelector.selector_primitive_full_error q hq0 hq1 hodd hn2000 1
  have hP2 := EndpointSelector.selector_primitive_full_error q hq0 hq1 hodd hn2000 2
  have hP3 := EndpointSelector.selector_primitive_full_error q hq0 hq1 hodd hn2000 3
  have hQ := EndpointFlow.affine_flow_full_error q hq0 hq1 hodd hn2000
  have herror : ∀ i : Fin 5,
      (parameterizedFullMeasure G q hq0 hq1).real
        {ω | ¬ selectorAndAffineFlowEvents hodd (by omega)
          (selectorBudget (p q) (Fintype.card G)) (flowBudget (tau q) (Fintype.card G)) i ω} ≤
      (![6,6,6,6,18] : Fin 5 → ℝ) i *
        (Fintype.card G : ℝ)^((![2,1,2,3,6] : Fin 5 → ℕ) i) *
        Real.exp (-(pqTailRate q ((![true,true,true,true,false] : Fin 5 → Bool) i)) *
          (Fintype.card G : ℝ)) := by
    intro i
    fin_cases i
    · simpa [selectorAndAffineFlowEvents, pqTailRate] using hP0
    · simpa [selectorAndAffineFlowEvents, pqTailRate] using hP1
    · simpa [selectorAndAffineFlowEvents, pqTailRate] using hP2
    · simpa [selectorAndAffineFlowEvents, pqTailRate] using hP3
    · simpa [selectorAndAffineFlowEvents, pqTailRate] using hQ
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hbound herror)
  intro s hbad hgood
  obtain ⟨ω, hω, hall⟩ := hgood
  have hP : ∀ i : Fin 4,
      EndpointSelector.selectorPrimitiveEvents hodd (by omega)
        (selectorBudget (p q) (Fintype.card G)) i ω := by
    intro i
    fin_cases i
    · simpa [selectorAndAffineFlowEvents] using hall (0 : Fin 5)
    · simpa [selectorAndAffineFlowEvents] using hall (1 : Fin 5)
    · simpa [selectorAndAffineFlowEvents] using hall (2 : Fin 5)
    · simpa [selectorAndAffineFlowEvents] using hall (3 : Fin 5)
  have hflow : EndpointFlow.affineFlowEvent hodd (by omega)
      (flowBudget (tau q) (Fintype.card G)) ω := by
    simpa [selectorAndAffineFlowEvents] using hall (4 : Fin 5)
  have hselectors := EndpointSelector.Assembly.coloured_selectors_of_primitives
    hodd (by omega) (selectorBudget (p q) (Fintype.card G))
    (selectorExternalBudget (p q) (Fintype.card G)) hmargin ω hP
  have hsupplier := EndpointFlow.Cover.sixRootSupplier_of_affine_event hodd (by omega)
    (flowBudget (tau q) (Fintype.card G)) ω hflow
  exact hbad ⟨ω, hω, hselectors, hsupplier,
    pairedCovers_of_sixRootSupplier hodd ω (flowBudget (tau q) (Fintype.card G)) hsupplier⟩

/-- Same additive group, original categorical sample, common augmentation,
and quantified selector/cover outputs as the existing abelian theorem,
now with an actual strict rate reserve for adjoining further events. -/
theorem original_selectors_sixRoots_and_covers_probability_with_margin_abelian
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [AddCommGroup G] [Fintype G]
      (_hodd : Odd (Fintype.card G)) (_hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ EndpointFlow.AbelianTransport.OriginalAdmitsSelectorsSixRootsAndCovers
          (selectorExternalBudget (p q) (Fintype.card G))
          (flowBudget (tau q) (Fintype.card G)) s} ≤
        Real.exp (-(2 * (xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N, hN⟩ := original_selectors_sixRoots_and_covers_probability_with_margin q hq0 hq1
  refine ⟨N, ?_⟩
  intro G A ft hodd hn
  obtain ⟨ring, hcompat⟩ := EndpointFlow.AbelianTransport.exists_compatible_commRing G
  have hbase := @hN G ring ft hodd hn
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hbase
  intro s hbad hgood
  exact hbad (EndpointFlow.AbelianTransport.additive_selectors_sixRoots_and_covers_of_compatible_ring
    G A ring hcompat _ _ s hgood)

/-- Two events with twice the desired positive coefficient can be united
without losing the desired coefficient, above one numerical threshold.
No independence between the two events is used by this tail inequality. -/
theorem two_doubled_tails_pay_final_rate (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n ≥ N,
      Real.exp (-(2*c) * n) + Real.exp (-(2*c) * n) ≤ Real.exp (-c * n) := by
  obtain ⟨N, hN⟩ := polynomial_union_absorbed 2 (2*c) c 0 (by linarith)
  refine ⟨N, ?_⟩
  intro n hn
  simpa only [pow_zero, mul_one, two_mul] using hN n hn

end

end CorralFormalization.EndpointProof.Probability.ExponentialMargin
